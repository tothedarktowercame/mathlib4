import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sublists

/-!
# R11 hierarchical shared-budget arbitration

This module states the record-level role implemented by
`futon2/src/futon2/aif/hierarchical_budget.clj/arbitrate`, including its
`leaf-frontier`, `branch-frontier`, `combine-options`, and `usage-by-node`
helpers, and replayed by
`futon2/src/futon2/aif/hierarchical_budget_adapter.clj/replay`, read at Futon2
commit `0f9587532031beb50a21091cc41cd10f4a16ff63`.

Costs, utilities and budgets are natural numbers here. The runtime uses finite
doubles and tolerance `1.0e-9`; this exact model deliberately has no epsilon.
The module states feasibility and finite-field optimality of a retained
portfolio. It does not prove that the Clojure Pareto-frontier algorithm computes
that portfolio, validate runtime schemas or numeric finiteness, enforce leaf
`:selection-limit`, or establish source/replay identity. The runtime's stable
minimum-cost then lexical-proposal-id tie-break among equal-utility portfolios
is also left out: it chooses one maximizer but does not change feasibility or
maximum utility.
-/

namespace DarkTower.WarMachine.R11HierarchicalBudget

/-- A hierarchy node. `nodeId` stands for runtime node `:id`; `budget` stands
for its normalized non-negative `:budget`. -/
structure BudgetNode where
  nodeId : Nat
  budget : Nat
  deriving DecidableEq, Repr

/-- A proposal in the finite field. The fields stand for runtime proposal
`:id`, `:cost`, `:utility`, and the complete ancestor list retained as
`:budget/path`. -/
structure Proposal where
  proposalId : Nat
  cost : Nat
  utility : Nat
  budgetPath : List Nat
  deriving DecidableEq, Repr

/-- The retained arbitration carrier. `rootId` stands for adapter `:root-id`;
`nodes` for the flattened hierarchy's `:node-budgets`; `proposals` for the
complete normalized proposal field; and `selectedIds` for output
`:selected-ids`. -/
structure ArbitrationRecord where
  rootId : Nat
  nodes : List BudgetNode
  proposals : List Proposal
  selectedIds : List Nat
  deriving DecidableEq, Repr

def selectedProposals (record : ArbitrationRecord) : List Proposal :=
  record.proposals.filter fun proposal => proposal.proposalId ∈ record.selectedIds

/-- Runtime `usage-by-node`: a selected proposal's cost is charged to every
node named in its `:budget/path`. -/
def usageAt (record : ArbitrationRecord) (nodeId : Nat) : Nat :=
  (selectedProposals record).foldl
    (fun used proposal => if nodeId ∈ proposal.budgetPath then used + proposal.cost else used)
    0

def totalUtility (record : ArbitrationRecord) : Nat :=
  (selectedProposals record).foldl (fun total proposal => total + proposal.utility) 0

def withSelection (record : ArbitrationRecord) (ids : List Nat) : ArbitrationRecord :=
  { record with selectedIds := ids }

/-- Every selected identity is from the supplied finite proposal field, no
identity is selected twice, hierarchy and proposal identities are unique, the
declared root exists, and usage at every hierarchy node is within its budget. -/
def Feasible (record : ArbitrationRecord) : Prop :=
  (record.nodes.map BudgetNode.nodeId).Nodup ∧
  (record.proposals.map Proposal.proposalId).Nodup ∧
  record.selectedIds.Nodup ∧
  record.rootId ∈ record.nodes.map BudgetNode.nodeId ∧
  record.selectedIds.Forall
    (fun id => id ∈ record.proposals.map Proposal.proposalId) ∧
  record.nodes.Forall
    (fun node => usageAt record node.nodeId ≤ node.budget)

/-- Executable feasibility checker over the retained finite carrier. -/
def checkFeasible (record : ArbitrationRecord) : Bool :=
  decide (record.nodes.map BudgetNode.nodeId).Nodup &&
  decide (record.proposals.map Proposal.proposalId).Nodup &&
  decide record.selectedIds.Nodup &&
  decide (record.rootId ∈ record.nodes.map BudgetNode.nodeId) &&
  record.selectedIds.all (fun id => decide (id ∈ record.proposals.map Proposal.proposalId)) &&
  record.nodes.all (fun node => decide (usageAt record node.nodeId ≤ node.budget))

theorem checkFeasible_eq_true_iff (record : ArbitrationRecord) :
    checkFeasible record = true ↔ Feasible record := by
  simp [checkFeasible, Feasible, and_assoc, List.forall_iff_forall_mem]

instance feasibleDecidable (record : ArbitrationRecord) : Decidable (Feasible record) :=
  decidable_of_iff (checkFeasible record = true) (checkFeasible_eq_true_iff record)

theorem checkFeasible_eq_false_iff (record : ArbitrationRecord) :
    checkFeasible record = false ↔ ¬ Feasible record := by
  rw [← Bool.not_eq_true, checkFeasible_eq_true_iff]

/-- All alternative portfolios are drawn from the same finite proposal field. -/
def candidatePortfolios (record : ArbitrationRecord) : List (List Nat) :=
  (record.proposals.map Proposal.proposalId).sublists

/-- R11 optimality: no feasible portfolio over this proposal field has greater
utility than the retained selected portfolio. -/
def Optimal (record : ArbitrationRecord) : Prop :=
  Feasible record ∧
  (candidatePortfolios record).Forall (fun ids =>
    Feasible (withSelection record ids) →
      totalUtility (withSelection record ids) ≤ totalUtility record)

def checkOptimal (record : ArbitrationRecord) : Bool :=
  checkFeasible record &&
  (candidatePortfolios record).all (fun ids =>
    !checkFeasible (withSelection record ids) ||
      decide (totalUtility (withSelection record ids) ≤ totalUtility record))

theorem checkOptimal_eq_true_iff (record : ArbitrationRecord) :
    checkOptimal record = true ↔ Optimal record := by
  simp [checkOptimal, Optimal, List.forall_iff_forall_mem, checkFeasible_eq_true_iff,
    checkFeasible_eq_false_iff]
  intro _
  constructor
  · intro checked ids retained selected
    rcases checked ids retained with rejected | bounded
    · exact False.elim (rejected selected)
    · exact bounded
  · intro bounded ids retained
    by_cases selected : Feasible (withSelection record ids)
    · exact Or.inr (bounded ids retained selected)
    · exact Or.inl selected

/-- Hierarchical consequence: feasibility bounds root usage as well as leaf
usage; satisfying children alone is not enough. -/
theorem feasible_root_usage_within_budget (record : ArbitrationRecord)
    (feasible : Feasible record) (root : BudgetNode)
    (rootRetained : root ∈ record.nodes) (rootIdentity : root.nodeId = record.rootId) :
    usageAt record record.rootId ≤ root.budget := by
  have within := feasible.2.2.2.2.2
  rw [List.forall_iff_forall_mem] at within
  simpa [rootIdentity] using within root rootRetained

def root : BudgetNode := { nodeId := 0, budget := 8 }
def leafA : BudgetNode := { nodeId := 1, budget := 6 }
def leafB : BudgetNode := { nodeId := 2, budget := 6 }

def proposalA : Proposal :=
  { proposalId := 10, cost := 6, utility := 10, budgetPath := [0, 1] }
def proposalB : Proposal :=
  { proposalId := 20, cost := 6, utility := 9, budgetPath := [0, 2] }
def proposalC : Proposal :=
  { proposalId := 30, cost := 2, utility := 8, budgetPath := [0, 2] }

/-- Positive two-level witness: A and C use exactly the shared root budget. -/
def positiveRecord : ArbitrationRecord :=
  { rootId := 0
    nodes := [root, leafA, leafB]
    proposals := [proposalA, proposalB, proposalC]
    selectedIds := [10, 30] }

theorem positiveRecord_is_feasible : Feasible positiveRecord :=
  (checkFeasible_eq_true_iff positiveRecord).mp (by decide)

theorem positiveRecord_is_optimal : Optimal positiveRecord := by
  rw [← checkOptimal_eq_true_iff]
  native_decide

/-- Control A: both leaves respect budget 6, but their combined cost 12 exceeds
the shared parent budget 8. -/
def parentOverBudgetRecord : ArbitrationRecord :=
  { positiveRecord with selectedIds := [10, 20] }

def LeafFeasible (record : ArbitrationRecord) : Prop :=
  record.nodes.Forall (fun node => node.nodeId ≠ record.rootId →
    usageAt record node.nodeId ≤ node.budget)

theorem parentOverBudget_leaves_are_feasible : LeafFeasible parentOverBudgetRecord := by
  simp [LeafFeasible, List.forall_iff_forall_mem, parentOverBudgetRecord,
    positiveRecord, root, leafA, leafB, usageAt, selectedProposals, proposalA, proposalB,
    proposalC]

theorem parentOverBudget_is_rejected : ¬ Feasible parentOverBudgetRecord := by
  rw [← checkFeasible_eq_true_iff]
  decide

/-- Control B: selecting C alone is feasible but not optimal; the witnessed
alternative A+C has utility 18 rather than 8. -/
def nonoptimalRecord : ArbitrationRecord :=
  { positiveRecord with selectedIds := [30] }

theorem nonoptimalRecord_is_feasible : Feasible nonoptimalRecord :=
  (checkFeasible_eq_true_iff nonoptimalRecord).mp (by decide)

theorem betterPortfolio_is_feasible :
    Feasible (withSelection nonoptimalRecord [10, 30]) :=
  (checkFeasible_eq_true_iff _).mp (by decide)

theorem betterPortfolio_has_greater_utility :
    totalUtility nonoptimalRecord < totalUtility (withSelection nonoptimalRecord [10, 30]) := by
  decide

theorem nonoptimalRecord_is_rejected : ¬ Optimal nonoptimalRecord := by
  rw [← checkOptimal_eq_true_iff]
  native_decide

end DarkTower.WarMachine.R11HierarchicalBudget
