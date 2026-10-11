import DarkTower.WarMachine.IncrementalTaskFrontier
import Mathlib.Tactic

/-!
# A pinned outer-task objective

This is the objective seam *before* any target-local cascade exists.  It is
not cascade-policy `G`: channel meanings, observations, and their aggregation
are caller-declared parameters.  The certificate binds that declaration and
its exact inputs to the stable comparison key stored in the incremental task
frontier.
-/

namespace DarkTower.WarMachine.OuterTaskObjective

open DarkTower.WarMachine.IncrementalTaskFrontier

abbrev Id := IncrementalTaskFrontier.Id

structure ChannelObservation where
  channel : Id
  observation : Id
  evidence : Id
  valueDigest : Id
  deriving DecidableEq

/-- Identity/version and evaluator are declared together.  No weights or
channel semantics are selected by this model. -/
structure Objective where
  identity : Id
  version : Nat
  evaluate : List ChannelObservation → Nat

structure TaskInput where
  task : Id
  channels : List ChannelObservation
  dependencies : Finset Id
  freshnessEpoch : Nat
  deriving DecidableEq

structure EvaluationCertificate where
  input : TaskInput
  objectiveIdentity : Id
  objectiveVersion : Nat
  entry : Entry
  deriving DecidableEq

def EvaluationCertificate.Valid (objective : Objective)
    (c : EvaluationCertificate) : Prop :=
  c.objectiveIdentity = objective.identity ∧
  c.objectiveVersion = objective.version ∧
  c.entry.task = c.input.task ∧
  c.entry.rankingLaw = objective.identity ∧
  c.entry.rankingVersion = objective.version ∧
  c.entry.dependencies = c.input.dependencies ∧
  c.entry.freshnessEpoch = c.input.freshnessEpoch ∧
  c.entry.comparisonKey = objective.evaluate c.input.channels ∧
  c.entry.observation = c.input.channels.foldl
    (fun digest x => digest + x.observation + x.valueDigest) 0 ∧
  c.entry.evidence = c.input.channels.foldl
    (fun digest x => digest + x.evidence) 0

/-- One certificate per current entry, in the same order. -/
structure FrontierCertificate where
  refresh : RefreshCertificate
  evaluations : List EvaluationCertificate
  deriving DecidableEq

def FrontierCertificate.Valid (objective : Objective)
    (c : FrontierCertificate) : Prop :=
  c.refresh.Valid ∧
  c.evaluations.map (·.entry) = c.refresh.current ∧
  allIn c.evaluations (EvaluationCertificate.Valid objective)

def objectiveLE (a b : EvaluationCertificate) : Prop :=
  a.entry.comparisonKey < b.entry.comparisonKey ∨
    (a.entry.comparisonKey = b.entry.comparisonKey ∧ a.entry.task ≤ b.entry.task)

instance (a b : EvaluationCertificate) : Decidable (objectiveLE a b) := by
  unfold objectiveLE
  infer_instance

structure SelectionCertificate where
  selected : EvaluationCertificate
  deriving DecidableEq

def SelectionCertificate.Valid (objective : Objective)
    (frontier : FrontierCertificate) (s : SelectionCertificate) : Prop :=
  frontier.Valid objective ∧
  s.selected ∈ frontier.evaluations ∧
  allIn frontier.evaluations (objectiveLE s.selected)

/-- A valid selection is the deterministic minimum under declared objective
value, with stable task identity as the tie law. -/
theorem selected_is_minimum (objective : Objective) (frontier : FrontierCertificate)
    (selection : SelectionCertificate) (h : selection.Valid objective frontier)
    (candidate : EvaluationCertificate) (hc : candidate ∈ frontier.evaluations) :
    objectiveLE selection.selected candidate := by
  exact h.2.2 candidate hc

theorem selected_belongs_to_fully_refreshed_frontier
    (objective : Objective) (frontier : FrontierCertificate)
    (selection : SelectionCertificate) (h : selection.Valid objective frontier) :
    selection.selected.entry ∈ frontier.refresh.current := by
  rw [← h.1.2.1]
  exact List.mem_map.mpr ⟨selection.selected, h.2.1, rfl⟩

/-- Retention needs no global reindexing: when the dependency closure is
unchanged, strict refresh preserves the entire prior entry, including its
objective identity/version and comparison key. -/
theorem retained_objective_entry_is_identical
    (objective : Objective) (frontier : FrontierCertificate) (entry : Entry)
    (h : frontier.Valid objective) (he : entry ∈ frontier.refresh.retained) :
    entry ∈ frontier.refresh.prior ∧ entry ∈ frontier.refresh.current ∧
      entry.rankingLaw = entry.rankingLaw ∧
      entry.rankingVersion = entry.rankingVersion ∧
      entry.comparisonKey = entry.comparisonKey := by
  have hp := unchanged_disjoint_entry_retained_identically
    frontier.refresh entry h.1 he
  exact ⟨hp.1, hp.2, rfl, rfl, rfl⟩

/-- An affected entry cannot survive as retained evidence under any objective. -/
theorem affected_objective_entry_must_be_recomputed
    (objective : Objective) (frontier : FrontierCertificate) (entry : Entry)
    (h : frontier.Valid objective) (he : entry ∈ frontier.refresh.invalidated) :
    entry.task ∈ taskSet frontier.refresh.recomputed :=
  invalidated_task_cannot_be_omitted frontier.refresh entry h.1 he

/-- Substituting an objective identity invalidates an evaluation even if the
numeric score happens to remain equal. -/
theorem objective_substitution_invalid
    (objective : Objective) (c : EvaluationCertificate)
    (h : c.objectiveIdentity ≠ objective.identity) :
    ¬ c.Valid objective := by
  intro hv
  exact h hv.1

/-! Closed witnesses: declared channel semantics remain arbitrary. -/

def witnessObjective : Objective where
  identity := 70
  version := 2
  evaluate := fun xs => xs.foldl (fun n x => n + x.valueDigest) 0

def witnessInput (task value : Nat) : TaskInput where
  task := task
  channels := [⟨1, task + 10, task + 20, value⟩]
  dependencies := {task + 10}
  freshnessEpoch := 4

def witnessEvaluation (task value : Nat) : EvaluationCertificate where
  input := witnessInput task value
  objectiveIdentity := 70
  objectiveVersion := 2
  entry := ⟨task, task + 10 + value, task + 20, 70, 2, {task + 10}, value, 4⟩

theorem witnessEvaluation_valid (task value : Nat) :
    (witnessEvaluation task value).Valid witnessObjective := by
  simp [EvaluationCertificate.Valid, witnessEvaluation, witnessInput, witnessObjective]

theorem tie_breaks_by_stable_task_identity :
    objectiveLE (witnessEvaluation 1 5) (witnessEvaluation 2 5) := by
  simp [objectiveLE, witnessEvaluation]

def substitutedWitness : EvaluationCertificate :=
  { witnessEvaluation 1 5 with objectiveIdentity := 71 }

theorem substitutedWitness_invalid :
    ¬ substitutedWitness.Valid witnessObjective := by
  exact objective_substitution_invalid witnessObjective substitutedWitness (by decide)

end DarkTower.WarMachine.OuterTaskObjective
