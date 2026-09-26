import DarkTower.WarMachine.CascadeOrder
import DarkTower.WarMachine.CascadeTransition

/-!
# The containment order built from the interpreted patterns (C1, registry `:containment-order`)

WM-LEAN-ABSENT-TRIAGE-D (`futon2 57849fb9`) row 17 and entry C1. `CascadeOrder`
states the order VOCABULARY — `Reach`, `Below`, `IsMeet`, `acyclicDescent` — over
an arbitrary relation `r`, and `acyclicDescent` was what the registry row's
`:lean` named. But the row's `:formal` does not describe a condition on an
arbitrary `r`; it CONSTRUCTS one from the patterns: "Unit A is above unit B iff A
produces a token B's guard needs". No declaration did that, which is why the
edge R2→R6 (`interp`) had no import behind it. `containmentOrder` is that
construction.

It is the same object `futon2:src/futon2/aif/construction.clj:113-230`
(`containment-order`) builds: its `descent` is the pairs `[a b]` with `a ≠ b`
whose `(:produces a)` meets `(get-in b [:guard :needs])`, and in
`CascadeTransition.InterpretedPattern` the guard's needs are `consumes`
(`guard p s` requires `p.consumes ⊆ s`). The `a ≠ b` is the code's own
`:when (not= a b)`, kept here so the two name one relation
(`containmentOrder_irreflexive`).

## The condition the row does not state, which is this module's finding

The triage asks for `acyclicDescent` "under the row's stated conditions". THE ROW
STATES NONE THAT IMPLY IT. It says only what happens when acyclicity fails —
"A cyclic containment REFUSES with `:cyclic-containment`" — and `acyclicDescent`
in its `:latex` is the definition of that condition, not a sufficient condition on
the patterns. It cannot state one by accident either: `twoPatternCycleIsNotAcyclic`
below builds a genuine two-pattern cycle out of nothing but `produces` and
`consumes`, so the construction is cyclic for some libraries and the row's own
refusal is the only thing standing between the machine and a cascade with no order.

The smallest hypothesis that does give the theorem, stated on the PATTERNS rather
than on the derived relation, is a token `Stratification`: a level on tokens that
every pattern strictly raises from everything it consumes to everything it
produces. That is a property a pattern LIBRARY can be checked for once, which is
the useful place for it, rather than a property of each cascade discovered after
assembly. `acyclicDescent_of_stratification` is the theorem;
`noStratificationForTheCycle` shows the hypothesis is not vacuous by exhibiting
patterns that have none.

Ranking by the derived relation instead (`CascadeOrder.acyclic_of_increasing_rank`
with a rank on units) would also discharge it, and would say nothing: for a finite
unit set such a rank exists exactly when the order is acyclic, so it restates the
conclusion.

## What this module does not claim

It does not state the restricted-meet condition: that is
`Proof2.CoApplicationKernel.hasRestrictedMeets`, already written, and the row's
`:lean-note` names it. It says nothing about `:missing-meets`, about the
precedence-violation record `construction.clj` also returns, or about units —
`ι` here indexes UNIT APPLICATIONS already, so the row's "one node per
application, the pattern id as an attribute" is an assumption on the caller's
indexing, not something proved here.
-/

namespace DarkTower.WarMachine.Proof2.ContainmentOrder

open DarkTower.WarMachine.CascadeTransition

variable {ι V : Type*} [Fintype V] [DecidableEq V]

/-- **The containment order.** Unit `a` is above unit `b` exactly when `a`
produces a token `b`'s guard needs, and `a` is not `b`. -/
def containmentOrder (pat : ι → InterpretedPattern V) (a b : ι) : Prop :=
  a ≠ b ∧ ((pat a).produces ∩ (pat b).consumes).Nonempty

/-- The code's `:when (not= a b)`: a pattern that produces a token its own guard
needs contributes no edge. -/
theorem containmentOrder_irreflexive (pat : ι → InterpretedPattern V) (a : ι) :
    ¬ containmentOrder pat a a := fun h => h.1 rfl

/-- The witnessing token of an edge: it is produced by `a` and consumed by `b`. -/
theorem containmentOrder_token (pat : ι → InterpretedPattern V) {a b : ι}
    (h : containmentOrder pat a b) :
    ∃ t, t ∈ (pat a).produces ∧ t ∈ (pat b).consumes := by
  obtain ⟨t, ht⟩ := h.2
  exact ⟨t, (Finset.mem_inter.mp ht).1, (Finset.mem_inter.mp ht).2⟩

/-- **A token stratification of a pattern library.** `level` ranks tokens, and
every pattern strictly raises it from each token it consumes to each token it
produces. `pos` keeps the levels above the bottom so that a pattern consuming
nothing still sits strictly below what it feeds; any stratification can be
shifted by one to satisfy it. -/
structure Stratification (pat : ι → InterpretedPattern V) where
  level : V → ℕ
  pos : ∀ v, 0 < level v
  raises : ∀ i, ∀ c ∈ (pat i).consumes, ∀ p ∈ (pat i).produces, level c < level p

/-- A unit's rank: the highest level it consumes (zero when it consumes
nothing). -/
def rank (pat : ι → InterpretedPattern V) (s : Stratification pat) (i : ι) : ℕ :=
  (pat i).consumes.sup s.level

/-- Every edge of the containment order strictly raises the rank. -/
theorem rank_lt_of_edge (pat : ι → InterpretedPattern V) (s : Stratification pat)
    {a b : ι} (h : containmentOrder pat a b) : rank pat s a < rank pat s b := by
  obtain ⟨t, hta, htb⟩ := containmentOrder_token pat h
  have hbelow : rank pat s a < s.level t := by
    refine (Finset.sup_lt_iff (s.pos t)).mpr ?_
    intro c hc
    exact s.raises a c hc t hta
  exact lt_of_lt_of_le hbelow (Finset.le_sup htb)

/-- **The theorem.** A stratified pattern library has an acyclic containment
order, whatever cascade is assembled from it — so the row's
`:cyclic-containment` refusal is unreachable exactly there. -/
theorem acyclicDescent_of_stratification (pat : ι → InterpretedPattern V)
    (s : Stratification pat) : acyclicDescent (containmentOrder pat) :=
  acyclic_of_increasing_rank _ (rank pat s) fun _ _ h => rank_lt_of_edge pat s h

/-! ## The bad case: two patterns that feed each other

`A` consumes token 0 and produces token 1; `B` consumes token 1 and produces
token 0. Nothing about them is malformed — both are honest `InterpretedPattern`s
— and their containment order has a two-cycle. This is the refusal
`construction.clj` raises as `:cyclic-containment`, and it is why the hypothesis
above cannot be dropped. -/

section Cycle

/-- The pattern that turns token 0 into token 1. -/
def upPattern : InterpretedPattern (Fin 2) where
  consumes := {0}
  produces := {1}
  forbids := ∅
  theta := 1
  theta_nonneg := by norm_num
  theta_le_one := by norm_num

/-- The pattern that turns token 1 back into token 0. -/
def downPattern : InterpretedPattern (Fin 2) where
  consumes := {1}
  produces := {0}
  forbids := ∅
  theta := 1
  theta_nonneg := by norm_num
  theta_le_one := by norm_num

/-- Two units, one applying each pattern. -/
def cyclePat : Bool → InterpretedPattern (Fin 2)
  | true => upPattern
  | false => downPattern

theorem cycle_edge_up : containmentOrder cyclePat true false :=
  ⟨by simp, ⟨1, by decide⟩⟩

theorem cycle_edge_down : containmentOrder cyclePat false true :=
  ⟨by simp, ⟨0, by decide⟩⟩

/-- **The two-pattern cycle is not acyclic**, so `acyclicDescent` is a real
condition on this construction and not a theorem about it. -/
theorem twoPatternCycleIsNotAcyclic : ¬ acyclicDescent (containmentOrder cyclePat) := by
  intro hacyc
  exact hacyc true (Reach.tail (Reach.single cycle_edge_up) cycle_edge_down)

/-- **And the hypothesis is not vacuous**: those two patterns admit no
stratification. Any level would have to satisfy `level 0 < level 1` (from the
up-pattern) and `level 1 < level 0` (from the down-pattern). -/
theorem noStratificationForTheCycle : IsEmpty (Stratification cyclePat) := by
  constructor
  intro s
  have h01 : s.level 0 < s.level 1 :=
    s.raises true 0 (by decide) 1 (by decide)
  have h10 : s.level 1 < s.level 0 :=
    s.raises false 1 (by decide) 0 (by decide)
  exact absurd (h01.trans h10) (lt_irrefl _)

end Cycle

/-! ## The accepting case

One pattern feeding another, the shape `CascadeOrder`'s
`attempt008_2026_07_16_descent_is_accepted` records from
`attempt-008/003-construction.edn`. Here it is built from patterns rather than
declared as a relation. -/

section Chain

/-- The pattern that consumes token 1 and produces token 2. -/
def midPattern : InterpretedPattern (Fin 3) where
  consumes := {1}
  produces := {2}
  forbids := ∅
  theta := 1
  theta_nonneg := by norm_num
  theta_le_one := by norm_num

/-- The pattern that consumes token 0 and produces token 1. -/
def lowPattern : InterpretedPattern (Fin 3) where
  consumes := {0}
  produces := {1}
  forbids := ∅
  theta := 1
  theta_nonneg := by norm_num
  theta_le_one := by norm_num

def chainPat : Bool → InterpretedPattern (Fin 3)
  | true => lowPattern
  | false => midPattern

/-- Token level = token index + 1, which every pattern here strictly raises. -/
def chainStratification : Stratification chainPat where
  level := fun v => v.val + 1
  pos := fun _ => Nat.succ_pos _
  raises := by decide

/-- The chain is accepted, and by the theorem rather than by inspection. -/
theorem chainIsAcyclic : acyclicDescent (containmentOrder chainPat) :=
  acyclicDescent_of_stratification chainPat chainStratification

/-- Its one edge is the one the code would derive: the low pattern feeds the
middle one, and not the other way. -/
theorem chainHasOneDirection :
    containmentOrder chainPat true false ∧ ¬ containmentOrder chainPat false true := by
  refine ⟨⟨by simp, ⟨1, by decide⟩⟩, ?_⟩
  rintro ⟨-, hne⟩
  have hempty : (chainPat false).produces ∩ (chainPat true).consumes = ∅ := by decide
  exact hne.ne_empty hempty

end Chain

#print axioms containmentOrder
#print axioms containmentOrder_irreflexive
#print axioms containmentOrder_token
#print axioms Stratification
#print axioms rank
#print axioms rank_lt_of_edge
#print axioms acyclicDescent_of_stratification
#print axioms cycle_edge_up
#print axioms cycle_edge_down
#print axioms twoPatternCycleIsNotAcyclic
#print axioms noStratificationForTheCycle
#print axioms chainStratification
#print axioms chainIsAcyclic
#print axioms chainHasOneDirection

end DarkTower.WarMachine.Proof2.ContainmentOrder
