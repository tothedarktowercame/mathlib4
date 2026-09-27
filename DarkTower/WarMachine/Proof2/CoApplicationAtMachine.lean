import DarkTower.WarMachine.Proof2.ContainmentOrder
import DarkTower.WarMachine.Proof2.CoApplicationKernel

/-!
# The co-application kernel at the machine's containment order (W9-1, registry
`:co-application-kernel`)

W9-D (`futon2 holes/labs/wm-contract/proof2/packets/W9-D.md`, PROOF-2a ⟨2⟩1d):
`CoApplicationKernel.coApplyKernel` binds its descent order `r` FREE, and no
module applied it at `containmentOrder pat` — the R6→R4 `:r` edge was blue at
node grain only (`:via [PolicyPosteriorAtMachine]`) while the term's own
module was unreached by any R4 module. `machineCoApplyKernel` is that
application: the kernel at C1's containment order, the relation
`futon2:src/futon2/aif/construction.clj` (`containment-order`) builds from the
published interpretations. No existing declaration changes statement.

## The refusal mirror of `order-use`

`futon2:src/futon2/aif/efe.clj` (`order-use`) reads the order off the action's
construction receipt and never defaults a missing or refused order into the
co-application kernel: no order on the receipt, a refused order
(`:cyclic-containment`), or precedence violations all fall back to the list
kernel with the reason recorded in `:meta`. `machineCoApplication` is the
typed mirror: the co-application step is ABSENT (an `Except.error` carrying
`¬ acyclicDescent (containmentOrder pat)`) when the order is cyclic, never
silently the list kernel. The other two `order-use` fallback arms are
receipt-level inputs this module does not model; they appear as the remaining
`CoApplicationAbsence` constructors so the absence TYPE names all three arms.

The acyclicity hypothesis for the ok arm is C1's `Stratification` (the row
states none; the machine's refusal is what the code does), and
`twoPatternCycleIsNotAcyclic` makes the cyclic arm reachable.
-/

namespace DarkTower.WarMachine.Proof2.CoApplicationAtMachine

open scoped BigOperators
open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.Proof2.ContainmentOrder
open DarkTower.WarMachine.Proof2.CoApplicationKernel

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- **The machine's co-application kernel**: the co-application kernel at the
containment order built from the same patterns. This is the registry row
`:co-application-kernel`'s new `:lean` target. -/
noncomputable def machineCoApplyKernel (pat : ι → InterpretedPattern V)
    (s s' : Finset V) : ℝ :=
  coApplyKernel pat (containmentOrder pat) s s'

/-- The machine kernel IS `coApplyKernel` at `containmentOrder pat`. -/
theorem machineCoApplyKernel_eq (pat : ι → InterpretedPattern V) (s s' : Finset V) :
    machineCoApplyKernel pat s s' = coApplyKernel pat (containmentOrder pat) s s' := rfl

/-- Row sums at the machine's order, by composition with
`coApplyKernel_rowsum`. -/
theorem machineCoApplyKernel_rowsum (pat : ι → InterpretedPattern V) (s : Finset V) :
    ∑ s' : Finset V, machineCoApplyKernel pat s s' = 1 :=
  coApplyKernel_rowsum pat (containmentOrder pat) s

/-- Nonnegativity at the machine's order, by composition with
`coApplyKernel_nonneg`. -/
theorem machineCoApplyKernel_nonneg (pat : ι → InterpretedPattern V) (s s' : Finset V) :
    0 ≤ machineCoApplyKernel pat s s' :=
  coApplyKernel_nonneg pat (containmentOrder pat) s s'

/-- The chain case: when the containment order relates to a precedence list by
`chainCondition`, the machine kernel is the list kernel — the code's
`{:order :chain}` arm, where the two kernels coincide. -/
theorem machineCoApplyKernel_eq_cascadeKernel_of_chain
    (pat : ι → InterpretedPattern V) {precedence : List (InterpretedPattern V)}
    (h : chainCondition pat (containmentOrder pat) precedence) (s s' : Finset V) :
    machineCoApplyKernel pat s s' = cascadeKernel precedence s s' :=
  coApplyKernel_eq_cascadeKernel_of_chain h s s'

/-- The conflict flag at the machine's order: `frontierConflict` at
`containmentOrder pat`, unchanged — co-application carries the flag on the
certificate, it does not refuse. -/
noncomputable def machineFrontierConflict (pat : ι → InterpretedPattern V)
    (s : Finset V) : Prop :=
  frontierConflict pat (containmentOrder pat) s

omit [DecidableEq ι] in
/-- The flag is definitionally the kernel's flag at the containment order. -/
theorem machineFrontierConflict_eq (pat : ι → InterpretedPattern V) (s : Finset V) :
    machineFrontierConflict pat s ↔ frontierConflict pat (containmentOrder pat) s :=
  Iff.rfl

/-- **Why the co-application step is not used**: `order-use`'s list-kernel
fallback arms, typed. The code then scores the list kernel with the reason in
`:meta`; the reason is never dropped and no kernel is defaulted in. -/
inductive CoApplicationAbsence (pat : ι → InterpretedPattern V) where
  /-- The receipt carried no order (`:no-order-on-receipt`). -/
  | noOrder : CoApplicationAbsence pat
  /-- The order was refused as cyclic (`:cyclic-containment`); the absence
  carries the cyclicity. -/
  | cyclic : ¬ acyclicDescent (containmentOrder pat) → CoApplicationAbsence pat
  /-- The receipt recorded precedence violations (`:precedence-violations n`). -/
  | precedenceViolations : ℕ → CoApplicationAbsence pat

open Classical in
/-- **The machine's co-application step**: the kernel at the containment order
when that order is acyclic; the typed `cyclic` absence when it is not — the
co-application step is refused, never silently the list kernel. -/
noncomputable def machineCoApplication (pat : ι → InterpretedPattern V)
    (s s' : Finset V) : Except (CoApplicationAbsence pat) ℝ :=
  if h : acyclicDescent (containmentOrder pat)
    then .ok (machineCoApplyKernel pat s s')
    else .error (.cyclic h)

/-- A stratified pattern library always takes the ok arm: the
`:cyclic-containment` refusal is unreachable exactly there (C1's theorem). -/
theorem machineCoApplication_of_stratification (pat : ι → InterpretedPattern V)
    (st : Stratification pat) (s s' : Finset V) :
    machineCoApplication pat s s' = .ok (machineCoApplyKernel pat s s') := by
  unfold machineCoApplication
  rw [dif_pos (acyclicDescent_of_stratification pat st)]

/-- The cyclic arm is reachable: C1's two-pattern cycle is refused, and the
absence carries its cyclicity. -/
theorem machineCoApplication_cycle (s s' : Finset (Fin 2)) :
    machineCoApplication cyclePat s s' = .error (.cyclic twoPatternCycleIsNotAcyclic) := by
  unfold machineCoApplication
  rw [dif_neg twoPatternCycleIsNotAcyclic]

/-! ## The bad case: a different order gives a different kernel

`CoApplicationKernel.ConflictFixture`: `p` produces `a` and forbids `b`; `q`
produces `b` and forbids `a`; both consume nothing. Their containment order
has NO edges (nothing consumes anything), so the machine kernel co-applies the
whole frontier and reaches `{a, b}` in one step with probability `θ_p · θ_q`.
At the order that puts `p` above `q`, `p` is off the frontier and `{a, b}` is
unreachable in one step. The order is an input, not a detail. -/

section BadCase

open ConflictFixture (Tok Idx)

/-- The fixture patterns at PROOF-2a's θ = 4/5. -/
noncomputable abbrev fixturePat : Idx → InterpretedPattern Tok :=
  ConflictFixture.pat (4 / 5) (4 / 5)
    ConflictFixture.h80_nonneg ConflictFixture.h80_le_one
    ConflictFixture.h80_nonneg ConflictFixture.h80_le_one

/-- Nothing consumes anything in the fixture, so its containment order has no
edges. -/
theorem fixture_no_containment_edges : ∀ a b : Idx, ¬ containmentOrder fixturePat a b := by
  intro a b
  cases a <;> cases b <;> simp [containmentOrder, fixturePat, ConflictFixture.pat]

/-- The machine kernel at the fixture is the kernel at the empty order. -/
theorem machineKernel_fixture :
    machineCoApplyKernel fixturePat =
      coApplyKernel fixturePat ConflictFixture.r := by
  have hr : containmentOrder fixturePat = ConflictFixture.r := by
    funext a b
    exact propext ⟨fun h => (fixture_no_containment_edges a b h).elim, fun h => h.elim⟩
  unfold machineCoApplyKernel
  rw [hr]

/-- Co-application at the machine's order reaches `{a, b}` from `∅` in one
step with probability `(4/5)²`. -/
theorem machineKernel_fixture_both :
    machineCoApplyKernel fixturePat ∅ {Tok.a, Tok.b} = (4 / 5 : ℝ) * (4 / 5) := by
  rw [machineKernel_fixture]
  exact ConflictFixture.coApply_both _ _ _ _ _ _

/-- A different descent order on the same patterns: `p` above `q`. -/
def pAboveQ : Idx → Idx → Prop := fun a b => a = .p ∧ b = .q

/-- Reach under `pAboveQ` is the single edge. -/
theorem reach_pAboveQ {x y : Idx} (h : Reach pAboveQ x y) : x = .p ∧ y = .q := by
  induction h with
  | single e => exact e
  | tail _ e ih => exact ⟨ih.1, e.2⟩

/-- Under `pAboveQ` the frontier at `∅` is `{q}` alone: `p` has an enabled
pattern below it in the reach order, `q` has none. -/
theorem frontier_pAboveQ : enabledFrontier fixturePat pAboveQ ∅ = {Idx.q} := by
  ext x
  simp only [enabledFrontier, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨-, htop⟩
    cases x with
    | p =>
        exact False.elim (htop Idx.q
          (by simp [CascadeTransition.guard, fixturePat, ConflictFixture.pat])
          (Reach.single ⟨rfl, rfl⟩))
    | q => rfl
  · intro hx
    subst hx
    refine ⟨by simp [CascadeTransition.guard, fixturePat, ConflictFixture.pat], ?_⟩
    intro q' _ hreach
    exact Idx.noConfusion (reach_pAboveQ hreach).1

/-- **The bad case.** At the machine's order `{a, b}` is reached in one step;
at the `p`-above-`q` order the singleton frontier `{q}` gives the pattern
kernel of `q`, which never reaches `{a, b}` in one step. Same patterns, same
state, different order, different kernel. -/
theorem machineKernel_differs_at_other_order :
    machineCoApplyKernel fixturePat ∅ {Tok.a, Tok.b} ≠
      coApplyKernel fixturePat pAboveQ ∅ {Tok.a, Tok.b} := by
  rw [machineKernel_fixture_both,
    coApplyKernel_of_singletonFrontier frontier_pAboveQ]
  have hp : (fixturePat Idx.q).produces = {Tok.b} := rfl
  rw [patternKernel, hp, Finset.empty_union,
    if_neg (by decide : ({Tok.a, Tok.b} : Finset Tok) ≠ {Tok.b}),
    if_neg (by decide : ({Tok.a, Tok.b} : Finset Tok) ≠ ∅)]
  norm_num

end BadCase

#print axioms machineCoApplyKernel
#print axioms machineCoApplyKernel_eq
#print axioms machineCoApplyKernel_rowsum
#print axioms machineCoApplyKernel_nonneg
#print axioms machineCoApplyKernel_eq_cascadeKernel_of_chain
#print axioms machineFrontierConflict
#print axioms machineFrontierConflict_eq
#print axioms CoApplicationAbsence
#print axioms machineCoApplication
#print axioms machineCoApplication_of_stratification
#print axioms machineCoApplication_cycle
#print axioms fixture_no_containment_edges
#print axioms machineKernel_fixture
#print axioms machineKernel_fixture_both
#print axioms pAboveQ
#print axioms reach_pAboveQ
#print axioms frontier_pAboveQ
#print axioms machineKernel_differs_at_other_order

end DarkTower.WarMachine.Proof2.CoApplicationAtMachine
