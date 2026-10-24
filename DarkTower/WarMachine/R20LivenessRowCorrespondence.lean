import DarkTower.WarMachine.R20Certificate

/-!
# Supplied R20 liveness-row correspondence

This module relates an explicitly supplied before/after state pair and Boolean
liveness report to the existing `R20Certificate.LivenessConforms` predicate.
It does not change that predicate.

The runtime liveness producer is currently absent.  Consequently this module
contains no retained live fixture and makes no claim to decode, authenticate,
or otherwise establish the provenance of a runtime record.  `RawRow.absent`
stays absent.  A present row carries values supplied over an arbitrary type with
decidable equality.

`encodePair` is local to one supplied pair: before is encoded as `0`; after is
`0` exactly when equal to before and `1` otherwise.  This preserves precisely
the equality used by the finite liveness predicate.  It is not a global state
registry, hash, or identity assignment.
-/

namespace DarkTower.WarMachine.R20LivenessRowCorrespondence

open DarkTower.WarMachine.R20Certificate
open DarkTower.WarMachine.R10ScheduledEntrypoint

/-- The three existing finite-row values, before any adaptation to `Nat`. -/
structure SuppliedTick (State : Type) where
  beforeState : State
  afterState : State
  reportedLive : Bool
  deriving Repr

/-- Presence is explicit.  Missing input is not a false label or default state. -/
inductive RawRow (State : Type) where
  | absent
  | present (tick : SuppliedTick State)
  deriving Repr

/-- Equality-preserving local encoding of one supplied state pair. -/
def encodePair {State : Type} [DecidableEq State] (before after : State) : Nat × Nat :=
  (0, if after = before then 0 else 1)

theorem encodePair_preserves_equality {State : Type} [DecidableEq State]
    (before after : State) :
    (encodePair before after).1 = (encodePair before after).2 ↔ before = after := by
  simp [encodePair, eq_comm]

/-- Project a supplied tick to the unchanged R20 `LiveRow`. -/
def project {State : Type} [DecidableEq State] (tick : SuppliedTick State) : LiveRow :=
  let encoded := encodePair tick.beforeState tick.afterState
  { beforeState := encoded.1
    afterState := encoded.2
    reportedLive := tick.reportedLive }

/-- Adapt only a present supplied row. -/
def adapt {State : Type} [DecidableEq State] : RawRow State → Option LiveRow
  | .absent => none
  | .present tick => some (project tick)

/-- The finite runtime-side honesty rule, stated independently of `project`. -/
def SuppliedHonest {State : Type} (tick : SuppliedTick State) : Prop :=
  tick.reportedLive = true → tick.beforeState ≠ tick.afterState

/-- Exact supplied-value correspondence for every present row. -/
theorem suppliedHonest_iff_conforms {State : Type} [DecidableEq State]
    (tick : SuppliedTick State) :
    SuppliedHonest tick ↔ LivenessConforms (project tick) := by
  simp only [SuppliedHonest, LivenessConforms, HonestLiveness, List.mem_singleton]
  constructor
  · intro honest projected _ labelled
    subst projected
    intro equal
    apply honest labelled
    exact (encodePair_preserves_equality tick.beforeState tick.afterState).mp equal
  · intro conforms labelled equal
    have changed := conforms (project tick) rfl labelled
    apply changed
    exact (encodePair_preserves_equality tick.beforeState tick.afterState).mpr equal

/-- The printed case depends only on whether the supplied states are equal. -/
def suppliedCase {State : Type} [DecidableEq State] (tick : SuppliedTick State) : LivenessCase :=
  if tick.beforeState = tick.afterState then .notLive else .live

theorem suppliedCase_eq_caseOf {Policy State : Type} [Fintype Policy] [Nonempty Policy]
    [DecidableEq State] (tick : SuppliedTick State) :
    .liveness (suppliedCase tick) =
      caseOf (Policy := Policy) .liveness (project tick) := by
  simp [suppliedCase, caseOf, LiveTick, ChangedState, project,
    encodePair_preserves_equality]

theorem absent_stays_absent {State : Type} [DecidableEq State] :
    adapt (RawRow.absent : RawRow State) = none := rfl

/-! ## Synthetic controls (not retained runtime evidence) -/

def changedTrue : SuppliedTick Bool := ⟨false, true, true⟩
def changedFalse : SuppliedTick Bool := ⟨false, true, false⟩
def equalFalse : SuppliedTick Bool := ⟨false, false, false⟩
def equalTrue : SuppliedTick Bool := ⟨false, false, true⟩

theorem changedTrue_conforms : LivenessConforms (project changedTrue) := by
  rw [← suppliedHonest_iff_conforms]
  simp [SuppliedHonest, changedTrue]

theorem changedFalse_conforms : LivenessConforms (project changedFalse) := by
  rw [← suppliedHonest_iff_conforms]
  simp [SuppliedHonest, changedFalse]

theorem equalFalse_conforms : LivenessConforms (project equalFalse) := by
  rw [← suppliedHonest_iff_conforms]
  simp [SuppliedHonest, equalFalse]

theorem equalTrue_refused : ¬ LivenessConforms (project equalTrue) := by
  rw [← suppliedHonest_iff_conforms]
  simp [SuppliedHonest, equalTrue]

theorem changedTrue_prints_live :
    caseOf (Policy := Fin 1) .liveness (project changedTrue) = .liveness .live := by
  simp [caseOf, project, changedTrue, encodePair, LiveTick, ChangedState]
theorem changedFalse_prints_live :
    caseOf (Policy := Fin 1) .liveness (project changedFalse) = .liveness .live := by
  simp [caseOf, project, changedFalse, encodePair, LiveTick, ChangedState]
theorem equalFalse_prints_notLive :
    caseOf (Policy := Fin 1) .liveness (project equalFalse) = .liveness .notLive := by
  simp [caseOf, project, equalFalse, encodePair, LiveTick, ChangedState]
theorem equalTrue_prints_notLive :
    caseOf (Policy := Fin 1) .liveness (project equalTrue) = .liveness .notLive := by
  simp [caseOf, project, equalTrue, encodePair, LiveTick, ChangedState]

#print axioms encodePair_preserves_equality
#print axioms suppliedHonest_iff_conforms
#print axioms suppliedCase_eq_caseOf
#print axioms absent_stays_absent
#print axioms changedTrue_conforms
#print axioms changedFalse_conforms
#print axioms equalFalse_conforms
#print axioms equalTrue_refused

end DarkTower.WarMachine.R20LivenessRowCorrespondence
