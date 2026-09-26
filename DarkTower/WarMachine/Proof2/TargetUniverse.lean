import DarkTower.WarMachine.Proof2.TargetGrainG

/-!
# The target's token universe U(t), declared (C7, registry `:target-universe`)

This row is the registry's ONE row with no `:lean` at all, and its
`:lean-absent` says why: "the universe is the Finset `U` that
`Proof2.TargetGrainG.localDelta` takes as an ARGUMENT; no declaration names
it". `targetUniverse` is that declaration, so `:target-grain-g` imports U from
a named thing rather than binding it free.

## What the ok arm reads U from

**The field entry's recorded universe**, which is what
`futon2:src/futon2/aif/target_field.clj:278-308` (`with-pair-overlap`) reads:
`universe-of` keeps `(:universe e)` per feasible entry and yields
`{:absent :no-universe}` for a target that has none. `Target.recordedUniverse`
is that field, as an `Option (Finset V)`.

**Not the reading.** The row's `:formal` says U is "read from t's own text at
click time — the same reading step that produces C". That STEP is H-C's, and it
is `:mission-preference`'s row, not this one. This module declares U from what
the field records; it takes the reading's output and says nothing about how the
reading gets it.

## Absent is not empty, and the default would be silent

`with-pair-overlap`'s discriminator is `(when (:universe e) …)`: `nil` means
the target records none, and anything else — INCLUDING an empty collection,
which is truthy in Clojure — means it recorded one. So the code already
distinguishes the two, and `noUniverseIsNotEmpty` states it: a target with no
universe is REFUSED where a target with the empty universe is accepted as `∅`.

Why that matters rather than being a nicety: `localDelta` is
`-∑ v ∈ U, (…)`, so `localDelta ∅ = 0` (`emptyUniverseGivesZeroDelta`).
Defaulting an absent universe to `∅` would therefore score EVERY candidate at
ΔG = 0 — every target indistinguishable from the baseline and from every other
target — and nothing downstream could tell that from a real tie.
`localDeltaAt_absent` is the arm that refuses instead.

## What I found in the code, and it is not what the `:code` line implies

`with-pair-overlap` reads `:universe` off each feasible entry, and **nothing
writes it**. `target_field.clj`'s entry builders (`step`, `constructor-step`)
never attach one, no other namespace assoc's `:universe` onto a target-field
entry, and no test constructs an entry carrying one. So at futon2 HEAD
`universe-of` is empty and EVERY target records none — the typed absence this
module returns is not a corner case, it is the whole field. (`assess` at
`:213-277` separately reads the SOURCES' `:universes` map, keyed by target, as
an observation view `token ↦ bool`; that is a different object from the token
SET this row defines, and this module does not model it.)

## What this module does not claim

Nothing about the click-time reading (H-C), about pair overlap or
commensurability (`TargetGrainG.target_comparison` has that), or about how a
universe would be populated — only what U is once recorded, and what happens
when it is not.
-/

namespace DarkTower.WarMachine.Proof2.TargetUniverse

open DarkTower.WarMachine.Proof2.TargetGrainG

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A target of the field, carrying its universe as the field records it:
`none` is "records none", `some u` is a recorded universe — which may be
empty. -/
structure Target (V : Type*) where
  id : String
  recordedUniverse : Option (Finset V)

/-- The one absence, named with the target it is about. Not a value. -/
inductive UniverseAbsence where
  | noUniverse (target : String)
  deriving DecidableEq

/-- **U(t).** The target's token universe, or the typed absence. -/
def targetUniverse (t : Target V) : Except UniverseAbsence (Finset V) :=
  match t.recordedUniverse with
  | some u => .ok u
  | none => .error (.noUniverse t.id)

omit [Fintype V] [DecidableEq V] in
/-- **`targetUniverse_eq_recorded`.** The ok arm is exactly what the field
recorded — nothing is added to it or filtered out of it. -/
theorem targetUniverse_eq_recorded (t : Target V) (u : Finset V)
    (h : t.recordedUniverse = some u) : targetUniverse t = .ok u := by
  simp [targetUniverse, h]

omit [Fintype V] [DecidableEq V] in
/-- A target that records none is refused, by name. -/
theorem targetUniverse_absent (t : Target V) (h : t.recordedUniverse = none) :
    targetUniverse t = .error (.noUniverse t.id) := by
  simp [targetUniverse, h]

omit [Fintype V] [DecidableEq V] in
/-- **`noUniverseIsNotEmpty`.** The two states are distinguishable, which is
`with-pair-overlap`'s own discriminator: a target with NO universe is refused,
a target with the EMPTY universe is accepted as `∅`, and the results differ. -/
theorem noUniverseIsNotEmpty (idAbsent idEmpty : String) :
    targetUniverse (⟨idAbsent, none⟩ : Target V) = .error (.noUniverse idAbsent) ∧
    targetUniverse (⟨idEmpty, some ∅⟩ : Target V) = .ok ∅ ∧
    targetUniverse (⟨idAbsent, none⟩ : Target V)
      ≠ targetUniverse (⟨idEmpty, some ∅⟩ : Target V) := by
  refine ⟨rfl, rfl, ?_⟩
  simp [targetUniverse]

/-! ## The tie to `localDelta` -/

/-- **ΔG_t at the target's own universe.** `TargetGrainG.localDelta` binds `U`
free; this supplies it from the target, and refuses when the target has none.
There is no arm that picks a universe. -/
noncomputable def localDeltaAt (t : Target V) (q₁ q₂ : Finset V → ℝ)
    (cIn cOut : V → ℝ) : Except UniverseAbsence ℝ :=
  (targetUniverse t).map (fun U => localDelta U q₁ q₂ cIn cOut)

/-- On the ok arm it IS `localDelta` at the recorded universe. -/
theorem localDeltaAt_ok (t : Target V) (u : Finset V)
    (h : t.recordedUniverse = some u) (q₁ q₂ : Finset V → ℝ) (cIn cOut : V → ℝ) :
    localDeltaAt t q₁ q₂ cIn cOut = .ok (localDelta u q₁ q₂ cIn cOut) := by
  simp [localDeltaAt, targetUniverse_eq_recorded t u h, Except.map]

/-- **`localDeltaAt_absent`.** With no universe there is no delta on ANY
arguments: no default universe on any arm. -/
theorem localDeltaAt_absent (t : Target V) (h : t.recordedUniverse = none)
    (q₁ q₂ : Finset V → ℝ) (cIn cOut : V → ℝ) :
    localDeltaAt t q₁ q₂ cIn cOut = .error (.noUniverse t.id) := by
  simp [localDeltaAt, targetUniverse_absent t h, Except.map]

/-- **Why the absence may not default to `∅`.** `localDelta` sums over `U`, so
the empty universe gives delta ZERO for every candidate and every preference.
A target defaulted to `∅` would therefore be indistinguishable from the
baseline and from every other defaulted target, and nothing downstream could
tell that from a real tie. -/
theorem emptyUniverseGivesZeroDelta (q₁ q₂ : Finset V → ℝ) (cIn cOut : V → ℝ) :
    localDelta (∅ : Finset V) q₁ q₂ cIn cOut = 0 := by
  simp [localDelta]

/-- And the default would be reached at EVERY target with no universe, which at
futon2 HEAD is all of them: stated as the composition it would be. -/
theorem defaultingWouldFlattenEveryTarget (t : Target V)
    (h : t.recordedUniverse = none) (q₁ q₂ : Finset V → ℝ) (cIn cOut : V → ℝ) :
    localDeltaAt t q₁ q₂ cIn cOut = .error (.noUniverse t.id) ∧
    localDelta ((targetUniverse t).toOption.getD ∅) q₁ q₂ cIn cOut = 0 := by
  refine ⟨localDeltaAt_absent t h q₁ q₂ cIn cOut, ?_⟩
  rw [targetUniverse_absent t h]
  exact emptyUniverseGivesZeroDelta q₁ q₂ cIn cOut

#print axioms Target
#print axioms UniverseAbsence
#print axioms targetUniverse
#print axioms targetUniverse_eq_recorded
#print axioms targetUniverse_absent
#print axioms noUniverseIsNotEmpty
#print axioms localDeltaAt
#print axioms localDeltaAt_ok
#print axioms localDeltaAt_absent
#print axioms emptyUniverseGivesZeroDelta
#print axioms defaultingWouldFlattenEveryTarget

end DarkTower.WarMachine.Proof2.TargetUniverse
