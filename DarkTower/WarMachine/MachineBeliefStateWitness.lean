import DarkTower.WarMachine.MachineBeliefState

namespace DarkTower.WarMachine.MachineBeliefStateWitness
open DarkTower.WarMachine.MachineBeliefState

def peaked : Posterior := fun s => if s = .spawned then 1 else 0
noncomputable def fresh01 : machineBeliefState := fun e => if e = 0 ∨ e = 1 then some uniformPrior else none
def carried02 : machineBeliefState := fun e => if e = 0 then some peaked else if e = 2 then some peaked else none

theorem carryEqualsNeitherInput :
    reconcileBeliefCarry fresh01 carried02 ≠ fresh01 ∧
    reconcileBeliefCarry fresh01 carried02 ≠ carried02 := by
  constructor
  · intro h
    have hs := congrFun h 0
    simp [reconcileBeliefCarry, fresh01, carried02] at hs
    have hv := congrFun hs .spawned
    norm_num [peaked, uniformPrior] at hv
  · intro h; have := congrFun h 1; simp [reconcileBeliefCarry, fresh01, carried02] at this

noncomputable def only0 : machineBeliefState := fun e => if e = 0 then some uniformPrior else none
def empty : machineBeliefState := fun _ => none

theorem reentryLosesHistory :
    let t0 : machineBeliefState := fun e => if e = 0 then some peaked else none
    let t1 := reconcileBeliefCarry empty t0
    let t2 := reconcileBeliefCarry only0 t1
    t0 0 = some peaked ∧ t1 0 = none ∧ t2 0 = some uniformPrior := by
  simp [reconcileBeliefCarry, empty, only0]

noncomputable def collisionA : Posterior := fun s =>
  match s with | .spawned => 1/2 | .refined => 3/10 | .strengthened => 1/5 | _ => 0
noncomputable def collisionB : Posterior := fun s =>
  match s with | .spawned => 1/2 | .refined => 1/5 | .strengthened => 3/10 | _ => 0

theorem collisionDistinct : collisionA ≠ collisionB := by
  intro h; have := congrFun h .refined; norm_num [collisionA, collisionB] at this

/-- Both counterexamples are distributions.  Without this the collision below is
a fact about two arbitrary functions rather than about two posteriors. -/
theorem collisionAIsNormalised : Normalised collisionA := by
  simp [Normalised, Status.all, collisionA]
  norm_num

theorem collisionBIsNormalised : Normalised collisionB := by
  simp [Normalised, Status.all, collisionB]
  norm_num

theorem peakedIsNormalised : Normalised peaked := by
  simp [Normalised, Status.all, peaked]

/-- STRICT, deliberately.  `most-likely-status` (`belief.clj:447-452`) is
`(key (apply max-key val posterior))`, whose value on a tie is whichever entry
`max-key` reaches first.  A non-strict maximum would therefore not force the
`:spawned` the readback measures; a strict one does. -/
theorem collisionSpawnedIsStrictArgmax (s : Status) (hs : s ≠ Status.spawned) :
    collisionA s < collisionA .spawned ∧ collisionB s < collisionB .spawned := by
  cases s <;> simp_all <;> norm_num [collisionA, collisionB]

theorem collisionSameEntropy : entropy collisionA = entropy collisionB := by
  simp [entropy, Status.all, collisionA, collisionB]
  ring

theorem collisionEntropyReference :
    entropy collisionA =
      -(1/2 * Real.log (1/2) + 3/10 * Real.log (3/10) +
        1/5 * Real.log (1/5)) := by
  simp [entropy, Status.all, collisionA]
  ring

theorem uniformEntropyReference :
    entropy uniformPrior = -(7 * (1/7 * Real.log (1/7))) := by
  simp [entropy, Status.all, uniformPrior]
  ring

theorem uniformCoordinates : ∀ s, uniformPrior s = 1/7 := by
  intro s; rfl

/-! ## Pinned production reference rows (2026-09-04 and 2026-05-23)

The decimal numerals below are the exact decimal renderings retained in
`row-7-belief-state-2026-09-12/input.edn`.  The production reader carries
these coordinates without renormalising them; the accompanying Clojure
readback records the IEEE-double comparison for every coordinate. -/

noncomputable def carriedTracePosterior : Posterior
  | .spawned => 0.10532904980883244
  | .refined => 0.14086253396643547
  | .strengthened => 0.31240050666821867
  | .addressed => 0.09555013225308848
  | .falsified => 0.07447381184188043
  | .foreclosed => 0.1660549156527121
  | .reopened => 0.10532904980883244

theorem carriedTraceCoordinates :
    carriedTracePosterior .spawned = 0.10532904980883244 ∧
    carriedTracePosterior .refined = 0.14086253396643547 ∧
    carriedTracePosterior .strengthened = 0.31240050666821867 ∧
    carriedTracePosterior .addressed = 0.09555013225308848 ∧
    carriedTracePosterior .falsified = 0.07447381184188043 ∧
    carriedTracePosterior .foreclosed = 0.1660549156527121 ∧
    carriedTracePosterior .reopened = 0.10532904980883244 := by
  norm_num [carriedTracePosterior]

noncomputable def bootstrappedTracePosterior : Posterior := fun _ =>
  0.14285714285714285

theorem bootstrappedTraceCoordinates : ∀ s,
    bootstrappedTracePosterior s = 0.14285714285714285 := by
  intro s
  rfl

noncomputable def retainedTraceBelief : machineBeliefState
  | 0 => some carriedTracePosterior
  | 1 => some bootstrappedTracePosterior
  | _ => none

theorem retainedTraceBeliefReferences :
    retainedTraceBelief 0 = some carriedTracePosterior ∧
    retainedTraceBelief 1 = some bootstrappedTracePosterior := by
  constructor <;> rfl

/-- THE FINDING, as one proposition rather than as pieces a reader must assemble.
`docs/futon-aif-completeness.md:49-68` requires "mean *and* precision (variance)
both explicitly represented" and `:63-64` answers with `most-likely-status` and
`entropy`.  Two distinct posteriors share both, so the pair does not determine
the posterior and is not a sufficient statistic for it.  Whether that satisfies
the criterion is a ruling and none is made here. -/
theorem momentPairIsNotSufficient :
    Normalised collisionA ∧ Normalised collisionB ∧
    collisionA ≠ collisionB ∧
    (∀ s, s ≠ Status.spawned →
      collisionA s < collisionA .spawned ∧ collisionB s < collisionB .spawned) ∧
    entropy collisionA = entropy collisionB :=
  ⟨collisionAIsNormalised, collisionBIsNormalised, collisionDistinct,
   fun s hs => collisionSpawnedIsStrictArgmax s hs, collisionSameEntropy⟩

end DarkTower.WarMachine.MachineBeliefStateWitness
