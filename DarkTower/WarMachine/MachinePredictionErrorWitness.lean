import DarkTower.WarMachine.MachinePredictionError
import DarkTower.WarMachine.MachinePrecisionWitness

/-!
# Reference values for the machine's prediction error

`futon2:holes/labs/wm-contract/worklist.edn` `:F8`, leg 1, slice 2. Exact
arithmetic against the production implementation
(`futon2:src/futon2/aif/free_energy.clj`), whose doubles were read by
`futon2:holes/labs/wm-contract/runs/F8-prediction-error/clojure-readback.txt`.

EXACTNESS, WITH ITS ONE EXCEPTION STATED. Every observation, mean and
variance below is dyadic, so the Clojure double and the Lean rational are the
same number and the comparison needs no tolerance — EXCEPT in the two floored
cases, where the arithmetic goes through `min-variance` `0.01`, which is NOT
dyadic (the double is
`0.01000000000000000020816681711721685132943093776702880859375`). There the
Lean value `100` and the Clojure value agree because `1.0 / 0.01` happens to
round back to exactly `100.0`, not because the operands are representable.
That is a rounding fact and it is named rather than folded into the others.
-/

namespace DarkTower.WarMachine.MachinePredictionErrorWitness

open DarkTower.WarMachine.MachinePredictionError

/-- The declared default of this producer, `free_energy.clj:240`. -/
noncomputable def mv : ℝ := 1 / 100

/-! ### The scored arm -/

/-- Observation 3/4 against a prediction of 1/4 with variance 1/4. -/
theorem basicTriple :
    (presentRecord mv (3/4) (1/4) (1/4)).error = 1/2 ∧
      (presentRecord mv (3/4) (1/4) (1/4)).perCallPrecision = 4 ∧
      (presentRecord mv (3/4) (1/4) (1/4)).weightedError = 2 := by
  refine ⟨by norm_num [presentRecord], ?_, ?_⟩ <;>
    norm_num [presentRecord, mv, max_def]

/-- Unit variance: the per-call precision is 1, so the weighted error is the
error. -/
theorem unitVariance :
    (presentRecord mv (3/4) (1/4) 1).perCallPrecision = 1 ∧
      (presentRecord mv (3/4) (1/4) 1).weightedError = 1/2 := by
  constructor <;> norm_num [presentRecord, mv, max_def]

/-- AN EMPTY BELIEF PREDICTS NOTHING, AND ε IS THEN THE OBSERVATION ITSELF.
`belief.clj:651-652` returns `{:mean 0.0 :variance 1.0}` — maximally uncertain
— for a belief with no entities, so on the first tick of a fresh belief the
machine's prediction error on a likelihood channel equals the raw observation
and the per-call precision is 1. -/
theorem emptyBeliefReadsTheObservation :
    (presentRecord mv (3/4) 0 1).error = 3/4 ∧
      (presentRecord mv (3/4) 0 1).perCallPrecision = 1 ∧
      (presentRecord mv (3/4) 0 1).weightedError = 3/4 := by
  refine ⟨by norm_num [presentRecord], ?_, ?_⟩ <;>
    norm_num [presentRecord, mv, max_def]

theorem negativeError :
    (presentRecord mv (1/4) (3/4) (1/4)).error = -(1/2) ∧
      (presentRecord mv (1/4) (3/4) (1/4)).weightedError = -2 := by
  refine ⟨by norm_num [presentRecord], ?_⟩
  norm_num [presentRecord, mv, max_def]

/-- A channel observed exactly where it was predicted contributes nothing,
whatever its precision. -/
theorem exactZeroError :
    (presentRecord mv (1/2) (1/2) (1/4)).error = 0 ∧
      (presentRecord mv (1/2) (1/2) (1/4)).weightedError = 0 := by
  refine ⟨by norm_num [presentRecord], ?_⟩
  norm_num [presentRecord, mv, max_def]

theorem eighthVariance :
    (presentRecord mv (3/4) (1/4) (1/8)).perCallPrecision = 8 ∧
      (presentRecord mv (3/4) (1/4) (1/8)).weightedError = 4 := by
  constructor <;> norm_num [presentRecord, mv, max_def]

/-! ### The floor, and the negative variance it absorbs -/

/-- A likelihood reporting certainty is floored: precision 100, not division
by zero. -/
theorem zeroVarianceFloored :
    (presentRecord mv (3/4) (1/4) 0).perCallPrecision = 100 ∧
      (presentRecord mv (3/4) (1/4) 0).weightedError = 50 := by
  constructor <;> norm_num [presentRecord, mv, max_def]

/-- AND SO IS A VARIANCE THAT CANNOT EXIST. `-4` is a finite number, so
`prediction-member` calls it present and the producer scores it. -/
theorem negativeVarianceFloored :
    (presentRecord mv (3/4) (1/4) (-4)).perCallPrecision = 100 ∧
      (presentRecord mv (3/4) (1/4) (-4)).weightedError = 50 := by
  constructor <;> norm_num [presentRecord, mv, max_def]

/-- THE FINDING, EXHIBITED. The two records are the same in every field the
downstream update reads; they differ only in the `:predicted-variance` nobody
downstream consults. A negative variance is therefore not merely accepted —
it is invisible after the floor. -/
theorem zeroAndNegativeVarianceAgree :
    (presentRecord mv (3/4) (1/4) 0).perCallPrecision
        = (presentRecord mv (3/4) (1/4) (-4)).perCallPrecision ∧
      (presentRecord mv (3/4) (1/4) 0).weightedError
        = (presentRecord mv (3/4) (1/4) (-4)).weightedError ∧
      (presentRecord mv (3/4) (1/4) 0).predictedVariance
        ≠ (presentRecord mv (3/4) (1/4) (-4)).predictedVariance := by
  refine ⟨?_, ?_, by norm_num [presentRecord]⟩ <;>
    norm_num [presentRecord, mv, max_def]

/-! ### The typed absences and refusals -/

/-- An unobserved channel under a working model is OMITTED, and its record
carries no numbers. -/
theorem unobservedIsOmitted :
    machineChannelPredictionError mv Field.missing
        ⟨Field.value (1/4), Field.value (1/4)⟩ = Outcome.absent Member.observed := rfl

/-- A likelihood that produced no mean REFUSES, naming the member. -/
theorem brokenModelRefuses :
    machineChannelPredictionError mv (Field.value (3/4))
        ⟨Field.missing, Field.value (1/4)⟩
      = Outcome.refused [Offence.missing Member.mean] := rfl

/-- REFUSAL DOMINATES ABSENCE, exhibited: the observation is missing AND the
mean is missing, and the record that comes out is a refusal naming the mean —
the missing observation is not even reported. -/
theorem unobservedWithBrokenModelRefuses :
    machineChannelPredictionError mv Field.missing
        ⟨Field.missing, Field.value (1/4)⟩
      = Outcome.refused [Offence.missing Member.mean] := rfl

/-- A non-numeric observation is refused rather than omitted, and the offence
names `observed`. -/
theorem malformedObservationRefuses :
    machineChannelPredictionError mv Field.notFinite
        ⟨Field.value (1/4), Field.value (1/4)⟩
      = Outcome.refused [Offence.notFinite Member.observed] := rfl

/-- Both model members broken: both are named, in `[mean variance]` order. -/
theorem bothModelMembersNamed :
    machineChannelPredictionError mv (Field.value (3/4)) ⟨Field.missing, Field.notFinite⟩
      = Outcome.refused [Offence.missing Member.mean, Offence.notFinite Member.variance] := rfl

/-! ### The two precisions are two numbers -/

/-- THE COLLISION, IN NUMBERS. On one channel in one tick with a single
prediction error of `1/2`: the producer stamps `:precision` `4`, computed from
the LIKELIHOOD's variance `1/4`; R7's Π for that same channel, computed from
the ERROR HISTORY `[1/2]`, is `8/5` (`MachinePrecisionWitness.halfError`, slice
1). `precision/weighted-error` (`precision.clj:213-233`) then overwrites the
first with the second and keeps it as `:per-call-precision`, so the weighted
error the belief update consumes is `2/5` and not the `2` the producer emitted.
Two quantities, one key, and the value under that key changes inside the tick. -/
theorem perCallPrecisionIsNotMachinePrecision :
    (presentRecord mv (3/4) (1/4) (1/4)).perCallPrecision = 4 ∧
      MachinePrecision.machinePrecision MachinePrecision.defaults [1/2] = 8/5 ∧
      (presentRecord mv (3/4) (1/4) (1/4)).perCallPrecision
        ≠ MachinePrecision.machinePrecision MachinePrecision.defaults [1/2] := by
  have hpi : (presentRecord mv (3/4) (1/4) (1/4)).perCallPrecision = 4 := by
    norm_num [presentRecord, mv, max_def]
  refine ⟨hpi, MachinePrecisionWitness.halfError, ?_⟩
  rw [hpi, MachinePrecisionWitness.halfError]
  norm_num

end DarkTower.WarMachine.MachinePredictionErrorWitness
