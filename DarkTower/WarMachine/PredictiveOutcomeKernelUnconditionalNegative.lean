import DarkTower.WarMachine.PredictiveOutcomeKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.PredictiveOutcomeKernelWitness

noncomputable def unconditional : PreferenceDistribution Obs where
  support := fun _ => [clear, fixed]
  mass := by
    classical
    exact fun s o => if o ∈ [clear, fixed] then 1 / 2 else 0
  nonnegative := by intros; split <;> norm_num
  support_nodup := by intro; simp [clear, fixed]
  mass_eq_zero_of_not_mem := by intro s o h; simp_all
  normalised := by
    intro s
    classical
    norm_num [clear, fixed]

-- Must fail: an unconditional distribution is not Q(o|pi).
/--
error: Type mismatch
  unconditional
has type
  PreferenceDistribution Obs
but is expected to have type
  PredictiveOutcomeKernel Policy Obs
-/
#guard_msgs in
def badPredictive : PredictiveOutcomeKernel Policy Obs := unconditional
