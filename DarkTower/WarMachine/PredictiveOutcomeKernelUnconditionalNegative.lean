import DarkTower.WarMachine.PredictiveOutcomeKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.PredictiveOutcomeKernelWitness

noncomputable def unconditional : PreferenceDistribution Obs where
  support := fun _ => [clear, fixed]
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

-- Must fail: an unconditional distribution is not Q(o|pi).
def badPredictive : PredictiveOutcomeKernel Policy Obs := unconditional
