import DarkTower.WarMachine.ParameterPosteriorKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.ParameterPosteriorKernelWitness

noncomputable def outcomePrediction : PredictiveOutcomeKernel Policy Obs where
  support := fun _ => [clear]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

-- Must fail: Q(o|pi) has neither the posterior's domain nor its codomain.
def badPosterior : ParameterPosteriorKernel Policy Obs Parameter := outcomePrediction
