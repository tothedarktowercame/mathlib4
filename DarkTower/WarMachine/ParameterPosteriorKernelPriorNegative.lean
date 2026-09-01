import DarkTower.WarMachine.ParameterPosteriorKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.ParameterPosteriorKernelWitness

noncomputable def parameterPrior : ParameterPriorKernel Policy Parameter where
  support := fun _ => [.cautious]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

-- Must fail: Q(theta|pi) omits the observed-outcome conditioning coordinate.
def badPosterior : ParameterPosteriorKernel Policy Obs Parameter := parameterPrior
