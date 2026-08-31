import DarkTower.WarMachine.TransitionKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.TransitionKernelWitness

noncomputable def uncontrolled : ProbabilityKernel State State where
  support := fun s => [s]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

-- Must fail: B is conditioned jointly on state and action.
def badTransition : TransitionKernel State Action := uncontrolled
