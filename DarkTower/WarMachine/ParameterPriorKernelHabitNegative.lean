import DarkTower.WarMachine.ParameterPriorKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.ParameterPriorKernelWitness

noncomputable def habit : PolicyPriorKernel Policy where
  support := fun _ => [.inspect, .repair]
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

-- Must fail: Q(pi) is unconditioned and ranges over policies, not parameters.
/--
error: Type mismatch
  habit
has type
  PolicyPriorKernel Policy
but is expected to have type
  ParameterPriorKernel Policy Parameter
-/
#guard_msgs in
def badPrior : ParameterPriorKernel Policy Parameter := habit
