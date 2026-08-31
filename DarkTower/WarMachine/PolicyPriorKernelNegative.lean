import DarkTower.WarMachine.PolicyPriorKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.PolicyPriorKernelWitness

inductive HiddenState where | one | two

noncomputable def stateConditioned : ProbabilityKernel HiddenState Policy where
  support := fun _ => [.inspect, .repair]
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

-- Must fail: a state-conditioned kernel is not the Unit-conditioned prior.
def badPrior : PolicyPriorKernel Policy := stateConditioned
