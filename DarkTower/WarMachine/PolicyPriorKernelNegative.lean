import DarkTower.WarMachine.Holes

open DarkTower.WarMachine.Holes

inductive Policy where | inspect | repair deriving DecidableEq

inductive HiddenState where | one | two

noncomputable def stateConditioned : ProbabilityKernel HiddenState Policy where
  support := fun _ => [.inspect, .repair]
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

-- Must fail: a state-conditioned kernel is not the Unit-conditioned prior.
/--
error: Type mismatch
  stateConditioned
has type
  ProbabilityKernel HiddenState Policy
but is expected to have type
  PolicyPriorKernel Policy
-/
#guard_msgs in
def badPrior : PolicyPriorKernel Policy := stateConditioned
