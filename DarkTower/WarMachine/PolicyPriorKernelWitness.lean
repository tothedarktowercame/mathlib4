import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.PolicyPriorKernelWitness
open Holes

inductive Policy where | inspect | repair deriving DecidableEq

/-- The record's unconditioned fair prior over two allowable policies. -/
noncomputable def reference : PolicyPriorKernel Policy where
  support := fun _ => [.inspect, .repair]
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

theorem referenceRowMass : ((reference.support ()).map (reference.mass ())).sum = 1 :=
  reference.normalised ()

end DarkTower.WarMachine.PolicyPriorKernelWitness
