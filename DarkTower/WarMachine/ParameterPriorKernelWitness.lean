import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.ParameterPriorKernelWitness

open Holes

inductive Policy where | inspect | repair deriving DecidableEq
inductive Parameter where | cautious | bold deriving DecidableEq

/-- Hand-derived deterministic parameter priors: inspect predicts cautious
parameters; repair predicts bold parameters. Each policy row has mass one. -/
noncomputable def prior : ParameterPriorKernel Policy Parameter where
  support
    | .inspect => [.cautious]
    | .repair => [.bold]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intro p; cases p <;> simp

theorem inspectRowMass :
    ((prior.support .inspect).map (prior.mass .inspect)).sum = 1 :=
  prior.normalised .inspect

end DarkTower.WarMachine.ParameterPriorKernelWitness
