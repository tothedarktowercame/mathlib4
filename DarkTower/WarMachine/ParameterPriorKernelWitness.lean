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
  mass := fun p o => match p, o with
    | .inspect, .cautious => 1
    | .repair, .bold => 1
    | _, _ => 0
  nonnegative := by intro p o; cases p <;> cases o <;> norm_num
  support_nodup := by intro p; cases p <;> simp
  mass_eq_zero_of_not_mem := by intro p o h; cases p <;> cases o <;> simp_all
  normalised := by intro p; cases p <;> simp

theorem inspectRowMass :
    ((prior.support .inspect).map (prior.mass .inspect)).sum = 1 :=
  prior.normalised .inspect

theorem allPriorRowsNormalised (p : Policy) :
    ((prior.support p).map (prior.mass p)).sum = 1 :=
  prior.normalised p

end DarkTower.WarMachine.ParameterPriorKernelWitness
