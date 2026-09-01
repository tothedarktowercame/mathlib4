import DarkTower.WarMachine.BayesFactorThresholdWitness

open DarkTower.WarMachine.Holes

noncomputable def perTickF : VariationalFreeEnergyValue := ⟨-7 / 2⟩

-- Must fail: per-tick variational F is not BMR model-change evidence.
/--
error: Application type mismatch: The argument
  perTickF
has type
  VariationalFreeEnergyValue
but is expected to have type
  ModelReductionFreeEnergyChange
in the application
  bayesFactorThreshold perTickF
-/
#guard_msgs in
def badThreshold : Prop := bayesFactorThreshold perTickF
