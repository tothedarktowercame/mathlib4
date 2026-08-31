import DarkTower.WarMachine.BayesFactorThresholdWitness

open DarkTower.WarMachine.Holes

noncomputable def perTickF : VariationalFreeEnergyValue := ⟨-7 / 2⟩

-- Must fail: per-tick variational F is not BMR model-change evidence.
example : bayesFactorThreshold perTickF := by
  norm_num [bayesFactorThreshold, perTickF]
