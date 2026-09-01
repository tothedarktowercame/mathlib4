import DarkTower.WarMachine.ModelReductionFreeEnergyChangeWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.ModelReductionFreeEnergyChangeWitness

-- Must fail: the hand-derived value is log 2, not zero.
example :
    (modelReductionFreeEnergyChange alpha11 alpha11 alpha21 alpha11).value = 0 := by
  norm_num [modelReductionFreeEnergyChange, logMultivariateBeta, alpha11, alpha21,
    Real.Gamma_add_one, Real.Gamma_one]
