import DarkTower.WarMachine.ModelReductionFreeEnergyChangeWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.ModelReductionFreeEnergyChangeWitness

-- Must fail: the hand-derived value is log 2, not zero.
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example :
    (modelReductionFreeEnergyChange reductionChangeReference.A
      reductionChangeReference.reducedPrior reductionChangeReference.prior
      reductionChangeReference.reducedPosterior).value = 0 := by
  norm_num [modelReductionFreeEnergyChange, logMultivariateBeta, reductionChangeReference,
    Real.Gamma_add_one, Real.Gamma_one]
