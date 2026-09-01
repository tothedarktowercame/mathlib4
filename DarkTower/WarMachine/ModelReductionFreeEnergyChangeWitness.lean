import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.ModelReductionFreeEnergyChangeWitness

open Holes

def alpha11 : DirichletConcentrations := ⟨[1, 1], by simp⟩
def alpha21 : DirichletConcentrations := ⟨[2, 1], by simp⟩

/-- From `B(1,1)=1` and `B(2,1)=1/2`, the four-term BMR expression
`ln B(1,1)+ln B(1,1)-ln B(2,1)-ln B(1,1)` is exactly `log 2`. -/
theorem gammaIdentityChange :
    (modelReductionFreeEnergyChange alpha11 alpha11 alpha21 alpha11).value =
      Real.log 2 := by
  norm_num [modelReductionFreeEnergyChange, logMultivariateBeta, alpha11, alpha21,
    Real.Gamma_add_one, Real.Gamma_one]

end DarkTower.WarMachine.ModelReductionFreeEnergyChangeWitness
