import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.ModelReductionFreeEnergyChangeWitness

open Holes

structure ReductionChangeReference where
  A : DirichletConcentrations
  reducedPrior : DirichletConcentrations
  prior : DirichletConcentrations
  reducedPosterior : DirichletConcentrations
  expectedChange : ℝ

noncomputable def reductionChangeReference : ReductionChangeReference :=
  { A := ⟨[1, 1], by simp⟩
    reducedPrior := ⟨[1, 1], by simp⟩
    prior := ⟨[2, 1], by simp⟩
    reducedPosterior := ⟨[1, 1], by simp⟩
    expectedChange := Real.log 2 }

/-- From `B(1,1)=1` and `B(2,1)=1/2`, the four-term BMR expression
`ln B(1,1)+ln B(1,1)-ln B(2,1)-ln B(1,1)` is exactly `log 2`. -/
theorem gammaIdentityChange :
    (modelReductionFreeEnergyChange reductionChangeReference.A
      reductionChangeReference.reducedPrior reductionChangeReference.prior
      reductionChangeReference.reducedPosterior).value =
      reductionChangeReference.expectedChange := by
  norm_num [modelReductionFreeEnergyChange, logMultivariateBeta, reductionChangeReference,
    Real.Gamma_add_one, Real.Gamma_one]

end DarkTower.WarMachine.ModelReductionFreeEnergyChangeWitness
