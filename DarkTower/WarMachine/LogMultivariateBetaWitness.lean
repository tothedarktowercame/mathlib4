import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.LogMultivariateBetaWitness

open Holes

private def alpha11 : {xs : List ℝ // xs ≠ [] ∧ ∀ x ∈ xs, 0 < x} :=
  ⟨[1, 1], by simp⟩

private def alpha21 : {xs : List ℝ // xs ≠ [] ∧ ∀ x ∈ xs, 0 < x} :=
  ⟨[2, 1], by simp⟩

structure BetaReference where
  firstConcentrations : List ℝ
  firstExpectedLog : ℝ
  secondConcentrations : List ℝ
  secondExpectedLog : ℝ

noncomputable def betaReference : BetaReference :=
  { firstConcentrations := [1, 1], firstExpectedLog := 0,
    secondConcentrations := [2, 1], secondExpectedLog := -Real.log 2 }

/-- `B(1,1) = 1`, derived from `Γ(1)=Γ(2)=1`. -/
theorem unit_pair : logMultivariateBeta alpha11 = betaReference.firstExpectedLog := by
  norm_num [betaReference, logMultivariateBeta, alpha11, Real.Gamma_add_one, Real.Gamma_one]

/-- `B(2,1) = 1/2`, derived independently from `Γ(n)=(n-1)!`. -/
theorem asymmetric_pair : logMultivariateBeta alpha21 = betaReference.secondExpectedLog := by
  norm_num [betaReference, logMultivariateBeta, alpha21, Real.Gamma_add_one, Real.Gamma_one]

end DarkTower.WarMachine.LogMultivariateBetaWitness
