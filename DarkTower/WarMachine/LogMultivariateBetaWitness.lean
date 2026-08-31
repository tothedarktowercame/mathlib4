import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.LogMultivariateBetaWitness

open Holes

private def alpha11 : {xs : List ℝ // xs ≠ [] ∧ ∀ x ∈ xs, 0 < x} :=
  ⟨[1, 1], by simp⟩

private def alpha21 : {xs : List ℝ // xs ≠ [] ∧ ∀ x ∈ xs, 0 < x} :=
  ⟨[2, 1], by simp⟩

/-- `B(1,1) = 1`, derived from `Γ(1)=Γ(2)=1`. -/
theorem unit_pair : logMultivariateBeta alpha11 = 0 := by
  norm_num [logMultivariateBeta, alpha11, Real.Gamma_add_one, Real.Gamma_one]

/-- `B(2,1) = 1/2`, derived independently from `Γ(n)=(n-1)!`. -/
theorem asymmetric_pair : logMultivariateBeta alpha21 = -Real.log 2 := by
  norm_num [logMultivariateBeta, alpha21, Real.Gamma_add_one, Real.Gamma_one]

end DarkTower.WarMachine.LogMultivariateBetaWitness
