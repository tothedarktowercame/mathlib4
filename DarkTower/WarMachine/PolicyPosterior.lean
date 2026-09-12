import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.PolicyPosterior

noncomputable section

/-- CARRIER · owner: sec-glossary.tex:35 · P-glossary-mathematics · holder: by-rule · evidence: Row 16 R6 production-trace witness · falsifier: the declared `F_π` term is omitted, or the zero-`F_π` branch diverges from `softmax` · The full policy posterior is Q(π) ∝ exp(ln E(π) − G(π)/τ − F_π(π)). -/
def softmaxWithFPi {PolicyIndex : Type*} (exp log : ℝ → ℝ)
    (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → DarkTower.WarMachine.Holes.ExpectedFreeEnergyValue)
    (fPi : PolicyIndex → ℝ) (tau : ℝ) (policies : List PolicyIndex) : List ℝ :=
  let weights := policies.map fun π =>
    exp (log (habit π) - (grade π).value / tau - fPi π)
  let total := weights.foldl (· + ·) 0
  weights.map fun weight => weight / total

/-- With an identically zero policy free-energy term, the general carrier is
exactly the existing closed-by-record softmax object. -/
theorem softmaxWithFPi_zero {PolicyIndex : Type*} (exp log : ℝ → ℝ)
    (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → DarkTower.WarMachine.Holes.ExpectedFreeEnergyValue)
    (tau : ℝ) (policies : List PolicyIndex) :
    softmaxWithFPi exp log habit grade (fun _ => 0) tau policies =
      DarkTower.WarMachine.Holes.softmax exp log habit grade tau policies := by
  simp [softmaxWithFPi, DarkTower.WarMachine.Holes.softmax]

end DarkTower.WarMachine.PolicyPosterior
