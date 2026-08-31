import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.SoftmaxWitness

open Holes

inductive TestPolicy where | lower | higher
  deriving DecidableEq

def habit (_ : TestPolicy) : ℝ := 1

noncomputable def grade : TestPolicy → ExpectedFreeEnergyValue
  | .lower => ⟨0⟩
  | .higher => ⟨Real.log 8 / 3⟩

theorem referenceWeights :
    softmax Real.exp Real.log habit grade (1 / 3 : ℝ)
      [.lower, .higher] = [8 / 9, 1 / 9] := by
  simp [softmax, habit, grade, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  norm_num

theorem referenceNormalised : (8 / 9 : ℝ) + 1 / 9 = 1 := by norm_num

theorem lowerGradeHasHigherProbability : (8 / 9 : ℝ) > 1 / 9 := by norm_num

end DarkTower.WarMachine.SoftmaxWitness
