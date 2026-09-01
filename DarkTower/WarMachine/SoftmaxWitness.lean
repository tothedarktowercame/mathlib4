import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.SoftmaxWitness

open Holes

inductive TestPolicy where | lower | higher
  deriving DecidableEq

def habit (_ : TestPolicy) : ℝ := 1

noncomputable def grade : TestPolicy → ExpectedFreeEnergyValue
  | .lower => ⟨0⟩
  | .higher => ⟨Real.log 8 / 3⟩

structure SoftmaxReference where
  temperature : ℝ
  lowerProbability : ℝ
  higherProbability : ℝ

noncomputable def softmaxReference : SoftmaxReference :=
  { temperature := 1 / 3, lowerProbability := 8 / 9, higherProbability := 1 / 9 }

theorem referenceWeights :
    softmax Real.exp Real.log habit grade softmaxReference.temperature
      [.lower, .higher] = [softmaxReference.lowerProbability,
        softmaxReference.higherProbability] := by
  simp [softmaxReference, softmax, habit, grade, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  norm_num

theorem referenceNormalised : (8 / 9 : ℝ) + 1 / 9 = 1 := by norm_num

theorem lowerGradeHasHigherProbability : (8 / 9 : ℝ) > 1 / 9 := by norm_num

end DarkTower.WarMachine.SoftmaxWitness
