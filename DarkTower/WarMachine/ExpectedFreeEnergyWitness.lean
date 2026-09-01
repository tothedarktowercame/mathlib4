import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.ExpectedFreeEnergyWitness

open Holes

inductive TestObservation : Vertex → Type
  | evidenceDatum : TestObservation .evidence

inductive TestPolicy
  | inspect

private def datum : Outcome TestObservation := ⟨.evidence, .evidenceDatum⟩

private def Q : PredictiveOutcomeKernel TestPolicy TestObservation where
  support := fun _ => [datum]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num

private def Cdist : PreferenceDistribution TestObservation where
  support := fun _ => [datum]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num

private theorem positivePreference :
    ∀ π o, o ∈ Q.support π → 0 < Cdist.mass () o := by
  intros
  norm_num [Cdist]

structure EFEReference where
  predictiveMass : ℝ
  preferenceMass : ℝ
  risk : ℝ
  ambiguity : ℝ
  epistemicGain : ℝ
  expectedFreeEnergy : ℝ

def efeReference : EFEReference :=
  { predictiveMass := 1, preferenceMass := 1, risk := 0,
    ambiguity := 2, epistemicGain := -2, expectedFreeEnergy := 2 }

/-- Independently, a one-point predictive and preferred distribution has KL
zero; adding ambiguity 2 therefore gives expected free energy 2. -/
theorem onePointFixture :
    expectedFreeEnergy Q Cdist positivePreference (fun _ => efeReference.ambiguity) .inspect =
      ⟨efeReference.expectedFreeEnergy⟩ := by
  norm_num [efeReference, expectedFreeEnergy, predictiveOutcomeRisk, Q, Cdist]

/-- The same fixture witnesses the decomposition bridge: risk `0` minus
epistemic gain `-2` equals KL `0` plus ambiguity `2`. -/
theorem decompositionFixture :
    G (fun _ : TestPolicy => efeReference.risk) (fun _ => efeReference.epistemicGain) .inspect =
      expectedFreeEnergy Q Cdist positivePreference (fun _ => efeReference.ambiguity) .inspect := by
  norm_num [efeReference, G, expectedFreeEnergy, predictiveOutcomeRisk, Q, Cdist]

end DarkTower.WarMachine.ExpectedFreeEnergyWitness
