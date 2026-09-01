import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.PredictiveOutcomeRiskWitness

open Holes

inductive Policy where | chooseA deriving DecidableEq
inductive Observation where | a | b deriving DecidableEq
def Obs : Vertex → Type := fun _ => Observation
def oa : Outcome Obs := ⟨.evidence, .a⟩
def ob : Outcome Obs := ⟨.evidence, .b⟩

noncomputable def predictive : PredictiveOutcomeKernel Policy Obs where
  support := fun _ => [oa]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

noncomputable def preference : PreferenceDistribution Obs where
  support := fun _ => [oa, ob]
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

theorem positivePreference : ∀ π o, o ∈ predictive.support π → 0 < preference.mass () o := by
  intros; norm_num [preference]

structure RiskReference where
  predictiveMassA : ℝ
  predictiveMassB : ℝ
  preferenceMassA : ℝ
  preferenceMassB : ℝ
  expectedRisk : ℝ

noncomputable def riskReference : RiskReference :=
  { predictiveMassA := 1, predictiveMassB := 0,
    preferenceMassA := 1 / 2, preferenceMassB := 1 / 2,
    expectedRisk := Real.log 2 }

/-- Independent identity: KL of a point mass against a fair binary preference
distribution is `log 2`. -/
theorem pointMassAgainstUniform :
    predictiveOutcomeRisk predictive preference positivePreference .chooseA =
      riskReference.expectedRisk := by
  simp [riskReference, predictiveOutcomeRisk, predictive, preference, oa]

end DarkTower.WarMachine.PredictiveOutcomeRiskWitness
