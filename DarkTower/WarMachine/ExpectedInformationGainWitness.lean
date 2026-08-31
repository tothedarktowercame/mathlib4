import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.ExpectedInformationGainWitness

open Holes
noncomputable section

inductive TestObservation : Vertex → Type
  | datum : TestObservation .evidence

inductive TestPolicy
  | inspect

inductive Parameter
  | a | b

private def outcome : Outcome TestObservation := ⟨.evidence, .datum⟩

private def Q : PredictiveOutcomeKernel TestPolicy TestObservation where
  support := fun _ => [outcome]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num

private def prior : ParameterPriorKernel TestPolicy Parameter where
  support := fun _ => [.a, .b]
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num

private def posterior : ParameterPosteriorKernel TestPolicy TestObservation Parameter where
  support := fun _ => [.a]
  mass := fun _ θ => match θ with | .a => 1 | .b => 0
  nonnegative := by
    intro _ θ
    cases θ <;> norm_num
  normalised := by intros; norm_num

private theorem positivePrior :
    ∀ π o θ, θ ∈ posterior.support (π, o) → 0 < prior.mass π θ := by
  intros
  norm_num [prior]

/-- A point posterior against the uniform two-parameter prior has KL `log 2`;
the single predicted outcome has mass one, so its expectation is also `log 2`. -/
theorem binaryFixture :
    expectedInformationGain Q prior posterior positivePrior .inspect =
      ⟨Real.log 2⟩ := by
  norm_num [expectedInformationGain, parameterInformationGain, Q, prior, posterior]

end
end DarkTower.WarMachine.ExpectedInformationGainWitness
