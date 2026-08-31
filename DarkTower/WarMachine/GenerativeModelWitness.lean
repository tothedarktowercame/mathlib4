import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.GenerativeModelWitness

open Holes
noncomputable section

inductive TestObservation : Vertex → Type
  | pass : TestObservation .evidence
  | fail : TestObservation .evidence

inductive TestState | ready
inductive OtherState | other
inductive TestAction | run
inductive TestPolicy | inspect

private def passOutcome : Outcome TestObservation := ⟨.evidence, .pass⟩
private def failOutcome : Outcome TestObservation := ⟨.evidence, .fail⟩

private def observation : ProbabilityKernel TestState (Outcome TestObservation) where
  support := fun _ => [passOutcome, failOutcome]
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num

/-- Used only by the executable structural negative control: its state type is
deliberately incompatible with `transition`. -/
private def wrongObservation : ProbabilityKernel OtherState (Outcome TestObservation) where
  support := fun _ => [passOutcome, failOutcome]
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num

private def transition : TransitionKernel TestState TestAction where
  support := fun _ => [.ready]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num

private def policyPrior : PolicyPriorKernel TestPolicy where
  support := fun _ => [.inspect]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num

private def model : GenerativeModel TestObservation TestState TestAction TestPolicy where
  observation := observation
  transition := transition
  policyPrior := policyPrior

/-- Hand calculation: `(1/2) × 1 × 1 = 1/2`. -/
theorem factorFixture :
    generativeFactorMass model .ready .run .ready passOutcome .inspect = 1 / 2 := by
  norm_num [generativeFactorMass, model, observation, transition, policyPrior]

end
end DarkTower.WarMachine.GenerativeModelWitness
