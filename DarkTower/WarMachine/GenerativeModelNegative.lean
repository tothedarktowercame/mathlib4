import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.GenerativeModelNegative

open Holes
noncomputable section

inductive Observation : Vertex → Type
  | pass : Observation .evidence
inductive State | ready
inductive OtherState | other
inductive Action | run
inductive Policy | inspect

private def passOutcome : Outcome Observation := ⟨.evidence, .pass⟩
private def wrongObservation : ProbabilityKernel OtherState (Outcome Observation) where
  support := fun _ => [passOutcome]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num
private def transition : TransitionKernel State Action where
  support := fun _ => [.ready]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num
private def policyPrior : PolicyPriorKernel Policy where
  support := fun _ => [.inspect]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num

/--
error: Type mismatch
  wrongObservation
has type
  ProbabilityKernel OtherState (Outcome Observation)
but is expected to have type
  ProbabilityKernel State (Outcome Observation)
-/
#guard_msgs in
private def miswired : GenerativeModel Observation State Action Policy where
  observation := wrongObservation
  transition := transition
  policyPrior := policyPrior

end
end DarkTower.WarMachine.GenerativeModelNegative
