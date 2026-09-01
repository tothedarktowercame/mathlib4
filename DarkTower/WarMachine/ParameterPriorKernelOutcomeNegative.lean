import DarkTower.WarMachine.ParameterPriorKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.ParameterPriorKernelWitness

inductive Observation where | clear deriving DecidableEq
def Obs : Vertex → Type := fun _ => Observation
def clear : Outcome Obs := ⟨.evidence, .clear⟩

noncomputable def outcomePrediction : PredictiveOutcomeKernel Policy Obs where
  support := fun _ => [clear]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

-- Must fail: Q(o|pi) has outcomes, not model parameters, as its codomain.
/--
error: Type mismatch
  outcomePrediction
has type
  PredictiveOutcomeKernel Policy Obs
but is expected to have type
  ParameterPriorKernel Policy Parameter
-/
#guard_msgs in
def badPrior : ParameterPriorKernel Policy Parameter := outcomePrediction
