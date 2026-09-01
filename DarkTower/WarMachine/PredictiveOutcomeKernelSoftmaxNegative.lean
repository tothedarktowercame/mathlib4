import DarkTower.WarMachine.PredictiveOutcomeKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.PredictiveOutcomeKernelWitness

noncomputable def policyPosterior : List ℝ := [1 / 2, 1 / 2]

-- Must fail: Q(pi), a softmax vector over policies, is not Q(o|pi).
/--
error: Type mismatch
  policyPosterior
has type
  List ℝ
but is expected to have type
  PredictiveOutcomeKernel Policy Obs
-/
#guard_msgs in
def badPredictive : PredictiveOutcomeKernel Policy Obs := policyPosterior
