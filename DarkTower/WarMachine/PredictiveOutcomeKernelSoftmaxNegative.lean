import DarkTower.WarMachine.PredictiveOutcomeKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.PredictiveOutcomeKernelWitness

noncomputable def policyPosterior : List ℝ := [1 / 2, 1 / 2]

-- Must fail: Q(pi), a softmax vector over policies, is not Q(o|pi).
def badPredictive : PredictiveOutcomeKernel Policy Obs := policyPosterior
