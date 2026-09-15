import DarkTower.WarMachine.ParameterPosteriorKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.ParameterPosteriorKernelWitness

noncomputable def outcomePrediction : PredictiveOutcomeKernel Policy Obs where
  support := fun _ => [clear]
  mass := by
    classical
    exact fun s o => if o ∈ [clear] then 1 else 0
  nonnegative := by intros; split <;> norm_num
  support_nodup := by intro; simp [clear]
  mass_eq_zero_of_not_mem := by intro s o h; simp_all
  normalised := by
    intro s
    classical
    norm_num [clear]

-- Must fail: Q(o|pi) has neither the posterior's domain nor its codomain.
/--
error: Type mismatch
  outcomePrediction
has type
  PredictiveOutcomeKernel Policy Obs
but is expected to have type
  ParameterPosteriorKernel Policy Obs Parameter
-/
#guard_msgs in
def badPosterior : ParameterPosteriorKernel Policy Obs Parameter := outcomePrediction
