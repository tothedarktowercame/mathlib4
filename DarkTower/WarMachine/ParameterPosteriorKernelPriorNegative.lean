import DarkTower.WarMachine.ParameterPosteriorKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.ParameterPosteriorKernelWitness

noncomputable def parameterPrior : ParameterPriorKernel Policy Parameter where
  support := fun _ => [.cautious]
  mass := by
    classical
    exact fun s o => if o ∈ [.cautious] then 1 else 0
  nonnegative := by intros; split <;> norm_num
  support_nodup := by intro; simp
  mass_eq_zero_of_not_mem := by intro s o h; simp_all
  normalised := by
    intro s
    classical
    norm_num

-- Must fail: Q(theta|pi) omits the observed-outcome conditioning coordinate.
/--
error: Type mismatch
  parameterPrior
has type
  ParameterPriorKernel Policy Parameter
but is expected to have type
  ParameterPosteriorKernel Policy Obs Parameter
-/
#guard_msgs in
def badPosterior : ParameterPosteriorKernel Policy Obs Parameter := parameterPrior
