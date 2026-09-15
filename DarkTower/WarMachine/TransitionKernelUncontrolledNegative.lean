import DarkTower.WarMachine.TransitionKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.TransitionKernelWitness

noncomputable def uncontrolled : ProbabilityKernel State State where
  support := fun s => [s]
  mass := by
    classical
    exact fun s o => if o ∈ [s] then 1 else 0
  nonnegative := by intros; split <;> norm_num
  support_nodup := by intro; simp
  mass_eq_zero_of_not_mem := by intro s o h; simp_all
  normalised := by
    intro s
    classical
    norm_num

-- Must fail: B is conditioned jointly on state and action.
/--
error: Type mismatch
  uncontrolled
has type
  ProbabilityKernel State State
but is expected to have type
  TransitionKernel State Action
-/
#guard_msgs in
def badTransition : TransitionKernel State Action := uncontrolled
