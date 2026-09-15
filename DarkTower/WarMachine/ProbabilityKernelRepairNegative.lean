import DarkTower.WarMachine.Holes

/-! Rejection controls for finite-support kernels and nonnegative VFE precision.
Each candidate supplies every field. The rejected obligations are the actual
invariants, not missing-field or unrelated conditioning errors. -/
namespace DarkTower.WarMachine.ProbabilityKernelRepairNegative
open DarkTower.WarMachine.Holes

/--
error: unsolved goals
s : Unit
⊢ False
-/
#guard_msgs in
noncomputable def duplicateKernel : ProbabilityKernel Unit Unit where
  support _ := [(), ()]
  mass _ _ := 1/2
  nonnegative _ _ := by norm_num
  normalised _ := by norm_num
  support_nodup := by intro s; simp
  mass_eq_zero_of_not_mem := by intro s o h; cases o; simp_all

/--
error: unsolved goals
case true
s : Unit
h : True
⊢ False
-/
#guard_msgs in
noncomputable def hiddenMassKernel : ProbabilityKernel Unit Bool where
  support _ := [false]
  mass _ b := if b then 100 else 1
  nonnegative _ b := by cases b <;> norm_num
  normalised _ := by norm_num
  support_nodup := by intro; simp
  mass_eq_zero_of_not_mem := by intro s o h; cases o <;> norm_num at *

/--
error: unsolved goals
x✝ : Channel
⊢ False
-/
#guard_msgs in
noncomputable def negativePrecisionCall :=
  variationalFreeEnergy (fun _ => ⟨-2, by norm_num⟩) (fun _ => 1)

end DarkTower.WarMachine.ProbabilityKernelRepairNegative
