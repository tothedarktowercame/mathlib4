import DarkTower.WarMachine.MachineModelSpec

namespace DarkTower.WarMachine.FloatCarriedRowCorrespondence
open DarkTower.WarMachine.MachineBeliefState
open DarkTower.WarMachine.MachineModelSpec

/-- Exact rational images of the seven retained binary64 values from binding-1.
This represents that one row; it does not verify the runtime reader. -/
def retainedMass : Status → ℚ
  | .spawned => (7589757911525539 : ℚ) / 72057594037927936
  | .refined => (5075107643853621 : ℚ) / 36028797018963968
  | .strengthened => (5627707221685375 : ℚ) / 18014398509481984
  | .addressed => (3442556320081687 : ℚ) / 36028797018963968
  | .falsified => (2683201850079625 : ℚ) / 36028797018963968
  | .foreclosed => (5982758850052747 : ℚ) / 36028797018963968
  | .reopened => (7589757911525539 : ℚ) / 72057594037927936

def retainedRow : FloatCarriedRow Status where
  support := Status.all
  mass := retainedMass
  nonnegative := by intro s; cases s <;> norm_num [retainedMass]
  support_nodup := by simp [Status.all]
  mass_eq_zero_of_not_mem := by intro s h; cases s <;> simp_all [Status.all]
  nearNormalised := by norm_num [Status.all, retainedMass, floatRowBound]

theorem retained_not_exact : (retainedRow.support.map retainedRow.mass).sum ≠ 1 := by
  norm_num [retainedRow, Status.all, retainedMass]

theorem retained_spawned : retainedRow.mass .spawned = (7589757911525539 : ℚ) / 72057594037927936 := rfl
theorem retained_refined : retainedRow.mass .refined = (5075107643853621 : ℚ) / 36028797018963968 := rfl
theorem retained_strengthened : retainedRow.mass .strengthened = (5627707221685375 : ℚ) / 18014398509481984 := rfl
theorem retained_addressed : retainedRow.mass .addressed = (3442556320081687 : ℚ) / 36028797018963968 := rfl
theorem retained_falsified : retainedRow.mass .falsified = (2683201850079625 : ℚ) / 36028797018963968 := rfl
theorem retained_foreclosed : retainedRow.mass .foreclosed = (5982758850052747 : ℚ) / 36028797018963968 := rfl
theorem retained_reopened : retainedRow.mass .reopened = (7589757911525539 : ℚ) / 72057594037927936 := rfl

end DarkTower.WarMachine.FloatCarriedRowCorrespondence
