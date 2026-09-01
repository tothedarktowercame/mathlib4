import DarkTower.WarMachine.Holes

open DarkTower.WarMachine.Holes

noncomputable def perTickMismatch : VariationalFreeEnergyValue := ⟨Real.log 2⟩

-- Must fail even with the identical payload: present-tense mismatch is not BMR evidence change.
/--
error: Type mismatch
  perTickMismatch
has type
  VariationalFreeEnergyValue
but is expected to have type
  ModelReductionFreeEnergyChange
-/
#guard_msgs in
def badReductionChange : ModelReductionFreeEnergyChange := perTickMismatch
