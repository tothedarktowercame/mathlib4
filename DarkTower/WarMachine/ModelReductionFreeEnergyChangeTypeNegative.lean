import DarkTower.WarMachine.Holes

open DarkTower.WarMachine.Holes

def perTickMismatch : VariationalFreeEnergyValue := ⟨Real.log 2⟩

-- Must fail even with the identical payload: present-tense mismatch is not BMR evidence change.
def badReductionChange : ModelReductionFreeEnergyChange := perTickMismatch
