import DarkTower.WarMachine.Holes

open DarkTower.WarMachine.Holes

def expectedValue : ExpectedFreeEnergyValue := ⟨1⟩

-- Must fail: equal numeric payloads do not bridge distinct free-energy types.
/--
error: Type mismatch
  expectedValue
has type
  ExpectedFreeEnergyValue
but is expected to have type
  VariationalFreeEnergyValue
-/
#guard_msgs in
def badVariationalValue : VariationalFreeEnergyValue := expectedValue
