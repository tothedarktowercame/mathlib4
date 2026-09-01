import DarkTower.WarMachine.Holes

open DarkTower.WarMachine.Holes

def expectedValue : ExpectedFreeEnergyValue := ⟨1⟩

-- Must fail: equal numeric payloads do not bridge distinct free-energy types.
def badVariationalValue : VariationalFreeEnergyValue := expectedValue
