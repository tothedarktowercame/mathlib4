import DarkTower.WarMachine.DirichletConcentrationsWitness

open DarkTower.WarMachine.Holes

-- Must fail: zero is outside the strictly positive concentration domain.
def zeroConcentration : DirichletConcentrations := ⟨[1, 0], by norm_num⟩
