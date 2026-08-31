import DarkTower.WarMachine.DirichletConcentrationsWitness

open DarkTower.WarMachine.Holes

-- Must fail: negative values are outside the concentration domain.
def negativeConcentration : DirichletConcentrations := ⟨[1, -1], by norm_num⟩
