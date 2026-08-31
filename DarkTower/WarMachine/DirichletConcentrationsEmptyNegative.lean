import DarkTower.WarMachine.DirichletConcentrationsWitness

open DarkTower.WarMachine.Holes

-- Must fail: a Dirichlet distribution has at least one concentration.
def emptyConcentrations : DirichletConcentrations := ⟨[], by simp⟩
