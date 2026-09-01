import DarkTower.WarMachine.DirichletConcentrationsWitness

open DarkTower.WarMachine.Holes

-- Must fail: a Dirichlet distribution has at least one concentration.
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
def emptyConcentrations : DirichletConcentrations := ⟨[], by simp⟩
