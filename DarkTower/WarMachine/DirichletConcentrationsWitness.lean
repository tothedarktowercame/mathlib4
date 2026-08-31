import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.DirichletConcentrationsWitness

open Holes

/-- `[2,1]` is a nonempty, strictly positive concentration vector. -/
def alpha21 : DirichletConcentrations := ⟨[2, 1], by simp⟩

theorem recordedValues : alpha21.val = [2, 1] := rfl

end DarkTower.WarMachine.DirichletConcentrationsWitness
