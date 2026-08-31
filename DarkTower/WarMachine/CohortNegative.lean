import DarkTower.WarMachine.Holes
open DarkTower.WarMachine.Holes
def bad : Cohort String Nat String Unit :=
  ⟨"bad", "epoch", 0, by decide, {()}, [1], by decide⟩
