import DarkTower.WarMachine.Holes
open DarkTower.WarMachine.Holes
/--
error: Tactic `decide` proved that the proposition
  0 < 0
is false
-/
#guard_msgs in
def bad : Cohort String Nat String Unit :=
  ⟨"bad", "epoch", 0, by decide, {()}, [], by decide⟩
