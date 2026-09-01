import DarkTower.WarMachine.Holes

open DarkTower.WarMachine.Holes

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : (modelUncertaintyBonus [⟨1, by norm_num⟩]).value = 0 := by
  norm_num [modelUncertaintyBonus]
