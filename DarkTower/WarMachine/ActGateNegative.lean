import DarkTower.WarMachine.Holes
open DarkTower.WarMachine.Holes
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : actGate none (some (-1)) = .pass := by simp [actGate]
