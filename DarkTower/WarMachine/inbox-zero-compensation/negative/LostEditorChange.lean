import DarkTower.WarMachine.InboxZeroCompensationWitness
open DarkTower.WarMachine
open InboxZeroCompensationWitness
-- Deliberately false claim: compiler must reject, not a normal build target.
example : restoredVersion editAfterSnapshot = 10 := by decide
