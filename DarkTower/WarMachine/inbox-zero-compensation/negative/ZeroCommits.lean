import DarkTower.WarMachine.InboxZeroCompensationWitness
open DarkTower.WarMachine
open InboxZeroCompensationWitness
-- Deliberately false claim: compiler must reject, not a normal build target.
example : (finish { InboxZeroWitness.cleanInput with repo := "clean" } editAfterSnapshot .restored .compensate).commitIssued = true := by decide
