import DarkTower.WarMachine.InboxZeroWitness
open DarkTower.WarMachine.InboxZeroWitness
-- Mutation: authorize from the dirty observation despite current in-flight state.
example : busyInput.current ≠ .inFlight ∨ staleCommit.committed = false := by decide
