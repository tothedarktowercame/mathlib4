import DarkTower.WarMachine.InboxZeroWitness
open DarkTower.WarMachine.InboxZeroWitness
-- Mutation: create a fresh flag from a clean state without an observation.
example : flag newDirt.state ≤ flag cleanInput.current := by decide
