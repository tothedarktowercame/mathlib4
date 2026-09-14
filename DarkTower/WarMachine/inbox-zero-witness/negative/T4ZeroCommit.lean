import DarkTower.WarMachine.InboxZeroWitness
open DarkTower.WarMachine.InboxZeroWitness
-- Mutation: the zero-state cycle emits a commit effect.
example : commitCount [staleCommit] = 0 := by decide
