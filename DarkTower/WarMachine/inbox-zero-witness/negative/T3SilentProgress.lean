import DarkTower.WarMachine.InboxZeroWitness
open DarkTower.WarMachine.InboxZeroWitness
-- Mutation: an idle committable repository gets neither commit nor blocker.
example : silent.committed = true ∨
    (∃ r, silent.record = some ⟨dirtyInput.repo, .refusal r⟩) := by simp [silent]
