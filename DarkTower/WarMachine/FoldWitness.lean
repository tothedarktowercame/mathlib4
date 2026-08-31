import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.FoldWitness

open Holes

structure RecordedWiring where
  nodeCount : Nat
  hyperedgeCount : Nat
  terminalCount : Nat

inductive RecordedPolicyHole where | unresolvedShape | unresolvedCoupling | unresolvedGrain

/-- The pinned record has 5 nodes, 5 hyperedges, one terminal, delta -1, and
three explicit policy holes. -/
def recordedFold : Fold RecordedWiring RecordedPolicyHole :=
  ⟨⟨5, 5, 1⟩, some (-1), [.unresolvedShape, .unresolvedCoupling, .unresolvedGrain]⟩

end DarkTower.WarMachine.FoldWitness
