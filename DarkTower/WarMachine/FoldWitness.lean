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

theorem recordedFoldFields :
    recordedFold.wiring.nodeCount = 5 ∧
    recordedFold.wiring.hyperedgeCount = 5 ∧
    recordedFold.wiring.terminalCount = 1 ∧
    recordedFold.coverageScoreDelta = some (-1) ∧
    recordedFold.policyHoles.length = 3 := by
  norm_num [recordedFold]

end DarkTower.WarMachine.FoldWitness
