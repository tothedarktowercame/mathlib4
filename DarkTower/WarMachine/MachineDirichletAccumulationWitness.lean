import DarkTower.WarMachine.MachineDirichletAccumulation

/-!
# Concrete production values for the R17 recount

Every theorem here is a numeral the Clojure readback transcribes
(`futon2:holes/labs/wm-contract/runs/F8-dirichlet-accumulation/clojure-readback.txt`).
`recountReference` and `bmrThresholdReference` as first delivered were
`f x = f x` and `(-3 : ℝ) = -3`; both are replaced below by statements about
named carriers, since a readback that transcribes its expectation from a
tautology measures nothing.
-/
namespace DarkTower.WarMachine.MachineDirichletAccumulationWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineBeliefState
open DarkTower.WarMachine.MachineDirichletAccumulation

/-- The prior every cell starts at (`futon2:src/futon2/aif/a4a.clj:11-13`). -/
theorem priorReference : a4aPrior = 1 / 10 := rfl

/-- One record: prior plus one increment (`futon2:src/futon2/aif/a4a.clj:78-113`). -/
theorem oneEdgeReference : machineDirichletAccumulation [⟨0, 0⟩] 0 0 = 11 / 10 := by
  norm_num [machineDirichletAccumulation, MachineDirichletAccumulation.matchesCell, a4aPrior, a4aIncrement]

/-- The same record twice: prior plus two increments.  The multiplicity lives in
the CORPUS, not in how many times the function ran
(`futon2:src/futon2/aif/a4a.clj:85-113`). -/
theorem twoEdgesReference :
    machineDirichletAccumulation [⟨0, 0⟩, ⟨0, 0⟩] 0 0 = 21 / 10 := by
  norm_num [machineDirichletAccumulation, MachineDirichletAccumulation.matchesCell, a4aPrior, a4aIncrement]

/-- One record moves one cell of the row and leaves the other at the prior —
`machineAppendMovesNoOtherCell` on concrete coordinates. -/
theorem twoMissionRowReference :
    machineDirichletAccumulation [⟨0, 0⟩] 0 0 = 11 / 10 ∧
    machineDirichletAccumulation [⟨0, 0⟩] 0 1 = 1 / 10 := by
  norm_num [machineDirichletAccumulation, MachineDirichletAccumulation.matchesCell, a4aPrior, a4aIncrement]

/-- THE RECOUNT HAS NO PREVIOUS-`a` INPUT, stated where it is statable: the
recount SHAPE fails the declared contract on the empty tick list, so the value
it returns is fixed by this tick's data alone.  The Clojure side of this — that
`corpus->concentration` returns the same result on the same corpus however often
it has run, and that no public `futon2.aif.a4a` function takes a previous
concentration with new records — is measured, not proved
(`futon2:holes/labs/wm-contract/runs/F8-dirichlet-accumulation/review-independent-probe-2.txt`). -/
theorem recountReference :
    recountShaped (fun _ _ => 1) [] Channel.loopHealth Status.spawned = 0 ∧
    declaredAccumulation (fun _ _ => 1) [] Channel.loopHealth Status.spawned = 1 := by
  constructor <;> simp [recountShaped, declaredAccumulation]

/-- The acceptance threshold the R17 decision uses, read off its own carrier
`Holes.bayesFactorThreshold` (`Holes.lean:6957`), which is a SEPARATE registry
row (`:model-reduction`, `Delta-F`) and is not part of this one.  Production's
`bmr/acceptance-threshold` is `-3.0` (`futon2:src/futon2/aif/bmr.clj:4`). -/
theorem bmrThresholdReference (change : ModelReductionFreeEnergyChange) :
    bayesFactorThreshold change ↔ change.value ≤ -3 := Iff.rfl

#print axioms priorReference
#print axioms oneEdgeReference
#print axioms twoEdgesReference
#print axioms twoMissionRowReference
#print axioms recountReference
#print axioms bmrThresholdReference

end DarkTower.WarMachine.MachineDirichletAccumulationWitness
