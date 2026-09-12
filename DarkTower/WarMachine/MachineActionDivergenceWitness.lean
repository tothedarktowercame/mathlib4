import DarkTower.WarMachine.MachineAction

namespace DarkTower.WarMachine.MachineActionDivergenceWitness

open DarkTower.WarMachine.MachineAction

/-- The controller-head candidate retained at rank 1 in the pinned schema-27
production record. Its integer score is irrelevant to the head branch. -/
def pinnedControllerHead : Candidate := ⟨1, 0, false⟩

/-- The action actually selected by the reason-bearing live selector in the
pinned record, retained there as chosen rank 139. -/
def pinnedLiveSelected : Candidate := ⟨139, 0, false⟩

/-- `machineAction`'s strategic controller-head branch returns the first
non-no-op candidate. At the pinned record that candidate has rank/id 1,
independently of the remaining 147 candidates and their scores. -/
theorem controllerHeadAtPinnedRecord (tail scored : List Candidate) :
    machineAction .strategicRecommendation .controllerHead false false
      (pinnedControllerHead :: tail) scored = some pinnedControllerHead := by
  simp [machineAction, strategicCandidates, pinnedControllerHead]

/-- The retained live selection is rank 139, hence it is not the rank-1 output
of `machineAction`'s controller-head branch. This refutes correspondence at
this record only; it does not refute the internal branch itself. -/
theorem liveSelectorDivergesFromMachineActionControllerHead
    (tail scored : List Candidate) :
    machineAction .strategicRecommendation .controllerHead false false
        (pinnedControllerHead :: tail) scored = some pinnedControllerHead ∧
      some pinnedLiveSelected ≠ some pinnedControllerHead := by
  constructor
  · exact controllerHeadAtPinnedRecord tail scored
  · decide

end DarkTower.WarMachine.MachineActionDivergenceWitness

#print axioms DarkTower.WarMachine.MachineActionDivergenceWitness.controllerHeadAtPinnedRecord
#print axioms DarkTower.WarMachine.MachineActionDivergenceWitness.liveSelectorDivergesFromMachineActionControllerHead
