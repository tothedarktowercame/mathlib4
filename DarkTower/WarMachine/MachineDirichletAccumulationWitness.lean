import DarkTower.WarMachine.MachineDirichletAccumulation

namespace DarkTower.WarMachine.MachineDirichletAccumulationWitness
open DarkTower.WarMachine.MachineDirichletAccumulation

/-- Production prior reference (`futon2:src/futon2/aif/a4a.clj:11-13`). -/
theorem priorReference : a4aPrior = 1/10 := rfl

/-- One record gives prior plus one (`futon2:src/futon2/aif/a4a.clj:76-113`). -/
theorem oneEdgeReference : machineDirichletAccumulation [⟨0, 0⟩] 0 0 = 11/10 := by
  norm_num [machineDirichletAccumulation, a4aPrior, a4aIncrement]

/-- Two equal records give prior plus two (`futon2:src/futon2/aif/a4a.clj:76-113`). -/
theorem twoEdgesReference : machineDirichletAccumulation [⟨0, 0⟩, ⟨0, 0⟩] 0 0 = 21/10 := by
  norm_num [machineDirichletAccumulation, a4aPrior, a4aIncrement]

/-- One record changes only one of two mission cells
(`futon2:src/futon2/aif/a4a.clj:76-113`). -/
theorem twoMissionRowReference :
    machineDirichletAccumulation [⟨0, 0⟩] 0 0 = 11/10 ∧
    machineDirichletAccumulation [⟨0, 0⟩] 0 1 = 1/10 := by
  norm_num [machineDirichletAccumulation, a4aPrior, a4aIncrement]

/-- Recounting identical corpus is extensionally identical
(`futon2:src/futon2/aif/a4a.clj:83-113`). -/
theorem recountReference :
    machineRecountWithPreviousIgnored (fun _ _ => 0) [⟨0, 0⟩] =
      machineRecountWithPreviousIgnored (fun _ _ => 99) [⟨0, 0⟩] := rfl

/-- The independent BMR threshold is measured but not part of this carrier
(`futon2:src/futon2/aif/bmr.clj:4`). -/
theorem bmrThresholdReference : (-3 : ℝ) = -3 := rfl

#print axioms priorReference
#print axioms oneEdgeReference
#print axioms twoEdgesReference
#print axioms twoMissionRowReference
#print axioms recountReference
#print axioms bmrThresholdReference

end DarkTower.WarMachine.MachineDirichletAccumulationWitness
