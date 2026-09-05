import DarkTower.WarMachine.MachineAction

namespace DarkTower.WarMachine.MachineActionWitness
open DarkTower.WarMachine.MachineAction

/-- Production readback expectation for the controller-head fixture
(`futon2:src/futon2/aif/policy.clj:567-594`). -/
theorem controllerHeadReference :
    machineAction .strategicRecommendation .controllerHead true false
      [⟨0, 2, false⟩, ⟨1, 1, false⟩] [⟨0, 0, false⟩, ⟨1, 3, false⟩] =
      some ⟨0, 2, false⟩ := by decide

/-- Production readback expectation for full-score selection
(`futon2:src/futon2/aif/policy.clj:567-594`). -/
theorem posteriorReference :
    machineAction .strategicRecommendation .fullScorePosterior true false
      [⟨0, 2, false⟩, ⟨1, 1, false⟩] [⟨0, 0, false⟩, ⟨1, 3, false⟩] =
      some ⟨1, 3, false⟩ := by decide

/-- Production readback expectation for posterior fallback
(`futon2:src/futon2/aif/policy.clj:567-594`). -/
theorem posteriorFallbackReference :
    machineAction .strategicRecommendation .fullScorePosterior false false
      [⟨0, 2, false⟩, ⟨1, 1, false⟩] [⟨0, 0, false⟩, ⟨1, 3, false⟩] =
      some ⟨0, 2, false⟩ := by decide

#print axioms controllerHeadReference
#print axioms posteriorReference
#print axioms posteriorFallbackReference

end DarkTower.WarMachine.MachineActionWitness
