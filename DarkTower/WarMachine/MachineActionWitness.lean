import DarkTower.WarMachine.MachineAction

namespace DarkTower.WarMachine.MachineActionWitness
open DarkTower.WarMachine.MachineAction

/-! The fixtures below are PRODUCTION's, not abstract: `ranked` carries the
`:controller-score` G in ascending order (`a` 0, `b` 1) and `scored` carries the
selection score `ln E − G/τ − F_π` at τ = 1 with ln E = ⟨0, 3⟩ and F_π = 0, so
`a` 0 and `b` 2. `runs/F8-action/clojure-readback.txt` measures both vectors.
`Candidate.score` therefore means G in `ranked` and the selection score in
`scored`; `machineAction` reads `ranked` only through `head?` and argmaxes only
`scored` (`futon2:src/futon2/aif/policy.clj:567-594`). -/

/-- Production readback expectation for the controller-head fixture
(`futon2:src/futon2/aif/policy.clj:567-594`). -/
theorem controllerHeadReference :
    machineAction .strategicRecommendation .controllerHead true false
      [⟨0, 0, false⟩, ⟨1, 1, false⟩] [⟨0, 0, false⟩, ⟨1, 2, false⟩] =
      some ⟨0, 0, false⟩ := by decide

/-- Production readback expectation for full-score selection
(`futon2:src/futon2/aif/policy.clj:567-594`). -/
theorem posteriorReference :
    machineAction .strategicRecommendation .fullScorePosterior true false
      [⟨0, 0, false⟩, ⟨1, 1, false⟩] [⟨0, 0, false⟩, ⟨1, 2, false⟩] =
      some ⟨1, 2, false⟩ := by decide

/-- Production readback expectation for posterior fallback
(`futon2:src/futon2/aif/policy.clj:567-594`). -/
theorem posteriorFallbackReference :
    machineAction .strategicRecommendation .fullScorePosterior false false
      [⟨0, 0, false⟩, ⟨1, 1, false⟩] [⟨0, 0, false⟩, ⟨1, 2, false⟩] =
      some ⟨0, 0, false⟩ := by decide

/-- The score vector the readback measures IS the one these fixtures name:
`selectionScore` at G = ⟨0, 1⟩, ln E = ⟨0, 3⟩, F_π = 0, τ = 1
(`futon2:src/futon2/aif/policy.clj:157-212`). -/
theorem scoreVectorReference :
    selectionScore 0 0 0 1 = 0 ∧ selectionScore 1 3 0 1 = 2 := by
  constructor <;> norm_num [selectionScore]

#print axioms scoreVectorReference
#print axioms controllerHeadReference
#print axioms posteriorReference
#print axioms posteriorFallbackReference

end DarkTower.WarMachine.MachineActionWitness
