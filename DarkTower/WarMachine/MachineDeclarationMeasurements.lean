import DarkTower.WarMachine.MachineTemperature

/-! Exact reference theorem for the retained 2026-09-04 production trace.
Depth and action are deliberately absent: their production inputs were not
retained in replayable form; the paired futon2 finding records the omissions. -/
namespace DarkTower.WarMachine.MachineDeclarationMeasurements

open MachineTemperature

/-- The first retained 2026-09-04 trace row records selection-gain-only,
`selectionGain = 1`, `tauMin = 0.01`, and the exact IEEE-decimal spread
`25.006118387130687`.  That production arm returns exactly one. -/
theorem temperatureTrace20260904Row0 :
    machineTemperature
      ⟨.selectionGainOnly, (1 : ℝ) / 100,
       (25006118387130687 : ℝ) / 1000000000000000, 1, none⟩ = .ok 1 := by
  norm_num [machineTemperature]

end DarkTower.WarMachine.MachineDeclarationMeasurements

#print axioms DarkTower.WarMachine.MachineDeclarationMeasurements.temperatureTrace20260904Row0
