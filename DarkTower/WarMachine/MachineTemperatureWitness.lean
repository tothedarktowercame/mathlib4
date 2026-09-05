import DarkTower.WarMachine.MachineTemperature

namespace DarkTower.WarMachine.MachineTemperatureWitness
open DarkTower.WarMachine.MachineTemperature

/-- Concrete discharge of the gain-one reduction with production `tau-min`
(`futon2:src/futon2/aif/policy.clj:33-45,113-117`). -/
theorem productionFloorGainOne :
    machineTemperature ⟨.spread, 1/100, 3/5, 1, none⟩ = .ok (3/5) ∧
    machineTemperature ⟨.selectionGainOnly, 1/100, 3/5, 1, none⟩ = .ok 1 := by
  exact gainOneReductions (3/5) (1/100) (by norm_num)

/-- A positive β below `tau-min` remains unchanged
(`futon2:src/futon2/aif/policy.clj:118-123`). -/
theorem belowFloorBetaReference :
    machineTemperature ⟨.variationalBetaGamma, 1/100, 3/5, 2,
      some (.finite (1/1000))⟩ = .ok (1/1000) := by
  exact betaIsNotFloored (1/1000) (1/100) (3/5) 2 (by norm_num)

/-- Non-finite β follows the same rejecting arm as a missing β
(`futon2:src/futon2/aif/policy.clj:47-55,135-141`). -/
theorem nonfiniteBetaReference :
    machineTemperature ⟨.variationalBetaGamma, 1/100, 3/5, 2,
      some .nonfinite⟩ = .error .invalidVariationalBeta := rfl

#print axioms productionFloorGainOne
#print axioms belowFloorBetaReference
#print axioms nonfiniteBetaReference

end DarkTower.WarMachine.MachineTemperatureWitness
