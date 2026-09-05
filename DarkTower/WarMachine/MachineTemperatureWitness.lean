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

/-- `finite-pos?` rejects zero as well as missing and non-finite
(`futon2:src/futon2/aif/policy.clj:47-55`); the delivered module exercised
neither zero nor a negative beta on a concrete value.  Measured at HEAD: both
throw with the same message the `nil` case does
(`runs/F8-temperature/review-independent-probe.txt`, the `variational beta=`
lines). -/
theorem zeroBetaReference :
    machineTemperature ⟨.variationalBetaGamma, 1/100, 3/5, 2,
      some (.finite 0)⟩ = .error .invalidVariationalBeta := by
  norm_num [machineTemperature]

/-- And a strictly negative beta (`futon2:src/futon2/aif/policy.clj:47-55`). -/
theorem negativeBetaReference :
    machineTemperature ⟨.variationalBetaGamma, 1/100, 3/5, 2,
      some (.finite (-1/4))⟩ = .error .invalidVariationalBeta := by
  norm_num [machineTemperature]

/-- The gain floor at production's `tau-min`: a degenerate gain of `0` gives
`100`, not a division by zero (`futon2:src/futon2/aif/policy.clj:132`).
Measured at HEAD: `100.0`
(`runs/F8-temperature/review-independent-probe.txt`, `g=0 :selection-gain-only`). -/
theorem productionGainFloorReference :
    machineTemperature ⟨.selectionGainOnly, 1/100, 3/5, 0, none⟩ = .ok 100 := by
  rw [gainFloorPreventsDivisionByZero (1/100) (3/5) (by norm_num)]
  norm_num

/-- The three laws on production's own defaults, with the numbers the probe
measured: `0.3`, `0.5`, `0.25`.  This is `threeLawsDisagree` discharged rather
than left as a statement about a definition. -/
theorem threeLawsReference :
    machineTemperature (probeOpts .spread) = .ok (3/10) ∧
    machineTemperature (probeOpts .selectionGainOnly) = .ok (1/2) ∧
    machineTemperature (probeOpts .variationalBetaGamma) = .ok (1/4) :=
  ⟨threeLawsDisagree.1, threeLawsDisagree.2.1, threeLawsDisagree.2.2.1⟩

#print axioms zeroBetaReference
#print axioms negativeBetaReference
#print axioms productionGainFloorReference
#print axioms threeLawsReference
#print axioms productionFloorGainOne
#print axioms belowFloorBetaReference
#print axioms nonfiniteBetaReference

end DarkTower.WarMachine.MachineTemperatureWitness
