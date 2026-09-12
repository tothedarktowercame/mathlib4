import DarkTower.WarMachine.MachineDepth

/-!
# Redirected machinery depth capture witness

This module states only the redirected machinery capture retained at
`futon2:holes/labs/wm-contract/runs/row-15-depth-capture-2026-09-12/capture.edn`
(SHA-256 `a906fdb015633beee344d597b58883143ba62ddcc1cbc63b779c27613c12ca1c`).
It is not a live production-trace claim.
-/
namespace DarkTower.WarMachine.MachineDepthCaptureWitness

open MachineDepth

/-- The machinery test requested three anticipation steps in its configuration. -/
def configuredRequest : Nat := 3

/-- Anticipation was unavailable, recorded as
`:reason :anticipation-events-unavailable`. -/
def anticipationAvailable : Bool := false

/-- Consequently the exact value passed to EFE was `:horizon-steps nil`. -/
def recordedEfeInput : Option Nat := none

/-- The capture's four exact reference facts. -/
theorem machineryCapture20260912Inputs :
    configuredRequest = 3 ∧
    anticipationAvailable = false ∧
    recordedEfeInput = none ∧
    effectiveDepth recordedEfeInput = 1 := by
  decide

/-- At the pinned input, the captured effective depth agrees with the declared
`machineDepth` law: nil selects the single-step path for every G term. -/
theorem machineryCapture20260912MachineDepth :
    (efeDepths : machineDepth) recordedEfeInput = ⟨1, 1, 1, 1⟩ := by
  rfl

end DarkTower.WarMachine.MachineDepthCaptureWitness

#print axioms DarkTower.WarMachine.MachineDepthCaptureWitness.machineryCapture20260912Inputs
#print axioms DarkTower.WarMachine.MachineDepthCaptureWitness.machineryCapture20260912MachineDepth
