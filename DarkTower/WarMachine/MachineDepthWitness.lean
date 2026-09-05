import DarkTower.WarMachine.MachineDepth

namespace DarkTower.WarMachine.MachineDepthWitness
open DarkTower.WarMachine.MachineDepth

def incrementStep (state : Nat) (_action : Unit) : Nat := state + 1

theorem depthThreeTrajectory :
    predictMultiHorizon incrementStep 0 () 3 = ([1, 2, 3], 3) := by decide

theorem depthThreeDiffersFromFirst :
    (predictMultiHorizon incrementStep 0 () 3).2 -
      (predictMultiHorizon incrementStep 0 () 3).1.head! = 2 := by decide

theorem efeDepthThreeReference : efeDepths (some 3) = ⟨3, 3, 1, 1⟩ := by decide
theorem nilDepthReference : effectiveDepth none = 1 := rfl
theorem oneDepthReference : effectiveDepth (some 1) = 1 := rfl
theorem forwardDefaultReference : (3 : Nat) = 3 := rfl
theorem rolloutDefaultReference : (2 : Nat) = 2 := rfl

end DarkTower.WarMachine.MachineDepthWitness
