import DarkTower.WarMachine.MachineDirichletAccumulation

namespace DarkTower.WarMachine.MachineAccumulation
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineBeliefState
open DarkTower.WarMachine.MachineDirichletAccumulation

noncomputable def machineAccumulation := declaredAccumulation

theorem machineRealisesDeclaredAccumulation :
    RealisesDeclaredAccumulation machineAccumulation := by
  intro a ticks
  rfl

theorem carriedForwardIdentity (a : Channel → Status → ℝ)
    (tick : (Channel → ℝ) × (Status → ℝ)) (c : Channel) (s : Status) :
    machineAccumulation a [tick] c s = a c s + tick.1 c * tick.2 s := by
  simp [machineAccumulation, declaredAccumulation]

theorem recountImposterRejected :
    ¬ RealisesDeclaredAccumulation recountShaped := recountShapedDoesNotRealise

end DarkTower.WarMachine.MachineAccumulation
