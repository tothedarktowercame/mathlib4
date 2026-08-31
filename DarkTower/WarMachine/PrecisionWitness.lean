import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.PrecisionWitness

open Holes

def precisionTwo : PrecisionMap := fun _ => ⟨2, by norm_num⟩
def precisionOne : PrecisionMap := fun _ => ⟨1, by norm_num⟩

theorem weightedReference :
    variationalFreeEnergy (fun k => (precisionTwo k).value) (fun _ => 1) = ⟨1⟩ := by
  norm_num [variationalFreeEnergy, Channel.all, precisionTwo]

theorem swappedReference :
    variationalFreeEnergy (fun k => (precisionOne k).value) (fun _ => 2) = ⟨2⟩ := by
  norm_num [variationalFreeEnergy, Channel.all, precisionOne]

theorem precisionAndErrorAreNotInterchangeable :
    variationalFreeEnergy (fun k => (precisionTwo k).value) (fun _ => 1) ≠
      variationalFreeEnergy (fun k => (precisionOne k).value) (fun _ => 2) := by
  norm_num [variationalFreeEnergy, Channel.all, precisionTwo, precisionOne]

end DarkTower.WarMachine.PrecisionWitness
