import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.PrecisionWitness

open Holes

def precisionTwo : PrecisionMap := fun _ => ⟨2, by norm_num⟩
def precisionOne : PrecisionMap := fun _ => ⟨1, by norm_num⟩

structure PrecisionReference where
  weightedPrecision : ℝ
  weightedError : ℝ
  weightedF : ℝ
  swappedPrecision : ℝ
  swappedError : ℝ
  swappedF : ℝ

def precisionReference : PrecisionReference :=
  { weightedPrecision := 2, weightedError := 1, weightedF := 1,
    swappedPrecision := 1, swappedError := 2, swappedF := 2 }

theorem weightedReference :
    variationalFreeEnergy (fun k => (precisionTwo k).value)
      (fun _ => precisionReference.weightedError) = ⟨precisionReference.weightedF⟩ := by
  norm_num [precisionReference, variationalFreeEnergy, Channel.all, precisionTwo]

theorem swappedReference :
    variationalFreeEnergy (fun k => (precisionOne k).value)
      (fun _ => precisionReference.swappedError) = ⟨precisionReference.swappedF⟩ := by
  norm_num [precisionReference, variationalFreeEnergy, Channel.all, precisionOne]

theorem precisionAndErrorAreNotInterchangeable :
    variationalFreeEnergy (fun k => (precisionTwo k).value) (fun _ => 1) ≠
      variationalFreeEnergy (fun k => (precisionOne k).value) (fun _ => 2) := by
  norm_num [variationalFreeEnergy, Channel.all, precisionTwo, precisionOne]

end DarkTower.WarMachine.PrecisionWitness
