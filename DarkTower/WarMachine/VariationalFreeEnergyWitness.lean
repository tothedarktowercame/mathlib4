import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.VariationalFreeEnergyWitness
open Holes

/-- The Lean object corresponding field-for-field to the independent EDN
reference fixture.  The positive-proof receipt pins this declaration together
with the fixture bytes and the mapping between their fields. -/
structure GaussianReference where
  channelCount : Nat
  precision : ℝ
  predictionError : ℝ
  expectedVariationalF : ℝ

def gaussianReference : GaussianReference :=
  { channelCount := 14
    precision := 2
    predictionError := 1
    expectedVariationalF := 1 }

/-- Independent Gaussian fixture: fourteen identical channels with precision 2
and error 1 have `F = 1/2 * mean(2 * 1^2) = 1`. -/
theorem constantGaussianReference :
    variationalFreeEnergy (fun _ => gaussianReference.precision)
        (fun _ => gaussianReference.predictionError) =
      ⟨gaussianReference.expectedVariationalF⟩ := by
  norm_num [gaussianReference, variationalFreeEnergy, Channel.all]

end DarkTower.WarMachine.VariationalFreeEnergyWitness
