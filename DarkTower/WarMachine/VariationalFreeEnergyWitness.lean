import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.VariationalFreeEnergyWitness
open Holes

/-- Independent Gaussian fixture: fourteen identical channels with precision 2
and error 1 have `F = 1/2 * mean(2 * 1^2) = 1`. -/
theorem constantGaussianReference :
    variationalFreeEnergy (fun _ => 2) (fun _ => 1) = ⟨1⟩ := by
  norm_num [variationalFreeEnergy, Channel.all]

end DarkTower.WarMachine.VariationalFreeEnergyWitness
