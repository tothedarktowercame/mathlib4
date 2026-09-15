import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.ObservationKernelWitness

open Holes

inductive State where | latent deriving DecidableEq
inductive Observation where | present | absent deriving DecidableEq

/-- Record-derived fair binary observation row. -/
noncomputable def reference : observationKernel State Observation where
  support := fun _ => [.present, .absent]
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  support_nodup := by intro; simp
  mass_eq_zero_of_not_mem := by intro s o h; cases o <;> simp_all
  normalised := by intro; norm_num

theorem referenceRowMass : observationKernelRowMass reference .latent = 1 := by
  norm_num [observationKernelRowMass, reference]

end DarkTower.WarMachine.ObservationKernelWitness
