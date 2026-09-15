import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.PreferenceDistributionWitness

open Holes

inductive Observation where | good | bad deriving DecidableEq
def Obs : Vertex → Type := fun _ => Observation
def good : Outcome Obs := ⟨.evidence, .good⟩
def bad : Outcome Obs := ⟨.evidence, .bad⟩

/-- Hand-derived fair preference over two outcomes: each mass is `1/2`. -/
noncomputable def fair : PreferenceDistribution Obs where
  support := fun _ => [good, bad]
  mass := by
    classical
    exact fun s o => if o ∈ [good, bad] then 1 / 2 else 0
  nonnegative := by intros; split <;> norm_num
  support_nodup := by intro; simp [good, bad]
  mass_eq_zero_of_not_mem := by intro s o h; simp_all
  normalised := by
    intro s
    classical
    norm_num [good, bad]

theorem fairMassesSumToOne :
    ((fair.support ()).map (fair.mass ())).sum = 1 := fair.normalised ()

end DarkTower.WarMachine.PreferenceDistributionWitness
