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
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

theorem fairMassesSumToOne :
    ((fair.support ()).map (fair.mass ())).sum = 1 := fair.normalised ()

end DarkTower.WarMachine.PreferenceDistributionWitness
