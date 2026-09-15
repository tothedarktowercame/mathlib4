import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.PredictiveOutcomeKernelWitness

open Holes

inductive Policy where | inspect | repair deriving DecidableEq
inductive Observation where | clear | fixed deriving DecidableEq
def Obs : Vertex → Type := fun _ => Observation
def clear : Outcome Obs := ⟨.evidence, .clear⟩
def fixed : Outcome Obs := ⟨.evidence, .fixed⟩

/-- Hand-derived deterministic predictions: inspect predicts `clear`; repair
predicts `fixed`. Each policy row is a normalized point mass. -/
noncomputable def predictive : PredictiveOutcomeKernel Policy Obs where
  support
    | .inspect => [clear]
    | .repair => [fixed]
  mass := fun p o => match p, o with
    | .inspect, ⟨.evidence, .clear⟩ => 1
    | .repair, ⟨.evidence, .fixed⟩ => 1
    | _, _ => 0
  nonnegative := by intro p o; rcases o with ⟨v, x⟩; cases p <;> cases v <;> cases x <;> norm_num
  support_nodup := by intro p; cases p <;> simp
  mass_eq_zero_of_not_mem := by intro p o h; rcases o with ⟨v, x⟩; cases p <;> cases v <;> cases x <;> simp_all [clear, fixed]
  normalised := by intro p; cases p <;> simp [clear, fixed]

theorem inspectRowMass :
    ((predictive.support .inspect).map (predictive.mass .inspect)).sum = 1 :=
  predictive.normalised .inspect

theorem repairRowMass :
    ((predictive.support .repair).map (predictive.mass .repair)).sum = 1 :=
  predictive.normalised .repair

theorem allPolicyRowsNormalised (p : Policy) :
    ((predictive.support p).map (predictive.mass p)).sum = 1 :=
  predictive.normalised p

end DarkTower.WarMachine.PredictiveOutcomeKernelWitness
