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
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intro p; cases p <;> simp

theorem inspectRowMass :
    ((predictive.support .inspect).map (predictive.mass .inspect)).sum = 1 :=
  predictive.normalised .inspect

theorem repairRowMass :
    ((predictive.support .repair).map (predictive.mass .repair)).sum = 1 :=
  predictive.normalised .repair

end DarkTower.WarMachine.PredictiveOutcomeKernelWitness
