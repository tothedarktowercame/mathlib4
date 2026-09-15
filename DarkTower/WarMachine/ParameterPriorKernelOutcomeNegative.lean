import DarkTower.WarMachine.ParameterPriorKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.ParameterPriorKernelWitness

inductive Observation where | clear deriving DecidableEq
def Obs : Vertex → Type := fun _ => Observation
def clear : Outcome Obs := ⟨.evidence, .clear⟩

noncomputable def outcomePrediction : PredictiveOutcomeKernel Policy Obs where
  support := fun _ => [clear]
  mass := by
    classical
    exact fun s o => if o ∈ [clear] then 1 else 0
  nonnegative := by intros; split <;> norm_num
  support_nodup := by intro; simp [clear]
  mass_eq_zero_of_not_mem := by intro s o h; simp_all
  normalised := by
    intro s
    classical
    norm_num [clear]

-- Must fail: Q(o|pi) has outcomes, not model parameters, as its codomain.
/--
error: Type mismatch
  outcomePrediction
has type
  PredictiveOutcomeKernel Policy Obs
but is expected to have type
  ParameterPriorKernel Policy Parameter
-/
#guard_msgs in
def badPrior : ParameterPriorKernel Policy Parameter := outcomePrediction
