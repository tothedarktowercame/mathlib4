import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.ParameterPosteriorKernelWitness

open Holes

inductive Policy where | inspect | repair deriving DecidableEq
inductive Observation where | clear | blocked deriving DecidableEq
inductive Parameter where | cautious | bold deriving DecidableEq

def Obs : Vertex → Type := fun _ => Observation
def clear : Outcome Obs := ⟨.evidence, .clear⟩
def blocked : Outcome Obs := ⟨.evidence, .blocked⟩

/-- Hand-derived deterministic posterior rows. The total function supplies a
normalized parameter row for every policy/observation pair; this witnesses the
carrier and does not claim that every observation must change the posterior. -/
noncomputable def posterior : ParameterPosteriorKernel Policy Obs Parameter where
  support := fun _ => [.cautious]
  mass := by
    classical
    exact fun s o => if o ∈ [.cautious] then 1 else 0
  nonnegative := by intros; split <;> norm_num
  support_nodup := by intro; simp
  mass_eq_zero_of_not_mem := by intro s o h; simp_all
  normalised := by
    intro s
    classical
    norm_num

theorem observedPolicyRowMass :
    ((posterior.support (.inspect, clear)).map
      (posterior.mass (.inspect, clear))).sum = 1 :=
  posterior.normalised (.inspect, clear)

theorem allPosteriorRowsNormalised (p : Policy) (o : Outcome Obs) :
    ((posterior.support (p, o)).map (posterior.mass (p, o))).sum = 1 :=
  posterior.normalised (p, o)

end DarkTower.WarMachine.ParameterPosteriorKernelWitness
