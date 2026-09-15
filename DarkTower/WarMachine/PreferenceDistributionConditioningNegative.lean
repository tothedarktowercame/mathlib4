import DarkTower.WarMachine.PreferenceDistributionWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.PreferenceDistributionWitness

inductive HiddenState where | one | two

noncomputable def stateConditioned : ProbabilityKernel HiddenState (Outcome Obs) where
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

-- Must fail: preferences are unconditional, not likelihoods indexed by state.
/--
error: Type mismatch
  stateConditioned
has type
  ProbabilityKernel HiddenState (Outcome Obs)
but is expected to have type
  PreferenceDistribution Obs
-/
#guard_msgs in
def badPreference : PreferenceDistribution Obs := stateConditioned
