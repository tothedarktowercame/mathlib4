import DarkTower.WarMachine.PreferenceDistributionWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.PreferenceDistributionWitness

inductive HiddenState where | one | two

noncomputable def stateConditioned : ProbabilityKernel HiddenState (Outcome Obs) where
  support := fun _ => [good, bad]
  mass := fun _ _ => 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

-- Must fail: preferences are unconditional, not likelihoods indexed by state.
def badPreference : PreferenceDistribution Obs := stateConditioned
