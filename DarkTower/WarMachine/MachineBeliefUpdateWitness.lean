import DarkTower.WarMachine.MachineBeliefUpdate

/-!
# Reference witnesses for the machine belief update

The dyadic aggregation, annealing, saturation, attribution, and zero-weight
cases are exact. The production categorical examples use weight one, hence
`kappa 1 = 1`; their decimal readback is compared to these rational witnesses
within `1e-12` because Clojure evaluates the same rational operations as
binary doubles.
-/

namespace DarkTower.WarMachine.MachineBeliefUpdateWitness

open DarkTower.WarMachine.MachineBeliefUpdate
open scoped BigOperators

noncomputable def positiveChannels : List ChannelContribution :=
  [⟨1, 2, 1/2⟩, ⟨-1, 1, 1/4⟩]

theorem multichannelReference : multichannelDriver positiveChannels = some (1/4) := by
  norm_num [positiveChannels, multichannelDriver, signedWeightedError]

theorem scaledMultichannelReference :
    multichannelDriver
      (positiveChannels.map fun c => { c with precision := 4 * c.precision }) =
      some (1/4) := by
  norm_num [positiveChannels, multichannelDriver, signedWeightedError]

theorem singleChannelReference :
    singleChannelDriver ⟨1, 2, 1/2⟩ = 1 := by
  norm_num [singleChannelDriver]

theorem scaledSingleChannelReference :
    singleChannelDriver ⟨1, 8, 1/2⟩ = 4 := by
  norm_num [singleChannelDriver]

theorem eventWeightAtZero : eventWeight 1 0 3 = 1/10 := by
  norm_num [eventWeight, baseWeight, annealFactor, abs_of_nonneg]

theorem eventWeightAtOne : eventWeight 1 1 3 = 1/15 := by
  norm_num [eventWeight, baseWeight, annealFactor, abs_of_nonneg]

theorem eventWeightAtTwo : eventWeight 1 2 3 = 1/30 := by
  norm_num [eventWeight, baseWeight, annealFactor, abs_of_nonneg]

theorem saturatedFifty : eventWeight 50 0 3 = 1/10 := by
  norm_num [eventWeight, baseWeight, annealFactor, abs_of_nonneg]

theorem zeroInconsistencyReference :
    attributedWeight (1/10) 2 0 0 .strengthened = 0 := by
  norm_num [attributedWeight, attributionNorm, inconsistency]

noncomputable def strengthenedLikelihood : Fin 7 → ℝ
  | 0 => 20/77 | 1 => 1/8 | 2 => 13/86 | 3 => 10/83
  | 4 => 10/83 | 5 => 10/77 | 6 => 7/77

noncomputable def foreclosedLikelihood : Fin 7 → ℝ
  | 0 => 10/77 | 1 => 7/80 | 2 => 5/43 | 3 => 10/83
  | 4 => 10/83 | 5 => 20/77 | 6 => 10/77

noncomputable def uniformSeven : Fin 7 → ℝ := fun _ => 1/7

noncomputable def rawHealth (q : Fin 7 → ℝ) : ℝ :=
  q 0 + q 1 + (1/2) * q 2 - (1/2) * q 5 - q 6

noncomputable def expectedHealth (q : Fin 7 → ℝ) : ℝ := (rawHealth q + 1) / 2

noncomputable def strengthenedPosterior : Fin 7 → ℝ
  | 0 => 571040/2193329 | 1 => 274813/2193329 | 2 => 332332/2193329
  | 3 => 264880/2193329 | 4 => 264880/2193329 | 5 => 285520/2193329
  | 6 => 199864/2193329

noncomputable def foreclosedPosterior : Fin 7 → ℝ
  | 0 => 2855200/21198491 | 1 => 1923691/21198491
  | 2 => 2556400/21198491 | 3 => 2648800/21198491
  | 4 => 2648800/21198491 | 5 => 5710400/21198491
  | 6 => 2855200/21198491

theorem uniformHealth : expectedHealth uniformSeven = 4/7 := by
  norm_num [expectedHealth, rawHealth, uniformSeven]

theorem strengthenedHealth :
    expectedHealth strengthenedPosterior = 1431362/2193329 := by
  norm_num [expectedHealth, rawHealth, strengthenedPosterior,
    Fin.sum_univ_succ]

theorem foreclosedHealth :
    expectedHealth foreclosedPosterior = 10772591/21198491 := by
  norm_num [expectedHealth, rawHealth, foreclosedPosterior,
    Fin.sum_univ_succ]

theorem updateIsNotSignSymmetric :
    expectedHealth strengthenedPosterior - expectedHealth uniformSeven ≠
      -(expectedHealth foreclosedPosterior - expectedHealth uniformSeven) := by
  rw [strengthenedHealth, foreclosedHealth, uniformHealth]
  norm_num

end DarkTower.WarMachine.MachineBeliefUpdateWitness
