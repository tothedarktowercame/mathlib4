import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.BayesFactorThresholdWitness

open Holes

/-- Hand-derived from the declared `ΔF ≤ -3` convention: `-3.5` passes. -/
theorem substantialReductionPasses :
    bayesFactorThreshold ⟨(-7 / 2 : ℝ)⟩ := by
  norm_num [bayesFactorThreshold]

/-- A reduction with only `-2` nats of evidence does not pass. -/
theorem weakReductionFails :
    ¬ bayesFactorThreshold ⟨(-2 : ℝ)⟩ := by
  norm_num [bayesFactorThreshold]

end DarkTower.WarMachine.BayesFactorThresholdWitness
