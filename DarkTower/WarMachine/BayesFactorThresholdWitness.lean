import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.BayesFactorThresholdWitness

open Holes

structure ThresholdReference where
  threshold : ℝ
  passingChange : ℝ
  failingChange : ℝ

noncomputable def thresholdReference : ThresholdReference :=
  { threshold := -3, passingChange := -7 / 2, failingChange := -2 }

/-- Hand-derived from the declared `ΔF ≤ -3` convention: `-3.5` passes. -/
theorem substantialReductionPasses :
    bayesFactorThreshold ⟨thresholdReference.passingChange⟩ := by
  norm_num [thresholdReference, bayesFactorThreshold]

/-- A reduction with only `-2` nats of evidence does not pass. -/
theorem weakReductionFails :
    ¬ bayesFactorThreshold ⟨thresholdReference.failingChange⟩ := by
  norm_num [thresholdReference, bayesFactorThreshold]

end DarkTower.WarMachine.BayesFactorThresholdWitness
