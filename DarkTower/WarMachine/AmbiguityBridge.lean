import DarkTower.WarMachine.Holes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Categorical and Gaussian ambiguity are distinct quantities

`Holes.ambiguity` consumes a predicted-state probability kernel and a
categorical observation kernel.  Production's Gaussian lane consumes a finite
map of per-channel variances.  These are different carrier types, so this
module names both and proves concrete comparison cases; it does not coerce or
relabel either quantity as the other.
-/

namespace DarkTower.WarMachine.AmbiguityBridge

open DarkTower.WarMachine.Holes

noncomputable section

/-- The declared categorical quantity, referenced without restating its body. -/
def categoricalAmbiguity {PolicyIndex State Observation : Type*}
    (predictedState : ProbabilityKernel PolicyIndex State)
    (A : observationKernel State Observation) (policy : PolicyIndex) : ℝ :=
  ambiguity predictedState A policy

/-- Production's variance floor (`futon2:src/futon2/aif/efe.clj:40-78`). -/
def gaussianVarianceFloor : ℝ := 1 / 1000000000

/-- The non-learn-action production ambiguity: SUM, not mean, over every value
in the predicted per-channel variance map,
`1/2 * log (2*pi*e*max(variance,1e-9))` (`efe.clj:40-78,725-730`).  The list is
the map's values because channel names do not enter this formula.  On the
learn-action branch production does not call this quantity: it substitutes the
zone evidence's scalar `:predictive-variance` instead (`efe.clj:725-730`). -/
def gaussianChannelAmbiguity (variances : List ℝ) : ℝ :=
  (variances.map fun variance =>
    (Real.log (2 * Real.pi * Real.exp 1 * max variance gaussianVarianceFloor)) / 2).sum

/-- By-reference projection for the registry's categorical law. -/
theorem categorical_projection {PolicyIndex State Observation : Type*}
    (predictedState : ProbabilityKernel PolicyIndex State)
    (A : observationKernel State Observation) (policy : PolicyIndex) :
    categoricalAmbiguity predictedState A policy = ambiguity predictedState A policy := by
  rfl

private def deterministicPredictedState : ProbabilityKernel Unit Unit where
  support _ := [()]
  mass _ _ := 1
  nonnegative _ _ := by norm_num
  support_nodup := by intro; simp
  mass_eq_zero_of_not_mem := by intro s o h; cases o <;> simp_all
  normalised _ := by norm_num

private def deterministicObservation : observationKernel Unit Unit where
  support _ := [()]
  mass _ _ := 1
  nonnegative _ _ := by norm_num
  support_nodup := by intro; simp
  mass_eq_zero_of_not_mem := by intro s o h; cases o <;> simp_all
  normalised _ := by norm_num

theorem deterministicCategoricalAmbiguity_is_zero :
    categoricalAmbiguity deterministicPredictedState deterministicObservation () = 0 := by
  norm_num [categoricalAmbiguity, ambiguity, observationEntropy,
    deterministicPredictedState, deterministicObservation]

/-- A natural-looking pairing already diverges: a deterministic categorical
observation has entropy zero, while one Gaussian channel with unit variance has
strictly positive differential entropy.  Hence no silent general bridge exists. -/
theorem unitVariance_diverges_from_deterministicCategorical :
    gaussianChannelAmbiguity [1] ≠
      categoricalAmbiguity deterministicPredictedState deterministicObservation () := by
  rw [deterministicCategoricalAmbiguity_is_zero]
  have harg : 1 < 2 * Real.pi * Real.exp 1 := by
    have hp : 3 < Real.pi := Real.pi_gt_three
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    nlinarith [Real.exp_pos 1]
  have hlog : 0 < Real.log (2 * Real.pi * Real.exp 1) := Real.log_pos harg
  have hfloor : gaussianVarianceFloor ≤ (1 : ℝ) := by
    norm_num [gaussianVarianceFloor]
  simp only [gaussianChannelAmbiguity, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, max_eq_left hfloor]
  rw [mul_one]
  exact ne_of_gt (div_pos hlog (by norm_num))

/-- A genuine agreement case exists.  A deterministic categorical row has
zero entropy, and a Gaussian channel at variance `1/(2*pi*e)` has zero
differential entropy.  This isolated equality does not identify the carriers. -/
theorem zeroEntropy_specialCase_agrees :
    gaussianChannelAmbiguity [(1 / (2 * Real.pi * Real.exp 1) : ℝ)] =
      categoricalAmbiguity deterministicPredictedState deterministicObservation () := by
  rw [deterministicCategoricalAmbiguity_is_zero]
  have hp : 0 < Real.pi := Real.pi_pos
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hdenom : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  have hp4 : Real.pi < 4 := Real.pi_lt_four
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hdenom24 : 2 * Real.pi * Real.exp 1 < 24 := by nlinarith
  have hfloor : gaussianVarianceFloor ≤ 1 / (2 * Real.pi * Real.exp 1) := by
    apply (le_div_iff₀ hdenom).2
    norm_num [gaussianVarianceFloor]
    nlinarith
  rw [gaussianChannelAmbiguity]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    max_eq_left hfloor]
  rw [show 2 * Real.pi * Real.exp 1 * (1 / (2 * Real.pi * Real.exp 1)) = 1 by
    field_simp]
  simp

#print axioms categorical_projection
#print axioms deterministicCategoricalAmbiguity_is_zero
#print axioms unitVariance_diverges_from_deterministicCategorical
#print axioms zeroEntropy_specialCase_agrees

end


end DarkTower.WarMachine.AmbiguityBridge
