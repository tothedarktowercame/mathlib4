import Mathlib
import DarkTower.WarMachine.PolicyPosterior
import DarkTower.WarMachine.InteroceptivePolicyPrecisionBounded
import DarkTower.WarMachine.InteroceptivePolicyPrecisionPositiveDomain

/-!
# Exact finite `:both` policy posterior for the interoceptive proposal

Policies are occurrence indices `Fin n`; `List.ofFn id` therefore preserves
order and multiplicity even when two occurrences have equal values.
-/
namespace DarkTower.WarMachine.InteroceptivePolicyPosteriorFinite

open scoped BigOperators
open DarkTower.WarMachine

variable {n : ℕ}

noncomputable def gradeOf (g : Fin n → ℝ) (i : Fin n) :
    Holes.ExpectedFreeEnergyValue := ⟨g i⟩

noncomputable def score (habit g fPi : Fin n → ℝ) (beta : ℝ) (i : Fin n) : ℝ :=
  Real.log (habit i) - g i / beta - fPi i

noncomputable def rawWeight (habit g fPi : Fin n → ℝ) (beta : ℝ) (i : Fin n) : ℝ :=
  Real.exp (score habit g fPi beta i)

noncomputable def normalizer (habit g fPi : Fin n → ℝ) (beta : ℝ) : ℝ :=
  ∑ i, rawWeight habit g fPi beta i

noncomputable def weight (habit g fPi : Fin n → ℝ) (beta : ℝ) (i : Fin n) : ℝ :=
  rawWeight habit g fPi beta i / normalizer habit g fPi beta

/-- Exact equality to the frozen canonical list carrier, specialized to
`Real.exp`, `Real.log`, occurrence-index support, and `tau = beta`. -/
theorem canonicalList_eq_ofFn (habit g fPi : Fin n → ℝ) (beta : ℝ) :
    PolicyPosterior.softmaxWithFPi Real.exp Real.log habit (gradeOf g) fPi beta
      (List.ofFn id) = List.ofFn (weight habit g fPi beta) := by
  simp [PolicyPosterior.softmaxWithFPi, gradeOf, weight, rawWeight, score,
    normalizer, List.foldl_eq_foldr, List.sum_ofFn]

theorem normalizer_pos [Nonempty (Fin n)] (habit g fPi : Fin n → ℝ) (beta : ℝ) :
    0 < normalizer habit g fPi beta := by
  exact Finset.sum_pos' (fun i _ => (Real.exp_pos _).le)
    ⟨Classical.choice inferInstance, Finset.mem_univ _ , Real.exp_pos _⟩

theorem weight_nonnegative [Nonempty (Fin n)] (habit g fPi : Fin n → ℝ)
    (beta : ℝ) (i : Fin n) : 0 ≤ weight habit g fPi beta i :=
  div_nonneg (Real.exp_pos _).le (normalizer_pos habit g fPi beta).le

theorem weights_normalised [Nonempty (Fin n)] (habit g fPi : Fin n → ℝ)
    (beta : ℝ) : ∑ i, weight habit g fPi beta i = 1 := by
  rw [show (∑ i, weight habit g fPi beta i) =
      normalizer habit g fPi beta / normalizer habit g fPi beta by
    simp [weight, Finset.sum_div, normalizer]]
  exact div_self (ne_of_gt (normalizer_pos habit g fPi beta))

/-- Ordered support has exactly `n` occurrence indices; equal candidate values
do not merge positions. -/
theorem canonicalList_length (habit g fPi : Fin n → ℝ) (beta : ℝ) :
    (PolicyPosterior.softmaxWithFPi Real.exp Real.log habit (gradeOf g) fPi beta
      (List.ofFn id)).length = n := by
  rw [canonicalList_eq_ofFn]
  simp

theorem score_continuousOn_positive (habit g fPi : Fin n → ℝ) (i : Fin n) :
    ContinuousOn (fun beta => score habit g fPi beta i) (Set.Ioi 0) := by
  exact (continuousOn_const.sub
    (continuousOn_const.div continuousOn_id (fun beta hbeta => ne_of_gt hbeta))).sub
      continuousOn_const

theorem rawWeight_continuousOn_positive (habit g fPi : Fin n → ℝ) (i : Fin n) :
    ContinuousOn (fun beta => rawWeight habit g fPi beta i) (Set.Ioi 0) :=
  Real.continuous_exp.comp_continuousOn (score_continuousOn_positive habit g fPi i)

theorem normalizer_continuousOn_positive (habit g fPi : Fin n → ℝ) :
    ContinuousOn (fun beta => normalizer habit g fPi beta) (Set.Ioi 0) := by
  exact continuousOn_finset_sum _ fun i _ => rawWeight_continuousOn_positive habit g fPi i

theorem weight_continuousOn_positive [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) (i : Fin n) :
    ContinuousOn (fun beta => weight habit g fPi beta i) (Set.Ioi 0) := by
  exact (rawWeight_continuousOn_positive habit g fPi i).div
    (normalizer_continuousOn_positive habit g fPi)
    (fun beta _ => ne_of_gt (normalizer_pos habit g fPi beta))

noncomputable def finiteWeights [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) (beta : ℝ) :
    InteroceptivePolicyPrecisionBounded.FiniteWeights n where
  weight := weight habit g fPi beta
  nonnegative := weight_nonnegative habit g fPi beta
  normalised := weights_normalised habit g fPi beta

/-- `pi` and `pi0` use the same ruled habit term; only `F_pi` is zeroed in
`pi0`. -/
noncomputable def evidenceDelta [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) (beta : ℝ) : ℝ :=
  InteroceptivePolicyPrecisionBounded.expectation (finiteWeights habit g fPi beta) g -
  InteroceptivePolicyPrecisionBounded.expectation
    (finiteWeights habit g (fun _ => 0) beta) g

theorem evidenceDelta_range_bound [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) {lo hi : ℝ}
    (hlo : ∀ i, lo ≤ g i) (hhi : ∀ i, g i ≤ hi) (beta : ℝ) :
    |evidenceDelta habit g fPi beta| ≤ hi - lo := by
  exact InteroceptivePolicyPrecisionBounded.finitePolicyDeltaBound hlo hhi

theorem evidenceDelta_continuousOn_positive [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) :
    ContinuousOn (evidenceDelta habit g fPi) (Set.Ioi 0) := by
  apply ContinuousOn.sub
  · exact continuousOn_finset_sum _ fun i _ =>
      (weight_continuousOn_positive habit g fPi i).mul continuousOn_const
  · exact continuousOn_finset_sum _ fun i _ =>
      (weight_continuousOn_positive habit g (fun _ => 0) i).mul continuousOn_const

#print axioms canonicalList_eq_ofFn
#print axioms normalizer_pos
#print axioms weights_normalised
#print axioms canonicalList_length
#print axioms evidenceDelta_range_bound
#print axioms evidenceDelta_continuousOn_positive

end DarkTower.WarMachine.InteroceptivePolicyPosteriorFinite
