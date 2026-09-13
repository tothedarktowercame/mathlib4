import Mathlib
import DarkTower.WarMachine.InteroceptivePolicyPrecisionUniqueRoot

/-!
# Exact variance and derivative certificate for the canonical finite posterior

All sums are over occurrence indices, so repeated policy values remain distinct.
-/
namespace DarkTower.WarMachine.InteroceptivePolicyPrecisionVariance

open scoped BigOperators
open DarkTower.WarMachine.InteroceptivePolicyPosteriorFinite
open DarkTower.WarMachine.InteroceptivePolicyPrecisionPositiveDomain
open DarkTower.WarMachine.InteroceptivePolicyPrecisionUniqueRoot

variable {n : ℕ}

noncomputable def expectedG [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) (beta : ℝ) : ℝ :=
  ∑ i, weight habit g fPi beta i * g i

noncomputable def weightedVariance [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) (beta : ℝ) : ℝ :=
  ∑ i, weight habit g fPi beta i *
    (g i - expectedG habit g fPi beta) ^ 2

theorem weightedVariance_nonnegative [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) (beta : ℝ) :
    0 ≤ weightedVariance habit g fPi beta := by
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (weight_nonnegative habit g fPi beta i) (sq_nonneg _)

theorem weightedVariance_eq_secondMoment_sub_sq [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) (beta : ℝ) :
    weightedVariance habit g fPi beta =
      (∑ i, weight habit g fPi beta i * (g i) ^ 2) -
        (expectedG habit g fPi beta) ^ 2 := by
  let m := expectedG habit g fPi beta
  calc
    weightedVariance habit g fPi beta =
        ∑ i, (weight habit g fPi beta i * (g i) ^ 2 -
          2 * m * (weight habit g fPi beta i * g i) +
          m ^ 2 * weight habit g fPi beta i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [m]
      ring
    _ = (∑ i, weight habit g fPi beta i * (g i) ^ 2) - m ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [weights_normalised]
      dsimp [m, expectedG]
      ring

theorem weightedVariance_le_range_sq_div_four [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) (beta : ℝ) {lo hi : ℝ}
    (hlo : ∀ i, lo ≤ g i) (hhi : ∀ i, g i ≤ hi) :
    weightedVariance habit g fPi beta ≤ (hi - lo) ^ 2 / 4 := by
  let w := finiteWeights habit g fPi beta
  let m := expectedG habit g fPi beta
  have hmlo : lo ≤ m := by
    exact InteroceptivePolicyPrecisionBounded.le_expectation (w := w) hlo
  have hmhi : m ≤ hi := by
    exact InteroceptivePolicyPrecisionBounded.expectation_le (w := w) hhi
  have hpoint : ∀ i, (g i) ^ 2 ≤ (lo + hi) * g i - lo * hi := by
    intro i
    have := mul_nonneg (sub_nonneg.mpr (hlo i)) (sub_nonneg.mpr (hhi i))
    nlinarith
  have hsecond :
      (∑ i, weight habit g fPi beta i * (g i) ^ 2) ≤
        (lo + hi) * m - lo * hi := by
    calc
      (∑ i, weight habit g fPi beta i * (g i) ^ 2) ≤
          ∑ i, weight habit g fPi beta i *
            ((lo + hi) * g i - lo * hi) := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hpoint i)
            (weight_nonnegative habit g fPi beta i)
      _ = (lo + hi) * m - lo * hi := by
        calc
          (∑ i, weight habit g fPi beta i *
              ((lo + hi) * g i - lo * hi)) =
              ∑ i, (weight habit g fPi beta i * ((lo + hi) * g i) -
                weight habit g fPi beta i * (lo * hi)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = (lo + hi) * m - lo * hi := by
            rw [Finset.sum_sub_distrib]
            have hfirst :
                (∑ i, weight habit g fPi beta i * ((lo + hi) * g i)) =
                  (lo + hi) * ∑ i, weight habit g fPi beta i * g i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
            have hsecond :
                (∑ i, weight habit g fPi beta i * (lo * hi)) = lo * hi := by
              rw [← Finset.sum_mul, weights_normalised, one_mul]
            rw [hfirst, hsecond]
            dsimp [m, expectedG]
  rw [weightedVariance_eq_secondMoment_sub_sq]
  have hsquare : 0 ≤ (2 * m - (lo + hi)) ^ 2 := sq_nonneg _
  nlinarith

theorem score_hasDerivAt [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) {beta : ℝ} (hbeta : 0 < beta) (i : Fin n) :
    HasDerivAt (fun b => score habit g fPi b i) (g i / beta ^ 2) beta := by
  have hbne : beta ≠ 0 := ne_of_gt hbeta
  have hgdiv : HasDerivAt (fun b : ℝ => g i / b) (-g i / beta ^ 2) beta := by
    convert ((hasDerivAt_id beta).inv hbne).const_mul (g i) using 1
    simp only [id_eq]
    field_simp
  convert (((hasDerivAt_const beta (Real.log (habit i))).sub hgdiv).sub_const
      (fPi i)) using 1
  ring

theorem rawWeight_hasDerivAt [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) {beta : ℝ} (hbeta : 0 < beta) (i : Fin n) :
    HasDerivAt (fun b => rawWeight habit g fPi b i)
      (rawWeight habit g fPi beta i * g i / beta ^ 2) beta := by
  convert (Real.hasDerivAt_exp (score habit g fPi beta i)).comp beta
      (score_hasDerivAt habit g fPi hbeta i) using 1
  rfl

theorem normalizer_hasDerivAt [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) {beta : ℝ} (hbeta : 0 < beta) :
    HasDerivAt (fun b => normalizer habit g fPi b)
      ((∑ i, rawWeight habit g fPi beta i * g i) / beta ^ 2) beta := by
  simpa [normalizer, Finset.sum_div] using
    HasDerivAt.fun_sum fun i _ => rawWeight_hasDerivAt habit g fPi hbeta i

theorem expectedG_eq_raw_div [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) (beta : ℝ) :
    expectedG habit g fPi beta =
      (∑ i, rawWeight habit g fPi beta i * g i) /
        normalizer habit g fPi beta := by
  simp only [expectedG, weight]
  calc
    (∑ x, rawWeight habit g fPi beta x /
        normalizer habit g fPi beta * g x) =
        ∑ x, (rawWeight habit g fPi beta x * g x) /
          normalizer habit g fPi beta := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_div]

theorem secondMoment_eq_raw_div [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) (beta : ℝ) :
    (∑ i, weight habit g fPi beta i * (g i) ^ 2) =
      (∑ i, rawWeight habit g fPi beta i * (g i) ^ 2) /
        normalizer habit g fPi beta := by
  simp only [weight]
  calc
    (∑ x, rawWeight habit g fPi beta x /
        normalizer habit g fPi beta * g x ^ 2) =
        ∑ x, (rawWeight habit g fPi beta x * g x ^ 2) /
          normalizer habit g fPi beta := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_div]

theorem expectedG_hasDerivAt [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) {beta : ℝ} (hbeta : 0 < beta) :
    HasDerivAt (fun b => expectedG habit g fPi b)
      (weightedVariance habit g fPi beta / beta ^ 2) beta := by
  let M : ℝ → ℝ := fun b => ∑ i, rawWeight habit g fPi b i * g i
  have hM : HasDerivAt M
      ((∑ i, rawWeight habit g fPi beta i * (g i) ^ 2) / beta ^ 2) beta := by
    convert HasDerivAt.fun_sum fun i _ =>
      (rawWeight_hasDerivAt habit g fPi hbeta i).mul_const (g i) using 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hZ := normalizer_hasDerivAt habit g fPi hbeta
  have hZne : normalizer habit g fPi beta ≠ 0 :=
    ne_of_gt (normalizer_pos habit g fPi beta)
  rw [show (fun b => expectedG habit g fPi b) =
      fun b => M b / normalizer habit g fPi b by
    funext b
    exact expectedG_eq_raw_div habit g fPi b]
  convert hM.div hZ hZne using 1
  rw [weightedVariance_eq_secondMoment_sub_sq,
    expectedG_eq_raw_div, secondMoment_eq_raw_div]
  dsimp [M]
  field_simp

theorem evidenceDelta_hasDerivAt [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) {beta : ℝ} (hbeta : 0 < beta) :
    HasDerivAt (evidenceDelta habit g fPi)
      ((weightedVariance habit g fPi beta -
        weightedVariance habit g (fun _ => 0) beta) / beta ^ 2) beta := by
  change HasDerivAt
    ((fun b => expectedG habit g fPi b) -
      fun b => expectedG habit g (fun _ => 0) b)
    ((weightedVariance habit g fPi beta -
      weightedVariance habit g (fun _ => 0) beta) / beta ^ 2) beta
  convert (expectedG_hasDerivAt habit g fPi hbeta).sub
      (expectedG_hasDerivAt habit g (fun _ => 0) hbeta) using 1
  ring

theorem canonical_derivativeCertificate [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) {lo hi : ℝ}
    (hlo : ∀ i, lo ≤ g i) (hhi : ∀ i, g i ≤ hi) :
    DerivativeCertificate (evidenceDelta habit g fPi) (hi - lo) := by
  refine ⟨fun beta hbeta => ?_⟩
  exact ⟨weightedVariance habit g fPi beta,
    weightedVariance habit g (fun _ => 0) beta,
    weightedVariance_nonnegative habit g (fun _ => 0) beta,
    weightedVariance_le_range_sq_div_four habit g fPi beta hlo hhi,
    evidenceDelta_hasDerivAt habit g fPi hbeta⟩

theorem canonical_unique_positive_root_discharged
    {n : ℕ} [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) {lo hi c : ℝ}
    (hhabit : ∀ i, 0 < habit i)
    (hlohi : lo ≤ hi) (hlo : ∀ i, lo ≤ g i) (hhi : ∀ i, g i ≤ hi)
    (hc : 3 * (hi - lo) / 2 < c) :
    (∀ i, Real.exp (Real.log (habit i)) = habit i) ∧
      ∃! beta, 0 < beta ∧ PosteriorRoot c (evidenceDelta habit g fPi) beta := by
  exact canonical_unique_positive_root habit g fPi hhabit hlohi hlo hhi hc
    (canonical_derivativeCertificate habit g fPi hlo hhi)

theorem canonical_prior_rate_root_order_discharged
    {n : ℕ} [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) {lo hi c1 c2 b1 : ℝ}
    (hhabit : ∀ i, 0 < habit i)
    (hlohi : lo ≤ hi) (hlo : ∀ i, lo ≤ g i) (hhi : ∀ i, g i ≤ hi)
    (hb1pos : 0 < b1) (hb1root : PosteriorRoot c1
      (evidenceDelta habit g fPi) b1)
    (hrates : c1 < c2) (hc2 : 3 * (hi - lo) / 2 < c2) :
    ∃ b2,
      PosteriorRoot c2 (evidenceDelta habit g fPi) b2 ∧ b1 < b2 ∧
      appliedGamma b2 < appliedGamma b1 ∧
      ∀ ⦃b : ℝ⦄, 0 < b →
        PosteriorRoot c2 (evidenceDelta habit g fPi) b → b = b2 := by
  exact canonical_prior_rate_root_order habit g fPi hhabit hlohi hlo hhi
    hb1pos hb1root hrates hc2 (canonical_derivativeCertificate habit g fPi hlo hhi)

#print axioms weightedVariance_nonnegative
#print axioms weightedVariance_le_range_sq_div_four
#print axioms expectedG_hasDerivAt
#print axioms evidenceDelta_hasDerivAt
#print axioms canonical_derivativeCertificate
#print axioms canonical_unique_positive_root_discharged
#print axioms canonical_prior_rate_root_order_discharged

end DarkTower.WarMachine.InteroceptivePolicyPrecisionVariance
