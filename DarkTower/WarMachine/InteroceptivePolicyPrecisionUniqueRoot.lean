import Mathlib
import DarkTower.WarMachine.InteroceptivePolicyPosteriorFinite

/-!
# A sufficient global positive-root criterion

This proves the `c > 3R/2` argument for the exact canonical finite posterior,
conditional only on its remaining analytic certificate: the expected-G
derivative identities and variance bounds.  It does not assert that production
floats or a bisection trace establish that certificate.
-/
namespace DarkTower.WarMachine.InteroceptivePolicyPrecisionUniqueRoot

open DarkTower.WarMachine.InteroceptivePolicyPosteriorFinite
open DarkTower.WarMachine.InteroceptivePolicyPrecisionPositiveDomain

/-- The exact missing analytic interface. `variancePi` and `variancePi0` are
the variances of the two canonical finite distributions at beta. -/
structure DerivativeCertificate (delta : ℝ → ℝ) (R : ℝ) : Prop where
  atPositive : ∀ beta, 0 < beta → ∃ variancePi variancePi0,
    0 ≤ variancePi0 ∧ variancePi ≤ R ^ 2 / 4 ∧
    HasDerivAt delta ((variancePi - variancePi0) / beta ^ 2) beta

theorem root_localisation {delta : ℝ → ℝ} {R c beta : ℝ}
    (hbound : ∀ b, 0 < b → |delta b| ≤ R)
    (hbeta : 0 < beta) (hroot : PosteriorRoot c delta beta) :
    c - R ≤ beta ∧ beta ≤ c + R := by
  have hb := hbound beta hbeta
  rw [abs_le] at hb
  dsimp [PosteriorRoot] at hroot
  constructor <;> linarith

theorem derivative_lt_one_above_half_range
    {delta : ℝ → ℝ} {R beta : ℝ}
    (hR : 0 ≤ R) (hbeta : R / 2 < beta)
    (cert : DerivativeCertificate delta R) : deriv delta beta < 1 := by
  have hRhalf : 0 ≤ R / 2 := div_nonneg hR (by norm_num)
  have hbpos : 0 < beta := lt_of_le_of_lt hRhalf hbeta
  obtain ⟨vp, v0, hv0, hvp, hd⟩ := cert.atPositive beta hbpos
  rw [hd.deriv]
  have hsquares : R ^ 2 < 4 * beta ^ 2 := by nlinarith
  have hden : 0 < 4 * beta ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hbpos)
  have hratio : R ^ 2 / (4 * beta ^ 2) < 1 := (div_lt_one hden).2 hsquares
  have : (vp - v0) / beta ^ 2 ≤ R ^ 2 / (4 * beta ^ 2) := by
    have hb2 : 0 < beta ^ 2 := sq_pos_of_pos hbpos
    have hv : vp - v0 ≤ R ^ 2 / 4 := by linarith
    calc
      (vp - v0) / beta ^ 2 ≤ (R ^ 2 / 4) / beta ^ 2 :=
        (div_le_div_iff_of_pos_right hb2).2 hv
      _ = R ^ 2 / (4 * beta ^ 2) := by rw [div_div]
  linarith

/-- For the canonical finite `:both` posterior, `c > 3R/2` plus the derivative
certificate gives exactly one positive root. The `R=0` case is included. -/
theorem canonical_unique_positive_root
    {n : ℕ} [Nonempty (Fin n)]
    (habit g fPi : Fin n → ℝ) {lo hi c : ℝ}
    (hhabit : ∀ i, 0 < habit i)
    (hlohi : lo ≤ hi) (hlo : ∀ i, lo ≤ g i) (hhi : ∀ i, g i ≤ hi)
    (hc : 3 * (hi - lo) / 2 < c)
    (cert : DerivativeCertificate (evidenceDelta habit g fPi) (hi - lo)) :
    (∀ i, Real.exp (Real.log (habit i)) = habit i) ∧
      ∃! beta, 0 < beta ∧ PosteriorRoot c (evidenceDelta habit g fPi) beta := by
  constructor
  · exact exp_log_habit hhabit
  let delta := evidenceDelta habit g fPi
  let R := hi - lo
  have hR : 0 ≤ R := sub_nonneg.mpr hlohi
  have hcont : ContinuousOn delta (Set.Ioi 0) :=
    evidenceDelta_continuousOn_positive habit g fPi
  have hbound : ∀ b, 0 < b → |delta b| ≤ R := fun b _ =>
    evidenceDelta_range_bound habit g fPi hlo hhi b
  let f : ℝ → ℝ := fun b => b - delta b
  have hfcont : ContinuousOn f (Set.Ioi (R / 2)) := by
    apply continuousOn_id.sub
    exact hcont.mono (by
      intro b hb
      exact lt_of_le_of_lt (div_nonneg hR (by norm_num)) hb)
  have hfmono : StrictMonoOn f (Set.Ioi (R / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi (R / 2)) hfcont
    intro b hb
    have hb' : R / 2 < b := by simpa using hb
    have hdlt := derivative_lt_one_above_half_range hR hb' cert
    have hbpos : 0 < b :=
      lt_of_le_of_lt (div_nonneg hR (by norm_num)) hb'
    obtain ⟨vp, v0, hv0, hvp, hd⟩ := cert.atPositive b hbpos
    have hfderiv : HasDerivAt f (1 - ((vp - v0) / b ^ 2)) b := by
      exact (hasDerivAt_id b).sub hd
    rw [hfderiv.deriv]
    rw [hd.deriv] at hdlt
    linarith
  let upper := c + R + 1
  have hcpos : 0 < c := by nlinarith
  have huppos : 0 < upper := by dsimp [upper]; nlinarith
  have hfcupper : c < f upper := by
    have hdle : delta upper ≤ R :=
      le_trans (le_abs_self (delta upper)) (hbound upper huppos)
    dsimp [f, upper]
    linarith
  have hlower : 0 < c - R := by nlinarith
  have hlowerf : f (c - R) ≤ c := by
    have hp : 0 < c - R := hlower
    have hneg := (abs_le.mp (hbound (c - R) hp)).1
    dsimp [f]
    linarith
  have hinterval : c - R ≤ upper := by dsimp [upper]; nlinarith
  have hsubset : Set.Icc (c - R) upper ⊆ Set.Ioi 0 := by
    intro b hb
    exact lt_of_lt_of_le hlower hb.1
  obtain ⟨beta, hbetamem, hbetaf⟩ :=
    (intermediate_value_Icc hinterval
      (continuousOn_id.sub (hcont.mono hsubset)))
      ⟨hlowerf, hfcupper.le⟩
  · have hbetapos : 0 < beta := lt_of_lt_of_le hlower hbetamem.1
    have hroot : PosteriorRoot c delta beta := by
      dsimp [f] at hbetaf
      dsimp [PosteriorRoot]
      linarith
    refine ⟨beta, ⟨hbetapos, hroot⟩, ?_⟩
    intro other hother
    have hbloc := root_localisation hbound hbetapos hroot
    have holoc := root_localisation hbound hother.1 hother.2
    have hbhalf : beta ∈ Set.Ioi (R / 2) := by
      have : R / 2 < c - R := by nlinarith
      exact lt_of_lt_of_le this hbloc.1
    have hohalf : other ∈ Set.Ioi (R / 2) := by
      have : R / 2 < c - R := by nlinarith
      exact lt_of_lt_of_le this holoc.1
    symm
    apply hfmono.injOn hbhalf hohalf
    dsimp [f, PosteriorRoot] at hroot hother ⊢
    linarith

#print axioms root_localisation
#print axioms derivative_lt_one_above_half_range
#print axioms canonical_unique_positive_root

end DarkTower.WarMachine.InteroceptivePolicyPrecisionUniqueRoot
