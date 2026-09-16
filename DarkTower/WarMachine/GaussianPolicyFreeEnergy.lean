import DarkTower.WarMachine.Holes
import DarkTower.WarMachine.ChannelFintype
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian policy free energy F_π (registry `:policy-free-energy`, audit A3 §1)

`F_pi := sum_k 1/2 ( ln(2 pi v_k(pi)) + (o_k - mu_k(pi))^2 / v_k(pi) )` — the
Gaussian negative log-likelihood of the observation under policy π's
per-channel predictive mean and variance. This is the F term of Parr et al.
2022 eq. B.9, π = σ(ln E − F − G) (`refs/parr2022.txt:12659–12664`); B.2/B.4
(`:12509–12514`) give F(π) ≥ −ln P(o|π) with equality for an exact
variational posterior, and the Gaussian form below is that bound's value under
a Gaussian predictive likelihood.

Variances are strictly positive by type: a zero-variance channel is outside
the Gaussian likelihood's domain and is not representable here — no tolerance
branch, no floor, no error mode (audit A3 §1 divergence). Channel coverage is
by type: the sum runs over all channels via `Fintype Channel`, never over a
supplied list.
-/

namespace DarkTower.WarMachine.GaussianPolicyFreeEnergy

open DarkTower.WarMachine.Holes


/-- A per-policy Gaussian predictive distribution: a predictive mean and a
strictly positive predictive variance at every channel. -/
structure GaussianPrediction where
  mean : Channel → ℝ
  variance : Channel → ℝ
  variance_pos : ∀ k : Channel, 0 < variance k

/-- The per-channel Gaussian surprisal: 1/2 (ln(2πv_k) + (o_k − μ_k)² / v_k).
The positive-variance branch only. -/
noncomputable def channelSurprisal (p : GaussianPrediction) (o : ObservationVector)
    (k : Channel) : ℝ :=
  (Real.log (2 * Real.pi * p.variance k) + (o.value k - p.mean k) ^ 2 / p.variance k) / 2

/-- `F_π` as the registry's `:formal` line: the sum of the per-channel
Gaussian surprisals over ALL channels, for policy π's predictive. -/
noncomputable def gaussianPolicyFreeEnergy {PolicyIndex : Type*}
    (pred : PolicyIndex → GaussianPrediction) (o : ObservationVector)
    (π : PolicyIndex) : ℝ :=
  ∑ k, channelSurprisal (pred π) o k

/-- The per-channel Gaussian form equals minus the log of Mathlib's
`gaussianPDFReal` density with that mean and variance. -/
theorem negLogGaussianReal (m x v : ℝ) (hv : 0 < v) :
    (Real.log (2 * Real.pi * v) + (x - m) ^ 2 / v) / 2 =
      -Real.log (ProbabilityTheory.gaussianPDFReal m ⟨v, le_of_lt hv⟩ x) := by
  have hc : NNReal.toReal ⟨v, le_of_lt hv⟩ = v := rfl
  have hs : (0 : ℝ) < 2 * Real.pi * v := by positivity
  have hsq : (0 : ℝ) < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.2 hs
  have hlm : Real.log ((Real.sqrt (2 * Real.pi * v))⁻¹ *
      Real.exp (-(x - m) ^ 2 / (2 * v))) =
      Real.log ((Real.sqrt (2 * Real.pi * v))⁻¹) +
        Real.log (Real.exp (-(x - m) ^ 2 / (2 * v))) :=
    Real.log_mul (inv_ne_zero hsq.ne') (Real.exp_pos _).ne'
  rw [ProbabilityTheory.gaussianPDFReal, hc, hlm, Real.log_inv, Real.log_exp,
    Real.log_sqrt hs.le]
  field_simp
  ring

theorem channelSurprisal_eq_neg_log_density (p : GaussianPrediction)
    (o : ObservationVector) (k : Channel) :
    channelSurprisal p o k =
      -Real.log (ProbabilityTheory.gaussianPDFReal (p.mean k)
        ⟨p.variance k, le_of_lt (p.variance_pos k)⟩ (o.value k)) := by
  rw [channelSurprisal,
    negLogGaussianReal (p.mean k) (o.value k) (p.variance k) (p.variance_pos k)]

/-- The per-channel surprisal is at least the exact-match value log(2πv)/2. -/
theorem channelSurprisal_ge_half_log (p : GaussianPrediction)
    (o : ObservationVector) (k : Channel) :
    Real.log (2 * Real.pi * p.variance k) / 2 ≤ channelSurprisal p o k := by
  have h : (0 : ℝ) ≤ (o.value k - p.mean k) ^ 2 / p.variance k :=
    div_nonneg (sq_nonneg _) (p.variance_pos k).le
  unfold channelSurprisal
  linarith

/-- Equality with the exact-match value holds exactly when the residual is
zero at that channel. -/
theorem channelSurprisal_eq_half_log_iff (p : GaussianPrediction)
    (o : ObservationVector) (k : Channel) :
    channelSurprisal p o k = Real.log (2 * Real.pi * p.variance k) / 2 ↔
      o.value k = p.mean k := by
  constructor
  · intro h
    have h0 : (o.value k - p.mean k) ^ 2 / p.variance k = 0 := by
      unfold channelSurprisal at h
      linarith
    have hs : (o.value k - p.mean k) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp h0 with hs' | hs'
      · exact hs'
      · exact absurd hs' (p.variance_pos k).ne'
    have := pow_eq_zero_iff (two_ne_zero) |>.mp hs
    exact sub_eq_zero.mp this
  · intro h
    unfold channelSurprisal
    rw [h, sub_self, zero_pow two_ne_zero, zero_div, add_zero]

/-- `F_π` depends on the observation only through the residual o − μ(π):
two observations with the same residual at every channel score identically. -/
theorem gaussianPolicyFreeEnergy_residual {PolicyIndex : Type*}
    (pred : PolicyIndex → GaussianPrediction) (o₁ o₂ : ObservationVector)
    (π : PolicyIndex)
    (h : ∀ k : Channel, o₁.value k - (pred π).mean k = o₂.value k - (pred π).mean k) :
    gaussianPolicyFreeEnergy pred o₁ π = gaussianPolicyFreeEnergy pred o₂ π := by
  unfold gaussianPolicyFreeEnergy
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold channelSurprisal
  rw [h k]

/-- Fixture replacing the audit counterexample (A3 §1): at a channel with
positive variance, an observation differing from the mean by 1 scores
STRICTLY more than an exact match. No mismatch scores the minimum. -/
theorem channelSurprisal_mismatch_gt_match (p : GaussianPrediction)
    (o₁ o₂ : ObservationVector) (k : Channel)
    (h₁ : o₁.value k = p.mean k) (h₂ : o₂.value k = p.mean k + 1) :
    channelSurprisal p o₁ k < channelSurprisal p o₂ k := by
  have hv : (0 : ℝ) < p.variance k := p.variance_pos k
  have hinv : (0 : ℝ) < 1 / p.variance k := by positivity
  unfold channelSurprisal
  rw [h₁, h₂, sub_self, add_sub_cancel_left, one_pow,
    zero_pow two_ne_zero, zero_div, add_zero]
  linarith

end DarkTower.WarMachine.GaussianPolicyFreeEnergy
