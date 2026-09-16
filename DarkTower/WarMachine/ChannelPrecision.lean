import Mathlib

/-!
# Channel precision of Buckley et al. 2017 eq. (84), stated

Row `:precision` of `futon2:holes/labs/wm-contract/aif-equations.edn`, per
audit A2 §3 (`AUDIT-lean-aif-equations-2026-09-16.md`): the registry formal is
`Pi_k := 1 / max(Var(eps_k), eps0)`, citing Buckley et al. 2017 eq. (84),
Λ = 1/σ (`refs/buckley2017.txt:2096–2101`), where σ is taken to be the
centred variance of channel k's prediction errors, floored at `eps0 > 0`.

The audit's finding: the typed producer `machinePrecision` computes a
prior-regularised uncentred squared-error estimate with floor/cap clamping —
a different quantity (twenty errors equal to 10 give 1/10 under the producer,
not the equation's value; twenty zero errors give 21, not 100). This module
binds the row to the equation itself; it does not patch the estimator.
-/

namespace DarkTower.WarMachine.ChannelPrecision

open Finset

variable {n : ℕ}

/-- Sample mean of a nonempty finite error sample: `(1/N) Σ e_i` with
`N = n + 1` the cardinality. -/
noncomputable def errorMean (errors : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i, errors i) / (n + 1)

/-- Centred (population) variance of a nonempty finite error sample:
`(1/N) Σ (e_i − mean)²`. No prior, no window parameter: the window is which
errors the caller passes. -/
noncomputable def errorVariance (errors : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i, (errors i - errorMean errors) ^ 2) / (n + 1)

/-- Registry formal `Pi_k := 1 / max (Var(eps_k), eps0)` — the eq. (84)
precision `Λ = 1/σ` with `σ := max (errorVariance errors) eps0` and
`eps0 > 0`. -/
noncomputable def channelPrecision (eps0 : ℝ) (h0 : 0 < eps0)
    (errors : Fin (n + 1) → ℝ) : ℝ :=
  1 / max (errorVariance errors) eps0

/-- The centred variance is nonnegative. -/
theorem errorVariance_nonneg (errors : Fin (n + 1) → ℝ) : 0 ≤ errorVariance errors :=
  div_nonneg (sum_nonneg fun i _ => sq_nonneg _) (by positivity)

/-- The precision is strictly positive: the floored variance exceeds zero. -/
theorem channelPrecision_pos (eps0 : ℝ) (h0 : 0 < eps0) (errors : Fin (n + 1) → ℝ) :
    0 < channelPrecision eps0 h0 errors :=
  one_div_pos.2 (lt_of_lt_of_le h0 (le_max_right _ _))

/-- The floor caps the precision at `1 / eps0`. -/
theorem channelPrecision_le_inv_eps0 (eps0 : ℝ) (h0 : 0 < eps0)
    (errors : Fin (n + 1) → ℝ) :
    channelPrecision eps0 h0 errors ≤ 1 / eps0 :=
  one_div_le_one_div_of_le h0 (le_max_right _ _)

/-- Buckley et al. 2017 eq. (84): the precision is `Λ = 1/σ` for the floored
variance `σ := max (errorVariance errors) eps0`, which is strictly positive. -/
theorem channelPrecision_eq84 (eps0 : ℝ) (h0 : 0 < eps0) (errors : Fin (n + 1) → ℝ) :
    0 < max (errorVariance errors) eps0 ∧
      channelPrecision eps0 h0 errors = 1 / max (errorVariance errors) eps0 :=
  ⟨lt_of_lt_of_le h0 (le_max_right _ _), rfl⟩

/-- Above the floor the precision is exactly the inverse centred variance. -/
theorem channelPrecision_of_eps0_le (eps0 : ℝ) (h0 : 0 < eps0) (errors : Fin (n + 1) → ℝ)
    (h : eps0 ≤ errorVariance errors) :
    channelPrecision eps0 h0 errors = 1 / errorVariance errors := by
  rw [channelPrecision, max_eq_left h]

/-- A constant error sample has mean equal to the constant. -/
theorem errorMean_const (c : ℝ) : errorMean (fun _ : Fin (n + 1) => c) = c := by
  rw [errorMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [div_eq_iff ((by positivity : (0 : ℝ) < ↑n + 1).ne')]
  push_cast
  ring

/-- A constant error sample has centred variance zero. -/
theorem errorVariance_const (c : ℝ) : errorVariance (fun _ : Fin (n + 1) => c) = 0 := by
  rw [errorVariance, errorMean_const]
  simp

/-- A constant error sample has variance zero and precision exactly the floor
`1 / eps0`. -/
theorem channelPrecision_const (eps0 : ℝ) (h0 : 0 < eps0) (c : ℝ) :
    errorVariance (fun _ : Fin (n + 1) => c) = 0
      ∧ channelPrecision eps0 h0 (fun _ : Fin (n + 1) => c) = 1 / eps0 := by
  refine ⟨errorVariance_const c, ?_⟩
  rw [channelPrecision, errorVariance_const c, max_eq_right h0.le]

/-! ### Audit fixtures (A2 §3)

Twenty errors equal to 10: variance 0, precision `1/eps0 = 100` at
`eps0 = 1/100` (the producer gives `1/10`). Twenty zero errors: precision
`100` (the producer gives `21`). Nonzero variance: `[1, −1]` has variance 1
and precision 1 at any floor below 1. -/

/-- Twenty errors, all equal to `c`. -/
def auditSample (c : ℝ) : Fin (19 + 1) → ℝ := fun _ => c

/-- A twenty-error constant sample has centred variance zero. -/
theorem auditSample_variance (c : ℝ) : errorVariance (auditSample c) = 0 :=
  errorVariance_const c

/-- Twenty errors equal to 10: variance 0. -/
theorem audit_fixture_const10_variance :
    errorVariance (auditSample 10) = 0 := auditSample_variance 10

/-- Twenty errors equal to 10: precision exactly 100 at `eps0 = 1/100`. -/
theorem audit_fixture_const10_precision :
    channelPrecision (1 / 100) (by norm_num) (auditSample 10) = 100 := by
  rw [channelPrecision, auditSample_variance, max_eq_right (by norm_num)]
  norm_num

/-- Twenty zero errors: precision exactly 100 at `eps0 = 1/100`. -/
theorem audit_fixture_zero_errors_precision :
    channelPrecision (1 / 100) (by norm_num) (auditSample 0) = 100 := by
  rw [channelPrecision, auditSample_variance, max_eq_right (by norm_num)]
  norm_num

/-- The two-point sample `[1, −1]`. -/
def twoPointSample : Fin 2 → ℝ := fun i => 1 - 2 * (i : ℝ)

/-- A sample with nonzero variance: `[1, −1]` has mean 0, variance 1. -/
theorem audit_fixture_nonzero_variance :
    errorVariance (n := 1) twoPointSample = 1 := by
  simp [errorVariance, errorMean, twoPointSample, Fin.sum_univ_two]
  norm_num

/-- `[1, −1]` at `eps0 = 1/2` has precision exactly 1. -/
theorem audit_fixture_nonzero_precision :
    channelPrecision (1 / 2) (by norm_num) (n := 1) twoPointSample = 1 := by
  rw [channelPrecision, audit_fixture_nonzero_variance,
    max_eq_left (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  norm_num

end DarkTower.WarMachine.ChannelPrecision
