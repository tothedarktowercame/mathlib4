import DarkTower.WarMachine.SensoryPredictionError
import DarkTower.WarMachine.ChannelFintype

/-!
# Belief updating as gradient descent on the Laplace free energy

Row `:belief-update` of `futon2:holes/labs/wm-contract/aif-equations.edn`, per
audit A2 §4. Buckley et al. 2017: under the Laplace approximation, with no
generalised coordinates (order-0 terms of eq. 45 only) and no dynamical-prior
terms, the free energy is `F(μ) = Σ_k ½ [Π_k ε_k² − ln Π_k]` up to a constant,
with `ε_k = o_k − g(μ)_k` (eq. 46). Beliefs descend its gradient
(eqs. 48–50, `refs/buckley2017.txt:1173–1210`; the worked system is eq. 59,
`:1387–1401`). For the identity observation map `−∂F/∂μ_k = Π_k ε_k`, so a
gradient step of size `α` is `μ_k + α Π_k ε_k`: the registry's formal line.
That derivation is proved here, not assumed.
-/

namespace DarkTower.WarMachine.LaplaceBeliefUpdate

open DarkTower.WarMachine.Holes DarkTower.WarMachine.SensoryPredictionError

/-- The identity observation map: the predicted observation is the belief mean. -/
def identityMap (μ : Channel → ℝ) : Channel → ℝ := μ

/-- The order-0 Laplace free energy of Buckley et al. 2017 eq. (45) for the
identity observation map, dropping the additive constant. -/
noncomputable def laplaceFreeEnergy (prec : Channel → ℝ) (o : ObservationVector)
    (μ : Channel → ℝ) : ℝ :=
  ∑ k, (prec k * sensoryPredictionError identityMap o μ k ^ 2 - Real.log (prec k)) / 2

/-- One gradient step of size `α` on `laplaceFreeEnergy`:
`μ_k + α Π_k ε_k` (registry formal `mu <- mu + alpha Pi eps`). -/
def beliefUpdate (α : ℝ) (prec : Channel → ℝ) (o : ObservationVector)
    (μ : Channel → ℝ) : Channel → ℝ :=
  fun k => μ k + α * prec k * sensoryPredictionError identityMap o μ k

theorem sensoryPredictionError_identityMap (o : ObservationVector) (μ : Channel → ℝ)
    (k : Channel) : sensoryPredictionError identityMap o μ k = o.value k - μ k := rfl

/-- Varying the belief at channel `k` alone leaves every other channel's term fixed. -/
theorem laplaceFreeEnergy_update (prec : Channel → ℝ) (o : ObservationVector)
    (μ : Channel → ℝ) (k : Channel) (t : ℝ) :
    laplaceFreeEnergy prec o (Function.update μ k t) =
      (∑ j ∈ Finset.univ.erase k,
          (prec j * (o.value j - μ j) ^ 2 - Real.log (prec j)) / 2)
        + (prec k * (o.value k - t) ^ 2 - Real.log (prec k)) / 2 := by
  unfold laplaceFreeEnergy
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [sensoryPredictionError_identityMap,
      Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · rw [sensoryPredictionError_identityMap, Function.update_self]

/-- The partial derivative of the Laplace free energy in `μ_k` is `−Π_k ε_k`. -/
theorem hasDerivAt_laplaceFreeEnergy (prec : Channel → ℝ) (o : ObservationVector)
    (μ : Channel → ℝ) (k : Channel) :
    HasDerivAt (fun t => laplaceFreeEnergy prec o (Function.update μ k t))
      (-(prec k * sensoryPredictionError identityMap o μ k)) (μ k) := by
  simp only [laplaceFreeEnergy_update]
  have hsub : HasDerivAt (fun t : ℝ => o.value k - t) (-1) (μ k) :=
    (hasDerivAt_id (μ k)).const_sub (o.value k)
  have hterm := (((hsub.pow 2).const_mul (prec k)).sub_const (Real.log (prec k))).div_const 2
  have h := (hasDerivAt_const (μ k) (∑ j ∈ Finset.univ.erase k,
      (prec j * (o.value j - μ j) ^ 2 - Real.log (prec j)) / 2)).add hterm
  refine h.congr_deriv ?_
  rw [sensoryPredictionError_identityMap]
  push_cast
  ring

/-- The update is exactly a gradient-descent step: `μ_k − α ∂F/∂μ_k`. -/
theorem beliefUpdate_is_gradient_step (α : ℝ) (prec : Channel → ℝ) (o : ObservationVector)
    (μ : Channel → ℝ) (k : Channel) :
    beliefUpdate α prec o μ k
      = μ k - α * (-(prec k * sensoryPredictionError identityMap o μ k)) := by
  simp only [beliefUpdate]
  ring

/-- The update is the gradient step on `laplaceFreeEnergy` itself: for any `d`
that is the partial derivative of the free energy in `μ_k`, the update at `k`
is `μ_k − α d`. -/
theorem beliefUpdate_eq_sub_deriv (α : ℝ) (prec : Channel → ℝ) (o : ObservationVector)
    (μ : Channel → ℝ) (k : Channel) {d : ℝ}
    (hd : HasDerivAt (fun t => laplaceFreeEnergy prec o (Function.update μ k t)) d (μ k)) :
    beliefUpdate α prec o μ k = μ k - α * d := by
  rw [hd.unique (hasDerivAt_laplaceFreeEnergy prec o μ k)]
  exact beliefUpdate_is_gradient_step α prec o μ k

/-- After the step each channel's error is scaled by `1 − α Π_k`. -/
theorem error_after_update (α : ℝ) (prec : Channel → ℝ) (o : ObservationVector)
    (μ : Channel → ℝ) (k : Channel) :
    o.value k - beliefUpdate α prec o μ k = (1 - α * prec k) * (o.value k - μ k) := by
  simp only [beliefUpdate, sensoryPredictionError_identityMap]
  ring

/-- A step that does not overshoot (`α Π_k ≤ 1` at every channel) never raises
the free energy. -/
theorem beliefUpdate_decreases_freeEnergy (α : ℝ) (prec : Channel → ℝ)
    (o : ObservationVector) (μ : Channel → ℝ) (hα : 0 < α) (hprec : ∀ k, 0 < prec k)
    (hstep : ∀ k, α * prec k ≤ 1) :
    laplaceFreeEnergy prec o (beliefUpdate α prec o μ) ≤ laplaceFreeEnergy prec o μ := by
  unfold laplaceFreeEnergy
  refine Finset.sum_le_sum fun k _ => ?_
  rw [sensoryPredictionError_identityMap, sensoryPredictionError_identityMap,
    error_after_update]
  have hs0 : 0 ≤ α * prec k := (mul_pos hα (hprec k)).le
  have h1 : (1 - α * prec k) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨by linarith [hstep k], by linarith⟩)
  have h2 : prec k * ((1 - α * prec k) * (o.value k - μ k)) ^ 2
      ≤ prec k * (o.value k - μ k) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg (o.value k - μ k)]) (hprec k).le
  linarith

/-- If some channel has a nonzero error and every step stays below `2`, the
free energy strictly decreases. -/
theorem beliefUpdate_strictly_decreases (α : ℝ) (prec : Channel → ℝ)
    (o : ObservationVector) (μ : Channel → ℝ) (hα : 0 < α) (hprec : ∀ k, 0 < prec k)
    (hstep : ∀ k, α * prec k < 2) (hne : o.value ≠ μ) :
    laplaceFreeEnergy prec o (beliefUpdate α prec o μ) < laplaceFreeEnergy prec o μ := by
  obtain ⟨k₀, hk₀⟩ : ∃ k, o.value k ≠ μ k := by
    by_contra h
    exact hne (funext fun k => not_not.mp fun hk => h ⟨k, hk⟩)
  have hle : ∀ k, (prec k * ((1 - α * prec k) * (o.value k - μ k)) ^ 2
        - Real.log (prec k)) / 2
      ≤ (prec k * (o.value k - μ k) ^ 2 - Real.log (prec k)) / 2 := by
    intro k
    have hs0 : 0 < α * prec k := mul_pos hα (hprec k)
    have h1 : (1 - α * prec k) ^ 2 ≤ 1 := by nlinarith [hstep k]
    have h2 : prec k * ((1 - α * prec k) * (o.value k - μ k)) ^ 2
        ≤ prec k * (o.value k - μ k) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (o.value k - μ k)]) (hprec k).le
    linarith
  unfold laplaceFreeEnergy
  simp only [sensoryPredictionError_identityMap, error_after_update]
  refine Finset.sum_lt_sum (fun k _ => hle k) ⟨k₀, Finset.mem_univ _, ?_⟩
  have hs0 : 0 < α * prec k₀ := mul_pos hα (hprec k₀)
  have h1 : (1 - α * prec k₀) ^ 2 < 1 := by nlinarith [hstep k₀]
  have hx : 0 < (o.value k₀ - μ k₀) ^ 2 := by
    have : o.value k₀ - μ k₀ ≠ 0 := sub_ne_zero.mpr hk₀
    positivity
  have h2 : prec k₀ * ((1 - α * prec k₀) * (o.value k₀ - μ k₀)) ^ 2
      < prec k₀ * (o.value k₀ - μ k₀) ^ 2 := by
    rw [mul_pow]
    exact mul_lt_mul_of_pos_left (by nlinarith) (hprec k₀)
  linarith

/-- The update leaves the belief fixed exactly when it already equals the
observation (given a positive step at every channel). -/
theorem beliefUpdate_fixed_iff (α : ℝ) (prec : Channel → ℝ) (o : ObservationVector)
    (μ : Channel → ℝ) (hα : 0 < α) (hprec : ∀ k, 0 < prec k) :
    beliefUpdate α prec o μ = μ ↔ μ = o.value := by
  constructor
  · intro h
    funext k
    have hk := congrFun h k
    simp only [beliefUpdate, sensoryPredictionError_identityMap] at hk
    have hne : α * prec k ≠ 0 := (mul_pos hα (hprec k)).ne'
    have : α * prec k * (o.value k - μ k) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hne
    · linarith
  · intro h
    funext k
    simp only [beliefUpdate, sensoryPredictionError_identityMap, h, sub_self, mul_zero,
      add_zero]

/-- The audit's numbers: `α = 1/10`, `Π = 2`, `ε = 1` from `μ_k = 1/2` gives `7/10`. -/
theorem audit_fixture (k : Channel) :
    beliefUpdate (1 / 10) (fun _ => 2) ⟨fun _ => 3 / 2⟩ (fun _ => 1 / 2) k = 7 / 10 := by
  simp only [beliefUpdate, sensoryPredictionError_identityMap]
  norm_num

end DarkTower.WarMachine.LaplaceBeliefUpdate
