import Mathlib

/-!
# Categorical state prediction error (Parr et al. 2022 eq. 4.13) and its fixed point

Rows `:state-prediction-error` (R3a) and `:state-belief-update` (R3) of
`futon2:holes/labs/wm-contract/aif-equations.edn`, minted under Joe's ruling P9.
Parr, Pezzulo & Friston 2022, eq. 4.13 (`refs/parr2022.txt:3806–3814`), with the
free energy of B.2–B.4 (`:12528–12565`):

  `s_πτ = σ(v_πτ)`, `v̇_πτ = ε_πτ`,
  `ε_πτ = ln A·o_τ + ln B_πτ s_πτ−1 + ln B_πτ+1 · s_πτ+1 − ln s_πτ`.

This is the mean-field form: each dot product is an expectation of a log
(`:12565`), so the past term is `Σ_{s₀} s_{τ−1}(s₀) ln P(x|s₀)` and the future
term `Σ_{s₁} s_{τ+1}(s₁) ln P(s₁|x)`. It is *not* the marginal message passing of
B.6, which takes `½ ln(B s_{τ−1}) + ½ ln(B† s_{τ+1})`; that scheme is not stated
here.

The fixed point of `v̇ = ε` under `s = σ(v)` is reached when `ε` is the same at
every state (it then equals `ln Z`, not `0`); that belief is `σ(v)` with
`v = ln A·o + past + future`. With the previous state observed (a point mass, as
P4's q0 provides) and a uniform future term, it is the exact Bayes posterior
`P(x|o) ∝ P(o|x) P(x|s₀)`. With an uncertain previous state the mean-field fixed
point is generally *not* the exact posterior (`fixture_meanField_not_bayes`).

Logarithms of zero probabilities are `−∞` in the source; Mathlib's `Real.log 0 = 0`
is not, so a zero probability would silently count as probability one. The
definitions below agree with eq. 4.13 only on `LogDefined`: `A(o|x) > 0`, and
`B`, `B_{τ+1}` positive wherever `s_{τ−1}`, `s_{τ+1}` put weight. The theorems that
speak of eq. 4.13 carry that hypothesis. States the source rules out (a `−∞` term)
are not represented here.

The link "`ṡ = 0` under `s = σ(v)` iff `v̇ = ε` is constant across states" is the
argument above, not a formalised dynamic: the theorems characterise the stationary
belief algebraically.
-/

namespace DarkTower.WarMachine.StatePredictionError

variable {S O : Type*} [Fintype S]

/-- The observation term `ln A·o` at state `x` for an observed outcome `o`. -/
noncomputable def likTerm (A : S → O → ℝ) (o : O) (x : S) : ℝ := Real.log (A x o)

/-- The past term `(ln B)·s_{τ−1}` at `x`: `Σ_{s₀} s_{τ−1}(s₀) ln P(x|s₀)`. -/
noncomputable def pastTerm (B : S → S → ℝ) (sPrev : S → ℝ) (x : S) : ℝ :=
  ∑ s₀, sPrev s₀ * Real.log (B s₀ x)

/-- The future term `ln B_{τ+1}·s_{τ+1}` at `x`: `Σ_{s₁} s_{τ+1}(s₁) ln P(s₁|x)`. -/
noncomputable def futureTerm (B' : S → S → ℝ) (sNext : S → ℝ) (x : S) : ℝ :=
  ∑ s₁, sNext s₁ * Real.log (B' x s₁)

/-- `v` at its fixed point: `ln A·o + (ln B)·s_{τ−1} + (ln B')ᵀ·s_{τ+1}`. -/
noncomputable def logMessage (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O)
    (sPrev sNext : S → ℝ) (x : S) : ℝ :=
  likTerm A o x + pastTerm B sPrev x + futureTerm B' sNext x

/-- Eq. 4.13: the state prediction error `ε_πτ` at state `x` for belief `s`. -/
noncomputable def statePredictionError (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O)
    (sPrev sNext s : S → ℝ) (x : S) : ℝ :=
  logMessage A B B' o sPrev sNext x - Real.log (s x)

/-- The domain on which the definitions here are eq. 4.13: every log that carries
weight is the log of a positive probability. -/
def LogDefined (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O) (sPrev sNext : S → ℝ) : Prop :=
  (∀ x, 0 < A x o) ∧ (∀ s₀ x, 0 < sPrev s₀ → 0 < B s₀ x) ∧
    (∀ x s₁, 0 < sNext s₁ → 0 < B' x s₁)

/-- The stationary belief of eq. 4.13: `σ(ln A·o + (ln B)·s_{τ−1} + (ln B')ᵀ·s_{τ+1})`. -/
noncomputable def statePosterior (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O)
    (sPrev sNext : S → ℝ) (x : S) : ℝ :=
  Real.exp (logMessage A B B' o sPrev sNext x) /
    ∑ y, Real.exp (logMessage A B B' o sPrev sNext y)

section

variable (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O) (sPrev sNext : S → ℝ)

theorem partition_pos [Nonempty S] : 0 < ∑ y, Real.exp (logMessage A B B' o sPrev sNext y) :=
  Finset.sum_pos (fun y _ => Real.exp_pos _) Finset.univ_nonempty

theorem statePosterior_pos [Nonempty S] (x : S) : 0 < statePosterior A B B' o sPrev sNext x :=
  div_pos (Real.exp_pos _) (partition_pos A B B' o sPrev sNext)

theorem statePosterior_sum [Nonempty S] : ∑ x, statePosterior A B B' o sPrev sNext x = 1 := by
  simp only [statePosterior, ← Finset.sum_div]
  exact div_self (partition_pos A B B' o sPrev sNext).ne'

/-- **R3: the stationary belief.** On `LogDefined`, for a belief `s` in the open
simplex, the error of eq. 4.13 is the same at every state exactly when `s = σ(v)`.
(The algebra holds for the Lean definitions without `LogDefined`; outside it they
are not eq. 4.13.) -/
theorem error_const_iff_posterior (_hdom : LogDefined A B B' o sPrev sNext)
    (s : S → ℝ) (hs : ∀ x, 0 < s x) (hs1 : ∑ x, s x = 1) :
    (∃ c, ∀ x, statePredictionError A B B' o sPrev sNext s x = c)
      ↔ s = statePosterior A B B' o sPrev sNext := by
  have hne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hs1
  have hZ := partition_pos A B B' o sPrev sNext
  constructor
  · rintro ⟨c, hc⟩
    have hsx : ∀ x, Real.exp (logMessage A B B' o sPrev sNext x) = Real.exp c * s x := fun x => by
      have h := hc x
      rw [statePredictionError, sub_eq_iff_eq_add] at h
      rw [h, Real.exp_add, Real.exp_log (hs x)]
    have hsum : ∑ y, Real.exp (logMessage A B B' o sPrev sNext y) = Real.exp c := by
      simp only [hsx, ← Finset.mul_sum, hs1, mul_one]
    funext x
    rw [statePosterior, hsum, hsx x, mul_div_cancel_left₀ _ (Real.exp_pos c).ne']
  · intro h
    refine ⟨Real.log (∑ y, Real.exp (logMessage A B B' o sPrev sNext y)), fun x => ?_⟩
    rw [statePredictionError, h, statePosterior, Real.log_div (Real.exp_pos _).ne' hZ.ne',
      Real.log_exp]
    ring

/-- On `LogDefined`, at the stationary belief the error is `ln Z` at every state, so
it is `0` only when the unnormalised weights already sum to one. -/
theorem error_at_posterior [Nonempty S] (_hdom : LogDefined A B B' o sPrev sNext) (x : S) :
    statePredictionError A B B' o sPrev sNext (statePosterior A B B' o sPrev sNext) x
      = Real.log (∑ y, Real.exp (logMessage A B B' o sPrev sNext y)) := by
  rw [statePredictionError, statePosterior,
    Real.log_div (Real.exp_pos _).ne' (partition_pos A B B' o sPrev sNext).ne', Real.log_exp]
  ring

end

/-- **One-step exact Bayes with an observed previous state.** If the previous
state is a point mass at `s₀` (P4) and the future term is the same at every state
(e.g. no future evidence yet), then with positive likelihood and transition rows
the fixed point of eq. 4.13 is `P(x|o) ∝ P(o|x) P(x|s₀)`. -/
theorem onestep_bayes_observed [DecidableEq S] (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O)
    (sNext : S → ℝ) (s₀ : S) (hA : ∀ x, 0 < A x o) (hB : ∀ x, 0 < B s₀ x) (k : ℝ)
    (hfut : ∀ x, futureTerm B' sNext x = k) (x : S) :
    statePosterior A B B' o (fun s => if s = s₀ then 1 else 0) sNext x
      = A x o * B s₀ x / ∑ y, A y o * B s₀ y := by
  have hw : ∀ y, Real.exp (logMessage A B B' o (fun s => if s = s₀ then 1 else 0) sNext y)
      = Real.exp k * (A y o * B s₀ y) := fun y => by
    have hp : pastTerm B (fun s => if s = s₀ then 1 else 0) y = Real.log (B s₀ y) := by
      simp [pastTerm]
    rw [logMessage, hp, hfut y, likTerm, Real.exp_add, Real.exp_add, Real.exp_log (hA y),
      Real.exp_log (hB y)]
    ring
  rw [statePosterior, hw x, Finset.sum_congr rfl fun y _ => hw y, ← Finset.mul_sum,
    mul_div_mul_left _ _ (Real.exp_pos k).ne']

/-! ## Fixtures -/

/-- Likelihood `P(o|s)`: correct with probability 9/10. -/
noncomputable def fixtureA : Bool → Bool → ℝ := fun s ob => if s = ob then 9 / 10 else 1 / 10

/-- Transition `P(s'|s)`: stays with probability 9/10. -/
noncomputable def fixtureB : Bool → Bool → ℝ := fun s s' => if s' = s then 9 / 10 else 1 / 10

/-- Uniform belief. -/
noncomputable def fixtureUniform : Bool → ℝ := fun _ => 1 / 2

theorem fixture_futureTerm (x : Bool) :
    futureTerm fixtureB fixtureUniform x = (Real.log (9 / 10) + Real.log (1 / 10)) / 2 := by
  cases x <;> simp [futureTerm, fixtureB, fixtureUniform] <;> ring

/-- Previous state observed `false`, then outcome `true` observed:
posterior on `true` is `(9/10 · 1/10) / (9/10 · 1/10 + 1/10 · 9/10) = 1/2`. -/
theorem fixture_observed_bayes :
    statePosterior fixtureA fixtureB fixtureB true (fun s => if s = false then 1 else 0)
      fixtureUniform true = 1 / 2 := by
  rw [onestep_bayes_observed fixtureA fixtureB fixtureB true fixtureUniform false
    (fun x => by cases x <;> norm_num [fixtureA]) (fun x => by cases x <;> norm_num [fixtureB])
    _ fixture_futureTerm]
  simp [fixtureA, fixtureB]
  norm_num

/-- A transition used for the mean-field control: from `false` stay/leave 1/2,
from `true` go to `false` with 1/4 and stay with 3/4. -/
noncomputable def controlB : Bool → Bool → ℝ := fun s s' =>
  if s = false then 1 / 2 else if s' = false then 1 / 4 else 3 / 4

/-- **Mean-field is not exact Bayes under an uncertain previous state.** With a
uniform previous belief, eq. 4.13's past-term weights satisfy
`(w_true / w_false)² = 3`, whereas the exact predictive prior `B s_{τ−1}` gives
`(5/8 / 3/8)² = 25/9`. This compares the prior-side weights; with any positive
likelihood and a constant future term the posterior ratios differ by the same
factors, so the stationary belief is not the Bayes posterior. -/
theorem fixture_meanField_not_bayes :
    Real.exp (2 * (pastTerm controlB fixtureUniform true - pastTerm controlB fixtureUniform false))
        = 3 ∧
      ((∑ s₀, controlB s₀ true * fixtureUniform s₀) /
          (∑ s₀, controlB s₀ false * fixtureUniform s₀)) ^ 2 = 25 / 9 := by
  constructor
  · have h : 2 * (pastTerm controlB fixtureUniform true - pastTerm controlB fixtureUniform false)
        = Real.log 3 := by
      simp only [pastTerm, controlB, fixtureUniform, Fintype.sum_bool]
      simp only [if_true, Bool.true_eq_false, if_false]
      rw [show Real.log 3 = Real.log (3 / 4) - Real.log (1 / 4) by
        rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num]
      ring
    rw [h, Real.exp_log (by norm_num)]
  · simp [controlB, fixtureUniform, Fintype.sum_bool]
    norm_num

end DarkTower.WarMachine.StatePredictionError
