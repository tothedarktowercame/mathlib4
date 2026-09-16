import Mathlib

/-!
# Categorical state prediction error and its fixed point

Rows `:state-prediction-error` (R3a) and `:state-belief-update` (R3) of
`futon2:holes/labs/wm-contract/aif-equations.edn`, minted under Joe's ruling P9.
Parr, Pezzulo & Friston 2022, eq. 4.13 (`refs/parr2022.txt:3806–3814`) and
B.5–B.6 (`:12586–12622`):

  `s_πτ = σ(v_πτ)`, `v̇_πτ = ε_πτ`,
  `ε_πτ = ln A·o_τ + ln B_πτ s_πτ−1 + ln B†_πτ+1 s_πτ+1 − ln s_πτ`.

The three terms are messages from the observation, the past and the future.
`B† ∝ Bᵀ`; normalising the future message scales every state's message by the
same factor, which the softmax removes, so `Bᵀ` is used directly. The belief
update (R3) is the fixed point `ε = const`, i.e. `s = σ(v)`, which is the
normalised product of the three messages.
-/

namespace DarkTower.WarMachine.StatePredictionError

variable {S O : Type*} [Fintype S] [Fintype O]

/-- The observation message `A·o` at state `x`: `P(o|x)`. -/
def likMsg (A : S → O → ℝ) (o : O) (x : S) : ℝ := A x o

/-- The past message `B s_prev` at `x`: `Σ_{s₀} P(x|s₀) s_prev(s₀)`. -/
def pastMsg (B : S → S → ℝ) (sPrev : S → ℝ) (x : S) : ℝ := ∑ s₀, B s₀ x * sPrev s₀

/-- The future message `Bᵀ s_next` at `x`: `Σ_{s₁} P(s₁|x) s_next(s₁)`. -/
def futureMsg (B' : S → S → ℝ) (sNext : S → ℝ) (x : S) : ℝ := ∑ s₁, B' x s₁ * sNext s₁

/-- The product of the three messages. -/
def message (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O) (sPrev sNext : S → ℝ) (x : S) : ℝ :=
  likMsg A o x * pastMsg B sPrev x * futureMsg B' sNext x

/-- `v_πτ = ln A·o + ln B s_prev + ln B† s_next` (eq. 4.13 without `− ln s`). -/
noncomputable def logMessage (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O)
    (sPrev sNext : S → ℝ) (x : S) : ℝ :=
  Real.log (likMsg A o x) + Real.log (pastMsg B sPrev x) + Real.log (futureMsg B' sNext x)

/-- Eq. 4.13: the state prediction error `ε_πτ` at state `x` for belief `s`. -/
noncomputable def statePredictionError (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O)
    (sPrev sNext s : S → ℝ) (x : S) : ℝ :=
  logMessage A B B' o sPrev sNext x - Real.log (s x)

/-- The fixed point of eq. 4.13: the normalised message product. -/
noncomputable def statePosterior (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O)
    (sPrev sNext : S → ℝ) (x : S) : ℝ :=
  message A B B' o sPrev sNext x / ∑ y, message A B B' o sPrev sNext y

section

variable (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O) (sPrev sNext : S → ℝ)

theorem statePosterior_nonneg (hmsg : ∀ x, 0 ≤ message A B B' o sPrev sNext x) (x : S) :
    0 ≤ statePosterior A B B' o sPrev sNext x :=
  div_nonneg (hmsg x) (Finset.sum_nonneg fun y _ => hmsg y)

theorem statePosterior_sum (hZ : 0 < ∑ y, message A B B' o sPrev sNext y) :
    ∑ x, statePosterior A B B' o sPrev sNext x = 1 := by
  simp only [statePosterior, ← Finset.sum_div]
  exact div_self hZ.ne'

/-- When every message is positive, `ε = ln(message) − ln s`. -/
theorem logMessage_eq_log_message (x : S) (hl : 0 < likMsg A o x)
    (hp : 0 < pastMsg B sPrev x) (hf : 0 < futureMsg B' sNext x) :
    logMessage A B B' o sPrev sNext x = Real.log (message A B B' o sPrev sNext x) := by
  rw [logMessage, message, Real.log_mul (mul_pos hl hp).ne' hf.ne',
    Real.log_mul hl.ne' hp.ne']

/-- `s = σ(v)`: with positive messages, the posterior is the softmax of `v`. -/
theorem softmax_log_message (hl : ∀ x, 0 < likMsg A o x) (hp : ∀ x, 0 < pastMsg B sPrev x)
    (hf : ∀ x, 0 < futureMsg B' sNext x) :
    statePosterior A B B' o sPrev sNext = fun x =>
      Real.exp (logMessage A B B' o sPrev sNext x) /
        ∑ y, Real.exp (logMessage A B B' o sPrev sNext y) := by
  have hexp : ∀ x, Real.exp (logMessage A B B' o sPrev sNext x)
      = message A B B' o sPrev sNext x := fun x => by
    rw [logMessage_eq_log_message A B B' o sPrev sNext x (hl x) (hp x) (hf x),
      Real.exp_log (show 0 < message A B B' o sPrev sNext x from
        mul_pos (mul_pos (hl x) (hp x)) (hf x))]
  funext x
  simp only [hexp, statePosterior]

/-- **R3: the belief update is the fixed point of eq. 4.13.** For a positive
distribution `s` and positive messages, the error is the same at every state
(`ε = 0` up to the constant the softmax removes) exactly when `s` is the
normalised message product. -/
theorem error_const_iff_posterior (hl : ∀ x, 0 < likMsg A o x)
    (hp : ∀ x, 0 < pastMsg B sPrev x) (hf : ∀ x, 0 < futureMsg B' sNext x)
    (s : S → ℝ) (hs : ∀ x, 0 < s x) (hs1 : ∑ x, s x = 1) :
    (∃ c, ∀ x, statePredictionError A B B' o sPrev sNext s x = c)
      ↔ s = statePosterior A B B' o sPrev sNext := by
  have hm : ∀ x, 0 < message A B B' o sPrev sNext x :=
    fun x => mul_pos (mul_pos (hl x) (hp x)) (hf x)
  have herr : ∀ x, statePredictionError A B B' o sPrev sNext s x
      = Real.log (message A B B' o sPrev sNext x) - Real.log (s x) := fun x => by
    rw [statePredictionError, logMessage_eq_log_message A B B' o sPrev sNext x (hl x) (hp x)
      (hf x)]
  have hne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hs1
  have hZ : 0 < ∑ y, message A B B' o sPrev sNext y :=
    Finset.sum_pos (fun y _ => hm y) ⟨Classical.arbitrary S, Finset.mem_univ _⟩
  constructor
  · rintro ⟨c, hc⟩
    have hmx : ∀ x, message A B B' o sPrev sNext x = Real.exp c * s x := fun x => by
      have h := hc x
      rw [herr x, sub_eq_iff_eq_add, ← Real.exp_eq_exp, Real.exp_log (hm x),
        Real.exp_add, Real.exp_log (hs x)] at h
      exact h
    have hsum : ∑ y, message A B B' o sPrev sNext y = Real.exp c := by
      simp only [hmx, ← Finset.mul_sum, hs1, mul_one]
    funext x
    rw [statePosterior, hsum, hmx x, mul_div_cancel_left₀ _ (Real.exp_pos c).ne']
  · intro h
    refine ⟨Real.log (∑ y, message A B B' o sPrev sNext y), fun x => ?_⟩
    rw [herr x, h, statePosterior, Real.log_div (hm x).ne' hZ.ne']
    ring

/-- With a normalised message product, `ε = 0` everywhere exactly when the
belief equals the messages. -/
theorem error_zero_iff (hl : ∀ x, 0 < likMsg A o x)
    (hp : ∀ x, 0 < pastMsg B sPrev x) (hf : ∀ x, 0 < futureMsg B' sNext x)
    (s : S → ℝ) (hs : ∀ x, 0 < s x) :
    (∀ x, statePredictionError A B B' o sPrev sNext s x = 0)
      ↔ s = message A B B' o sPrev sNext := by
  have hm : ∀ x, 0 < message A B B' o sPrev sNext x :=
    fun x => mul_pos (mul_pos (hl x) (hp x)) (hf x)
  constructor
  · intro h
    funext x
    have hx := h x
    rw [statePredictionError, logMessage_eq_log_message A B B' o sPrev sNext x (hl x) (hp x)
      (hf x), sub_eq_zero] at hx
    exact (Real.log_injOn_pos (hm x) (hs x) hx).symm
  · intro h x
    rw [statePredictionError, logMessage_eq_log_message A B B' o sPrev sNext x (hl x) (hp x)
      (hf x), h, sub_self]

/-- **One-step exact Bayes.** With a uniform future term, the update is the
categorical posterior `P(x|o) ∝ P(o|x) · (B s_prev)(x)`. -/
theorem onestep_bayes (k : ℝ) (hk : 0 < k) (hconst : ∀ x, futureMsg B' sNext x = k) (x : S) :
    statePosterior A B B' o sPrev sNext x
      = A x o * pastMsg B sPrev x / ∑ y, A y o * pastMsg B sPrev y := by
  have hmsg : ∀ y, message A B B' o sPrev sNext y = k * (A y o * pastMsg B sPrev y) :=
    fun y => by rw [message, likMsg, hconst y]; ring
  rw [statePosterior, hmsg x, Finset.sum_congr rfl fun y _ => hmsg y, ← Finset.mul_sum,
    mul_div_mul_left _ _ hk.ne']

/-- A state the observation or the past rules out gets posterior zero; no
logarithm is involved. -/
theorem statePosterior_zero_of_impossible (x : S)
    (h : A x o = 0 ∨ pastMsg B sPrev x = 0) :
    statePosterior A B B' o sPrev sNext x = 0 := by
  rcases h with h | h <;> simp [statePosterior, message, likMsg, h]

end

/-! ## Fixture: a noisy observation of a two-state world -/

/-- Likelihood `P(o|s)`: correct with probability 9/10. -/
noncomputable def fixtureA : Bool → Bool → ℝ := fun s ob => if s = ob then 9 / 10 else 1 / 10

/-- Identity transition. -/
noncomputable def fixtureB : Bool → Bool → ℝ := fun s s' => if s' = s then 1 else 0

/-- Uniform belief. -/
noncomputable def fixtureUniform : Bool → ℝ := fun _ => 1 / 2

theorem fixture_pastMsg (x : Bool) : pastMsg fixtureB fixtureUniform x = 1 / 2 := by
  cases x <;> simp [pastMsg, fixtureB, fixtureUniform]

theorem fixture_futureMsg (x : Bool) : futureMsg fixtureB fixtureUniform x = 1 / 2 := by
  cases x <;> simp [futureMsg, fixtureB, fixtureUniform]

/-- Observing `true` under a uniform prior gives posterior 9/10 on `true`. -/
theorem fixture_posterior_true :
    statePosterior fixtureA fixtureB fixtureB true fixtureUniform fixtureUniform true = 9 / 10 := by
  rw [onestep_bayes _ _ _ _ _ _ (1 / 2) (by norm_num) fixture_futureMsg]
  simp [fixture_pastMsg, fixtureA]
  norm_num

theorem fixture_posterior_false :
    statePosterior fixtureA fixtureB fixtureB true fixtureUniform fixtureUniform false
      = 1 / 10 := by
  rw [onestep_bayes _ _ _ _ _ _ (1 / 2) (by norm_num) fixture_futureMsg]
  simp [fixture_pastMsg, fixtureA]
  norm_num

/-- The uniform belief is not the fixed point: its error differs between the
two states, so the scheme detects it and moves it. -/
theorem fixture_uniform_not_fixed :
    ¬ ∃ c, ∀ x, statePredictionError fixtureA fixtureB fixtureB true fixtureUniform
        fixtureUniform fixtureUniform x = c := by
  rintro ⟨c, hc⟩
  have ht := hc true
  have hf := hc false
  simp only [statePredictionError, logMessage, likMsg, fixture_pastMsg, fixture_futureMsg,
    fixtureA, fixtureUniform] at ht hf
  simp only [if_true, Bool.false_eq_true, if_false] at ht hf
  have : Real.log (9 / 10) = Real.log (1 / 10) := by linarith
  have h := Real.log_injOn_pos (by norm_num : (0 : ℝ) < 9 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    this
  norm_num at h

end DarkTower.WarMachine.StatePredictionError
