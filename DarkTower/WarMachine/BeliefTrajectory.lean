import DarkTower.WarMachine.StatePredictionError
import DarkTower.WarMachine.PolicyRollout

/-!
# The stored belief: `μ_t` is the belief after the update at `t − 1`

Row `:belief-state` (audit A2 §5), under P9's categorical model. Registry formal:
`mu_t := the stored belief after the update at t-1`. The audit found the old carrier
admitted non-distributions and a reconciliation step that dropped carried beliefs.

The update is the stationary belief of Parr et al. 2022 eq. 4.13 (see
`StatePredictionError`) in its online form: the future message is absent (uniform),
so `s_t(x) ∝ A(o_t|x) · exp(Σ_{s₀} s_{t−1}(s₀) ln B(x|s₀))`. The source's logarithms
are `ln 0 = −∞`; written multiplicatively that is
`exp(Σ_{s₀ ∈ supp s_{t−1}} s_{t−1}(s₀) ln B(x|s₀)) = Π_{s₀ ∈ supp s_{t−1}} B(x|s₀)^{s_{t−1}(s₀)}`,
with `0^p = 0` for `p > 0`, so zero probabilities are represented exactly (a state
the past rules out gets weight `0`) rather than through Lean's `Real.log 0 = 0`.

If the observation is impossible under every state the prior allows, the weights
all vanish and there is no posterior: the update returns `none`, a typed refusal,
instead of dropping or inventing a belief. The carrier is a fixed finite type (under
P2/P4 the token-state type `Finset V`), so no entity-domain reconciliation occurs.
-/

namespace DarkTower.WarMachine.BeliefTrajectory

open DarkTower.WarMachine.PolicyRollout

variable {S O : Type*} [Fintype S] [DecidableEq S]

/-- Unnormalised weight `A(o|x) · Π_{s₀ ∈ supp s_prev} B(x|s₀)^{s_prev(s₀)}`. -/
noncomputable def stateWeight (A : S → O → ℝ) (B : S → S → ℝ) (o : O) (sPrev : S → ℝ)
    (x : S) : ℝ :=
  A x o * ∏ s₀ ∈ Finset.univ.filter (fun s₀ => 0 < sPrev s₀), B s₀ x ^ sPrev s₀

open Classical in
/-- The online update of eq. 4.13: the normalised weights, or `none` when the
observation is impossible under the prior. -/
noncomputable def beliefUpdate (A : S → O → ℝ) (B : S → S → ℝ) (o : O) (sPrev : S → ℝ) :
    Option (S → ℝ) :=
  if ∑ y, stateWeight A B o sPrev y = 0 then none
  else some fun x => stateWeight A B o sPrev x / ∑ y, stateWeight A B o sPrev y

section

variable (A : S → O → ℝ) (B : S → S → ℝ) (o : O) (sPrev : S → ℝ)

theorem stateWeight_nonneg (hA : ∀ x, 0 ≤ A x o) (hB : ∀ s x, 0 ≤ B s x) (x : S) :
    0 ≤ stateWeight A B o sPrev x :=
  mul_nonneg (hA x) (Finset.prod_nonneg fun s₀ _ => Real.rpow_nonneg (hB s₀ x) _)

/-- A state the observation or the past rules out has weight zero. -/
theorem stateWeight_eq_zero (x : S)
    (h : A x o = 0 ∨ ∃ s₀, 0 < sPrev s₀ ∧ B s₀ x = 0) : stateWeight A B o sPrev x = 0 := by
  rcases h with h | ⟨s₀, hp, hb⟩
  · simp [stateWeight, h]
  · refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_filter.mpr
      ⟨Finset.mem_univ s₀, hp⟩) ?_)
    rw [hb, Real.zero_rpow hp.ne']

/-- A returned belief is a distribution. -/
theorem beliefUpdate_dist (hA : ∀ x, 0 ≤ A x o) (hB : ∀ s x, 0 ≤ B s x) {s : S → ℝ}
    (h : beliefUpdate A B o sPrev = some s) : (∀ x, 0 ≤ s x) ∧ ∑ x, s x = 1 := by
  unfold beliefUpdate at h
  split_ifs at h with hz
  cases h
  refine ⟨fun x => div_nonneg (stateWeight_nonneg A B o sPrev hA hB x)
    (Finset.sum_nonneg fun y _ => stateWeight_nonneg A B o sPrev hA hB y), ?_⟩
  rw [← Finset.sum_div, div_self hz]

/-- The update refuses exactly when every state has weight zero. -/
theorem beliefUpdate_eq_none_iff (hA : ∀ x, 0 ≤ A x o) (hB : ∀ s x, 0 ≤ B s x) :
    beliefUpdate A B o sPrev = none ↔ ∀ x, stateWeight A B o sPrev x = 0 := by
  unfold beliefUpdate
  split_ifs with hz
  · simp only [true_iff]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun y _ =>
      stateWeight_nonneg A B o sPrev hA hB y).mp hz |> fun h x => h x (Finset.mem_univ x)
  · simp only [reduceCtorEq, false_iff, not_forall]
    by_contra hall
    push Not at hall
    exact hz (Finset.sum_eq_zero fun y _ => hall y)

end

/-- **Agreement with eq. 4.13's stationary belief.** Where every log is finite
(`LogDefined`, with the future term absent), the update is
`StatePredictionError.statePosterior`. -/
theorem beliefUpdate_eq_statePosterior [Nonempty S] (A : S → O → ℝ) (B B' : S → S → ℝ) (o : O)
    (sPrev : S → ℝ) (hp : ∀ s, 0 ≤ sPrev s)
    (hA : ∀ x, 0 < A x o) (hB : ∀ s₀ x, 0 < sPrev s₀ → 0 < B s₀ x)
    (hfut : ∀ x, StatePredictionError.futureTerm B' (fun _ => 0) x = 0) :
    beliefUpdate A B o sPrev
      = some (StatePredictionError.statePosterior A B B' o sPrev (fun _ => 0)) := by
  have hw : ∀ x, stateWeight A B o sPrev x
      = Real.exp (StatePredictionError.logMessage A B B' o sPrev (fun _ => 0) x) := fun x => by
    rw [StatePredictionError.logMessage, hfut x, add_zero, Real.exp_add,
      StatePredictionError.likTerm, Real.exp_log (hA x), stateWeight]
    congr 1
    rw [StatePredictionError.pastTerm, Real.exp_sum,
      ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun s₀ => 0 < sPrev s₀)]
    have hzero : ∏ s₀ ∈ Finset.univ.filter (fun s₀ => ¬ 0 < sPrev s₀),
        Real.exp (sPrev s₀ * Real.log (B s₀ x)) = 1 := by
      refine Finset.prod_eq_one fun s₀ hs₀ => ?_
      have : sPrev s₀ = 0 :=
        le_antisymm (not_lt.mp (Finset.mem_filter.mp hs₀).2) (hp s₀)
      simp [this]
    rw [hzero, mul_one]
    refine Finset.prod_congr rfl fun s₀ hs₀ => ?_
    rw [Real.rpow_def_of_pos (hB s₀ x (Finset.mem_filter.mp hs₀).2), mul_comm]
  have hpos : 0 < ∑ y, stateWeight A B o sPrev y := by
    simp only [hw]
    exact Finset.sum_pos (fun y _ => Real.exp_pos _) Finset.univ_nonempty
  unfold beliefUpdate
  rw [if_neg hpos.ne']
  congr 1
  funext x
  simp only [StatePredictionError.statePosterior, hw]

/-- **Exact Bayes from an observed state, zeros included.** With the previous state
known (a point mass at `s₀`), the update is `P(x|o) ∝ P(o|x) P(x|s₀)`, with no
positivity hypotheses. -/
theorem beliefUpdate_observed (A : S → O → ℝ) (B : S → S → ℝ) (o : O) (s₀ : S)
    (hZ : ∑ y, A y o * B s₀ y ≠ 0) :
    beliefUpdate A B o (fun s => if s = s₀ then 1 else 0)
      = some fun x => A x o * B s₀ x / ∑ y, A y o * B s₀ y := by
  have hw : ∀ x, stateWeight A B o (fun s => if s = s₀ then 1 else 0) x = A x o * B s₀ x :=
    fun x => by
      have hf : Finset.univ.filter (fun s => 0 < (if s = s₀ then (1 : ℝ) else 0)) = {s₀} := by
        ext s
        by_cases h : s = s₀ <;> simp [h]
      rw [stateWeight, hf, Finset.prod_singleton, if_pos rfl, Real.rpow_one]
  unfold beliefUpdate
  simp only [hw]
  rw [if_neg hZ]

/-! ## The belief trajectory -/

/-- `μ_0 = q₀`; `μ_{t+1}` is the update of `μ_t` by the transition of action `u_t`
and the observation `o_{t+1}`. A refusal is carried forward. -/
noncomputable def beliefAt {U : Type*} (A : S → O → ℝ) (B : U → S → S → ℝ) (q₀ : S → ℝ)
    (u : ℕ → U) (o : ℕ → O) : ℕ → Option (S → ℝ)
  | 0 => some q₀
  | t + 1 => (beliefAt A B q₀ u o t).bind fun s => beliefUpdate A (B (u t)) (o (t + 1)) s

/-- **`μ_t` is the stored belief after the update at `t − 1`.** -/
theorem beliefAt_succ {U : Type*} (A : S → O → ℝ) (B : U → S → S → ℝ) (q₀ : S → ℝ)
    (u : ℕ → U) (o : ℕ → O) (t : ℕ) :
    beliefAt A B q₀ u o (t + 1)
      = (beliefAt A B q₀ u o t).bind fun s => beliefUpdate A (B (u t)) (o (t + 1)) s := rfl

/-- Every stored belief is a distribution. -/
theorem beliefAt_dist {U : Type*} (A : S → O → ℝ) (B : U → S → S → ℝ) (q₀ : S → ℝ)
    (u : ℕ → U) (o : ℕ → O) (hA : ∀ x o, 0 ≤ A x o) (hB : ∀ u s x, 0 ≤ B u s x)
    (hq0 : ∀ x, 0 ≤ q₀ x) (hq1 : ∑ x, q₀ x = 1) :
    ∀ t {s : S → ℝ}, beliefAt A B q₀ u o t = some s → (∀ x, 0 ≤ s x) ∧ ∑ x, s x = 1
  | 0, s, h => by
    simp only [beliefAt, Option.some.injEq] at h
    subst h
    exact ⟨hq0, hq1⟩
  | t + 1, s, h => by
    rw [beliefAt_succ, Option.bind_eq_some_iff] at h
    obtain ⟨s', _, hs⟩ := h
    exact beliefUpdate_dist A (B (u t)) (o (t + 1)) s' (fun x => hA x _) (hB (u t)) hs

/-- The belief at `t` depends only on the actions before `t` and the observations up
to `t`: nothing later is carried back and nothing earlier is dropped. -/
theorem beliefAt_congr {U : Type*} (A : S → O → ℝ) (B : U → S → S → ℝ) (q₀ : S → ℝ)
    {u u' : ℕ → U} {o o' : ℕ → O} :
    ∀ t, (∀ m < t, u m = u' m) → (∀ m ≤ t, o m = o' m) →
      beliefAt A B q₀ u o t = beliefAt A B q₀ u' o' t
  | 0, _, _ => rfl
  | t + 1, hu, ho => by
    rw [beliefAt_succ, beliefAt_succ,
      beliefAt_congr A B q₀ t (fun m hm => hu m (Nat.lt_succ_of_lt hm))
        (fun m hm => ho m (Nat.le_succ_of_le hm)),
      hu t (Nat.lt_succ_self t), ho (t + 1) le_rfl]

/-! ## Fixture -/

/-- Likelihood: correct with probability 9/10. -/
noncomputable def fxA : Bool → Bool → ℝ := fun s ob => if s = ob then 9 / 10 else 1 / 10

/-- Action `true` flips the state deterministically; `false` keeps it. -/
noncomputable def fxB : Bool → Bool → Bool → ℝ := fun u s s' =>
  if u then (if s' = !s then 1 else 0) else (if s' = s then 1 else 0)

/-- From a known state `false`, flipping and then observing `true` stores the belief
`true` with probability 1: the deterministic transition rules `false` out, which the
`ln 0 = −∞` convention requires and Lean's `Real.log 0 = 0` would not give. -/
theorem fixture_deterministic_zero :
    beliefAt fxA fxB (fun s => if s = false then 1 else 0) (fun _ => true) (fun _ => true) 1
      = some fun x => if x = true then 1 else 0 := by
  rw [beliefAt_succ]
  simp only [beliefAt, Option.bind_some]
  rw [beliefUpdate_observed fxA (fxB true) true false (by simp [fxA, fxB, Fintype.sum_bool])]
  congr 1
  funext x
  cases x <;> simp [fxA, fxB, Fintype.sum_bool]

/-- An observation impossible under the prior is refused, not absorbed. -/
theorem fixture_impossible_refused :
    beliefUpdate (fun (s : Bool) (ob : Bool) => if s = ob then (1 : ℝ) else 0) (fxB false) true
      (fun s => if s = false then 1 else 0) = none := by
  rw [beliefUpdate_eq_none_iff _ _ _ _ (fun x => by split_ifs <;> norm_num)
    (fun s x => by simp only [fxB]; split_ifs <;> norm_num)]
  intro x
  cases x
  · exact stateWeight_eq_zero _ _ _ _ _ (Or.inl (by simp))
  · exact stateWeight_eq_zero _ _ _ _ _ (Or.inr ⟨false, by simp, by simp [fxB]⟩)

end DarkTower.WarMachine.BeliefTrajectory
