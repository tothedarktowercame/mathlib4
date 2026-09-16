import Mathlib

/-!
# R4 / audit A3 §2: depth-T policy rollout (forward model)

Da Costa et al. 2020, eqs. (42)–(44) and the generative model they rest on
(`refs/dacosta2020.txt:1418–1423` for the predictive terms `A s^π_τ`;
`refs/dacosta2020.txt:257–259` and Table 2 rows for `D`, `B`, `A` at
`refs/dacosta2020.txt:316–322`): under a policy `π = (u_1, …, u_T)` the
predicted hidden-state belief is rolled forward by the transition matrices,
`Q(s_{τ+1}|π) = Σ_s B(u_τ)(s, s_{τ+1}) Q(s_τ|π)`, from the initial belief
`Q(s_1|π) = D`, and the predicted outcome distribution is
`Q(o_τ|π) = Σ_s A(s, o_τ) Q(s_τ|π)`.
-/

namespace DarkTower.WarMachine.PolicyRollout

variable {S O U : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- A discrete-state generative model: transition `B`, likelihood `A`, and
initial belief `q₀`, each with its actual normalisation facts
(Da Costa et al. 2020, Table 2; `refs/dacosta2020.txt:316–322`). -/
structure ForwardModel (S O U : Type*) [Fintype S] [DecidableEq S] [Fintype O]
    [DecidableEq O] where
  B : U → S → S → ℝ
  B_nonneg : ∀ u s s', 0 ≤ B u s s'
  B_rowsum : ∀ u s, ∑ s' : S, B u s s' = 1
  A : S → O → ℝ
  A_nonneg : ∀ s o, 0 ≤ A s o
  A_colsum : ∀ s, ∑ o : O, A s o = 1
  q₀ : S → ℝ
  q₀_nonneg : ∀ s, 0 ≤ q₀ s
  q₀_sum : ∑ s : S, q₀ s = 1

/-- `Q(s_τ | π)` rolled forward by `B` from `q₀`
(Da Costa et al. 2020, eqs. (42)–(44) and the free-energy terms of eq. (7),
`refs/dacosta2020.txt:583–595`). -/
noncomputable def rolloutState (M : ForwardModel S O U) (π : ℕ → U) : ℕ → S → ℝ
  | 0 => M.q₀
  | n + 1 => fun s' => ∑ s, M.B (π n) s s' * rolloutState M π n s

theorem rolloutState_zero (M : ForwardModel S O U) (π : ℕ → U) :
    rolloutState M π 0 = M.q₀ := rfl

theorem rolloutState_succ (M : ForwardModel S O U) (π : ℕ → U) (n : ℕ) (s' : S) :
    rolloutState M π (n + 1) s' = ∑ s, M.B (π n) s s' * rolloutState M π n s := rfl

/-- Extend a depth-`T` policy (a sequence of actions) to an action sequence by
repeating the last action past the horizon. -/
def policySeq {T : ℕ} (hT : 0 < T) (π : Fin T → U) : ℕ → U :=
  fun n => if h : n < T then π ⟨n, h⟩ else π ⟨T - 1, Nat.sub_lt hT (by norm_num)⟩

theorem policySeq_lt {T : ℕ} (hT : 0 < T) (π : Fin T → U) (n : ℕ) (h : n < T) :
    policySeq hT π n = π ⟨n, h⟩ := by
  simp only [policySeq, dif_pos h]

/-- `Q(s_τ | π)` reads only the first `τ` actions: two action sequences that
agree before `τ` give the same predicted state at `τ`. -/
theorem rolloutState_congr (M : ForwardModel S O U) {π π' : ℕ → U} (τ : ℕ)
    (h : ∀ n < τ, π n = π' n) : rolloutState M π τ = rolloutState M π' τ := by
  induction τ with
  | zero => rfl
  | succ n ih =>
    funext s'
    rw [rolloutState_succ, rolloutState_succ, h n (Nat.lt_succ_self n),
      ih fun m hm => h m (Nat.lt_succ_of_lt hm)]

/-- The depth-`T` rollout of a policy `π = (u_1, …, u_T)`, at `τ ≤ T`. -/
noncomputable def rolloutAt (M : ForwardModel S O U) {T : ℕ} (hT : 0 < T)
    (π : Fin T → U) (τ : Fin (T + 1)) : S → ℝ :=
  rolloutState M (policySeq hT π) τ

/-- The padding `policySeq` uses past the horizon is never read: at any
`τ ≤ T`, every action sequence extending `π` gives the same predicted state. -/
theorem rolloutAt_eq_of_extends (M : ForwardModel S O U) {T : ℕ} (hT : 0 < T)
    (π : Fin T → U) (τ : Fin (T + 1)) (σ : ℕ → U)
    (hσ : ∀ n (h : n < T), σ n = π ⟨n, h⟩) :
    rolloutAt M hT π τ = rolloutState M σ τ := by
  unfold rolloutAt
  apply rolloutState_congr
  intro n hn
  have hnT : n < T := lt_of_lt_of_le hn (Nat.lt_succ_iff.mp τ.isLt)
  rw [policySeq_lt hT π n hnT, hσ n hnT]

theorem rolloutState_nonneg (M : ForwardModel S O U) (π : ℕ → U) (n : ℕ) (s : S) :
    0 ≤ rolloutState M π n s := by
  induction n generalizing s with
  | zero => exact M.q₀_nonneg s
  | succ n ih =>
    have h : rolloutState M π (n + 1) s = ∑ s', M.B (π n) s' s * rolloutState M π n s' := rfl
    rw [h]
    exact Finset.sum_nonneg fun s' _ => mul_nonneg (M.B_nonneg _ _ _) (ih s')

theorem rolloutState_sum (M : ForwardModel S O U) (π : ℕ → U) (n : ℕ) :
    ∑ s', rolloutState M π n s' = 1 := by
  induction n with
  | zero => exact M.q₀_sum
  | succ n ih =>
    have h : ∀ s' : S,
        rolloutState M π (n + 1) s' = ∑ s, M.B (π n) s s' * rolloutState M π n s :=
      fun _ => rfl
    simp only [h]
    calc ∑ s', ∑ s, M.B (π n) s s' * rolloutState M π n s
        = ∑ s, ∑ s', M.B (π n) s s' * rolloutState M π n s := Finset.sum_comm
      _ = ∑ s, rolloutState M π n s * ∑ s', M.B (π n) s s' := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s' _ => mul_comm _ _
      _ = ∑ s, rolloutState M π n s := by simp only [M.B_rowsum, mul_one]
      _ = 1 := ih

/-- `Q(o_τ | π) = Σ_s A(s, o_τ) Q(s_τ | π)` (Da Costa et al. 2020, eq. (44),
`refs/dacosta2020.txt:1418–1423`). -/
noncomputable def predictedOutcome (M : ForwardModel S O U) (π : ℕ → U) (n : ℕ)
    (o : O) : ℝ :=
  ∑ s, M.A s o * rolloutState M π n s

theorem predictedOutcome_nonneg (M : ForwardModel S O U) (π : ℕ → U) (n : ℕ) (o : O) :
    0 ≤ predictedOutcome M π n o :=
  Finset.sum_nonneg fun s _ => mul_nonneg (M.A_nonneg _ _) (rolloutState_nonneg M π n s)

theorem predictedOutcome_sum (M : ForwardModel S O U) (π : ℕ → U) (n : ℕ) :
    ∑ o, predictedOutcome M π n o = 1 := by
  have key : ∀ s : S, ∑ o, M.A s o * rolloutState M π n s = rolloutState M π n s := by
    intro s
    rw [← Finset.sum_mul, M.A_colsum, one_mul]
  simp only [predictedOutcome, Finset.sum_comm, key]
  exact rolloutState_sum M π n

/-- At `τ = 1`, the predicted outcome is the one-step composition
`Σ_{s'} (Σ_s q₀ s · B(π 0) s s') · A s' o` — what
`MachineQ.predictiveOutcomeMass` computes. -/
theorem predictedOutcome_one (M : ForwardModel S O U) (π : ℕ → U) (o : O) :
    predictedOutcome M π 1 o
      = ∑ s', (∑ s, M.q₀ s * M.B (π 0) s s') * M.A s' o := by
  have h1 : predictedOutcome M π 1 o
      = ∑ s, ∑ s', M.A s o * (M.B (π 0) s' s * M.q₀ s') := by
    simp only [predictedOutcome, rolloutState_succ, rolloutState_zero, Finset.mul_sum]
  rw [h1]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

/-! ## Depth fixture: two policies differing only in their second action -/

private def boolB : Bool → Bool → Bool → ℝ :=
  fun u s s' => if u then (if s' = !s then 1 else 0) else (if s' = s then 1 else 0)

private def boolA : Bool → Bool → ℝ := fun s o => if s = o then 1 else 0

private def boolModel : ForwardModel Bool Bool Bool where
  B := boolB
  B_nonneg := by intro u s s'; cases u <;> cases s <;> cases s' <;> dsimp only [boolB] <;> norm_num
  B_rowsum := by
    intro u s
    cases u <;> cases s <;> simp [boolB]
  A := boolA
  A_nonneg := by intro s o; cases s <;> cases o <;> dsimp only [boolA] <;> norm_num
  A_colsum := by intro s; cases s <;> simp [boolA]
  q₀ := fun s => if s then 0 else 1
  q₀_nonneg := by intro s; cases s <;> norm_num
  q₀_sum := by simp [Finset.sum_insert, Finset.sum_singleton]

/-- Two depth-2 policies that differ only in their second action. -/
private def πsame : Fin 2 → Bool := fun _ => false
private def πflip : Fin 2 → Bool := fun i => i.val = 1

/-- Same first action ⟹ identical predicted outcome at τ = 1. -/
theorem fixture_outcome_one_eq (o : Bool) :
    predictedOutcome boolModel (policySeq (by norm_num) πsame) 1 o
      = predictedOutcome boolModel (policySeq (by norm_num) πflip) 1 o := by
  simp only [predictedOutcome, rolloutState, policySeq, πsame, πflip, boolModel, boolB, boolA]
  norm_num

/-- Different second action ⟹ different predicted outcome at τ = 2. -/
theorem fixture_outcome_two_diff :
    predictedOutcome boolModel (policySeq (by norm_num) πsame) 2 true = 0
    ∧ predictedOutcome boolModel (policySeq (by norm_num) πflip) 2 true = 1 := by
  constructor <;>
    simp only [predictedOutcome, rolloutState, policySeq, πsame, πflip, boolModel,
      boolB, boolA] <;>
    norm_num

end DarkTower.WarMachine.PolicyRollout
