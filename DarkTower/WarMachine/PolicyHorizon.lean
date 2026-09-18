import DarkTower.WarMachine.PolicyRollout
import Mathlib.Data.EReal.Operations

/-!
# Policy depth: one horizon for expected free energy

Row `:depth` (audit A4 §2). Friston et al. 2017: `G(π) = Σ_τ G(π, τ)`
(`refs/friston2017.txt:293`, `:483`); each `G(π, τ)` is evaluated at one future
time `τ` (Da Costa et al. 2020 eq. 42, `refs/dacosta2020.txt:1403`, which has no
sum over `τ`; `:1304–1309` identifies the horizon as `T`). Here `T` is a single
depth: every term reads risk and ambiguity from the same predicted state
`Q(s_τ|π)` of `PolicyRollout`, so no term can be evaluated at a different `τ`.
The preference is a family `C_τ` indexed by step (Friston's `U_τ = ln P(o_τ)`,
`refs/friston2017.txt:290`; SPEC §2 `Gτ = KL(Qτ‖Cτ) + …`; design P6), so a
constant `C` is the special case, not the definition. Step `0` is the present
belief `q₀`; the sum runs over the `T` predicted future steps.

**Horizon is not construction length** (SPEC-cascade-policy-semantics Stage 0,
"Horizon and the book"). The monotonicity proved here is in the prediction horizon
`T` for a fixed candidate policy. Candidates must be compared only at a common
declared `T` (a usage rule: the types do not enforce it). The cascade construction index `k` is not `T`, and nothing in this module
scores construction length.
-/

namespace DarkTower.WarMachine.PolicyHorizon

open DarkTower.WarMachine.PolicyRollout
open scoped Classical

variable {S O U : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- Entropy `H[A(·|s)] = −Σ_o A(o|s) ln A(o|s)` of the likelihood column at `s`. -/
noncomputable def rowEntropy (M : ForwardModel S O U) (s : S) : ℝ :=
  -∑ o, M.A s o * Real.log (M.A s o)

/-- Ambiguity at step `n` under the action sequence `σ`:
`Σ_s Q(s_n|π) H[A(·|s)]`. -/
noncomputable def stepAmbiguity (M : ForwardModel S O U) (σ : ℕ → U) (n : ℕ) : ℝ :=
  ∑ s, rolloutState M σ n s * rowEntropy M s

/-- Risk at step `n`: `D_KL[Q(o_n|π) ‖ C]` in `EReal` (as `OutcomeRiskKL`):
`⊤` iff some outcome has positive predicted mass and zero preferred mass; otherwise the
Gibbs sum over positive-mass outcomes. The citation is Da Costa et al. 2020
eq. (44) (`futon2/holes/labs/wm-contract/refs/dacosta2020.txt:1418-1423`,
`(Asπτ) · (log(Asπτ) − log C)`), carried by
`OutcomeRiskKL.outcomeRisk`; `predictedOutcome M σ n o = ∑ s, M.A s o *
rolloutState M σ n s` evaluates this term at the SAME predicted state and
the SAME `M.A` as `stepAmbiguity M σ n` (`∑ s, rolloutState M σ n s *
rowEntropy M s`). -/
noncomputable def stepRisk (M : ForwardModel S O U) (σ : ℕ → U) (n : ℕ) (C : O → ℝ) : EReal :=
  if ∃ o, 0 < predictedOutcome M σ n o ∧ C o = 0 then ⊤
  else ↑(∑ o, if 0 < predictedOutcome M σ n o then
      predictedOutcome M σ n o * Real.log (predictedOutcome M σ n o / C o) else 0)

/-- `G(π, n)`: risk against `C_n` plus ambiguity, both at the same step `n`. -/
noncomputable def stepTerm (M : ForwardModel S O U) (σ : ℕ → U) (n : ℕ) (C : ℕ → O → ℝ) :
    EReal :=
  stepRisk M σ n (C n) + ↑(stepAmbiguity M σ n)

/-- `G(π) = Σ_{τ=1}^{T} G(π, τ)` for a depth-`T` policy and a step-indexed preference. -/
noncomputable def horizonEFE (M : ForwardModel S O U) {T : ℕ} (hT : 0 < T) (π : Fin T → U)
    (C : ℕ → O → ℝ) : EReal :=
  ∑ i : Fin T, stepTerm M (policySeq hT π) (i.val + 1) C

/-! ## Each term depends only on the actions before its step -/

theorem stepTerm_congr (M : ForwardModel S O U) {σ σ' : ℕ → U} (n : ℕ) (C : ℕ → O → ℝ)
    (h : ∀ m < n, σ m = σ' m) : stepTerm M σ n C = stepTerm M σ' n C := by
  have hr := rolloutState_congr M n h
  simp only [stepTerm, stepRisk, stepAmbiguity, predictedOutcome, hr]

/-! ## Nonnegativity -/

theorem rowEntropy_nonneg (M : ForwardModel S O U) (s : S) : 0 ≤ rowEntropy M s := by
  have hle : ∀ o, M.A s o ≤ 1 := fun o => by
    rw [← M.A_colsum s]
    exact Finset.single_le_sum (fun o' _ => M.A_nonneg s o') (Finset.mem_univ o)
  rw [rowEntropy, neg_nonneg]
  exact Finset.sum_nonpos fun o _ => Real.mul_log_nonpos (M.A_nonneg s o) (hle o)

theorem stepAmbiguity_nonneg (M : ForwardModel S O U) (σ : ℕ → U) (n : ℕ) :
    0 ≤ stepAmbiguity M σ n :=
  Finset.sum_nonneg fun s _ => mul_nonneg (rolloutState_nonneg M σ n s) (rowEntropy_nonneg M s)

/-- Gibbs' inequality for the risk term, for a preference distribution `C`. -/
theorem stepRisk_nonneg (M : ForwardModel S O U) (σ : ℕ → U) (n : ℕ) (C : O → ℝ)
    (hC0 : ∀ o, 0 ≤ C o) (hC1 : ∑ o, C o = 1) : 0 ≤ stepRisk M σ n C := by
  unfold stepRisk
  split_ifs with h
  · exact le_top
  · push_neg at h
    refine EReal.coe_nonneg.mpr ?_
    set q := predictedOutcome M σ n
    have key : ∀ o, q o - C o ≤ (if 0 < q o then q o * Real.log (q o / C o) else 0) := fun o => by
      by_cases hq : 0 < q o
      · have hc : 0 < C o := lt_of_le_of_ne (hC0 o) (Ne.symm (h o hq))
        rw [if_pos hq]
        have hlog := Real.log_le_sub_one_of_pos (div_pos hc hq)
        have hmul : q o * (C o / q o) = C o := mul_div_cancel₀ _ hq.ne'
        rw [Real.log_div hc.ne' hq.ne'] at hlog
        rw [Real.log_div hq.ne' hc.ne']
        nlinarith
      · rw [if_neg hq]
        have : q o = 0 := le_antisymm (not_lt.mp hq) (predictedOutcome_nonneg M σ n o)
        linarith [hC0 o]
    have hsum : ∑ o, (q o - C o) = 0 := by
      rw [Finset.sum_sub_distrib, predictedOutcome_sum, hC1, sub_self]
    calc (0 : ℝ) = ∑ o, (q o - C o) := hsum.symm
      _ ≤ _ := Finset.sum_le_sum fun o _ => key o

theorem stepTerm_nonneg (M : ForwardModel S O U) (σ : ℕ → U) (n : ℕ) (C : ℕ → O → ℝ)
    (hC0 : ∀ o, 0 ≤ C n o) (hC1 : ∑ o, C n o = 1) : 0 ≤ stepTerm M σ n C :=
  add_nonneg (stepRisk_nonneg M σ n (C n) hC0 hC1) (EReal.coe_nonneg.mpr (stepAmbiguity_nonneg M σ n))

/-! ## One range: extending the horizon adds exactly the next step -/

/-- **Depth is one range.** For a depth-`T+1` policy and its first `T` actions,
`G_{T+1}(π) = G_T(π|T) + G(π, T+1)`: the new term is the risk and ambiguity at the
one new step, and every earlier term is unchanged. -/
theorem horizonEFE_succ (M : ForwardModel S O U) {T : ℕ} (hT : 0 < T) (π : Fin (T + 1) → U)
    (C : ℕ → O → ℝ) :
    horizonEFE M (Nat.succ_pos T) π C
      = horizonEFE M hT (fun i => π i.castSucc) C
        + stepTerm M (policySeq (Nat.succ_pos T) π) (T + 1) C := by
  rw [horizonEFE, Fin.sum_univ_castSucc, horizonEFE]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  apply stepTerm_congr
  intro m hm
  have hmT : m < T := by simp only [Fin.val_castSucc] at hm; omega
  rw [policySeq_lt _ π m (by omega), policySeq_lt hT _ m hmT]
  rfl

/-- **Monotone in the prediction horizon, for a fixed candidate.** This is not a
statement about construction length: compare candidates only at a common `T`. -/
theorem horizonEFE_mono (M : ForwardModel S O U) {T : ℕ} (hT : 0 < T) (π : Fin (T + 1) → U)
    (C : ℕ → O → ℝ) (hC0 : ∀ n o, 0 ≤ C n o) (hC1 : ∀ n, ∑ o, C n o = 1) :
    horizonEFE M hT (fun i => π i.castSucc) C ≤ horizonEFE M (Nat.succ_pos T) π C := by
  rw [horizonEFE_succ M hT π C]
  exact le_add_of_nonneg_right (stepTerm_nonneg M _ _ C (hC0 _) (hC1 _))

/-- At `T = 1`, `G` is the one-step risk plus ambiguity. -/
theorem horizonEFE_one (M : ForwardModel S O U) (π : Fin 1 → U) (C : ℕ → O → ℝ) :
    horizonEFE M Nat.one_pos π C = stepTerm M (policySeq Nat.one_pos π) 1 C := by
  simp [horizonEFE]

/-! ## Infinite risk anywhere in the horizon makes `G` infinite -/

private theorem sum_eq_top_iff {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) : s.sum f = ⊤ ↔ ∃ i ∈ s, f i = ⊤ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, f i ≠ ⊥ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsb : s.sum f ≠ ⊥ :=
      Finset.sum_induction f (· ≠ ⊥) (fun _ _ h1 h2 => EReal.add_ne_bot_iff.mpr ⟨h1, h2⟩)
        (by simp) hs
    rw [Finset.sum_insert ha]
    constructor
    · intro h
      by_cases hfa : f a = ⊤
      · exact ⟨a, Finset.mem_insert_self a s, hfa⟩
      · by_cases hst : s.sum f = ⊤
        · obtain ⟨i, hi, hfi⟩ := (ih hs).mp hst
          exact ⟨i, Finset.mem_insert_of_mem hi, hfi⟩
        · exact absurd h ((EReal.add_ne_top_iff_ne_top_left hsb hst).mpr hfa)
    · rintro ⟨i, hi, hfi⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rw [hfi, EReal.top_add_of_ne_bot hsb]
      · rw [(ih hs).mpr ⟨i, hi, hfi⟩, EReal.add_top_of_ne_bot (hf a (Finset.mem_insert_self a s))]

/-- `G = ⊤` iff some step within the horizon has infinite risk. -/
theorem horizonEFE_eq_top_iff (M : ForwardModel S O U) {T : ℕ} (hT : 0 < T) (π : Fin T → U)
    (C : ℕ → O → ℝ) (hC0 : ∀ n o, 0 ≤ C n o) (hC1 : ∀ n, ∑ o, C n o = 1) :
    horizonEFE M hT π C = ⊤ ↔
      ∃ i : Fin T, stepRisk M (policySeq hT π) (i.val + 1) (C (i.val + 1)) = ⊤ := by
  have hnb : ∀ i ∈ (Finset.univ : Finset (Fin T)),
      stepTerm M (policySeq hT π) (i.val + 1) C ≠ ⊥ := fun i _ =>
    ne_bot_of_le_ne_bot (by simp) (stepTerm_nonneg M _ _ C (hC0 _) (hC1 _))
  rw [horizonEFE, sum_eq_top_iff _ _ hnb]
  simp only [Finset.mem_univ, true_and]
  refine exists_congr fun i => ?_
  have hrb : stepRisk M (policySeq hT π) (i.val + 1) (C (i.val + 1)) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (stepRisk_nonneg M _ _ _ (hC0 _) (hC1 _))
  rw [stepTerm]
  constructor
  · intro h
    by_contra hr
    exact absurd h ((EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot _)
      (EReal.coe_ne_top _)).mpr hr)
  · intro h
    rw [h, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]

/-! ## Fixture: depth matters -/

/-- Action `true` flips the state, `false` keeps it. -/
private noncomputable def fxModel : ForwardModel Bool Bool Bool where
  B := fun u s s' => if u then (if s' = !s then 1 else 0) else (if s' = s then 1 else 0)
  B_nonneg := by intro u s s'; split_ifs <;> norm_num
  B_rowsum := by intro u s; cases u <;> cases s <;> simp
  A := fun s o => if s = o then 1 else 0
  A_nonneg := by intro s o; split_ifs <;> norm_num
  A_colsum := by intro s; cases s <;> simp
  q₀ := fun s => if s then 0 else 1
  q₀_nonneg := by intro s; split_ifs <;> norm_num
  q₀_sum := by simp

/-- Preference: outcome `false` preferred 3/4, `true` 1/4. -/
private noncomputable def fxC : Bool → ℝ := fun o => if o then 1 / 4 else 3 / 4

private def πstay : Fin 2 → Bool := fun _ => false
private def πflip : Fin 2 → Bool := fun i => decide (i.val = 1)

private theorem fx_rowEntropy (s : Bool) : rowEntropy fxModel s = 0 := by
  cases s <;> simp [rowEntropy, fxModel]

/-- A point-mass prediction at an outcome of positive preference has risk
`ln (1 / C o₀)`. -/
private theorem fx_stepRisk_point (C : Bool → ℝ) (hCt : 0 < C true) (hCf : 0 < C false)
    (σ : ℕ → Bool) (n : ℕ) (o₀ : Bool)
    (hq : ∀ o, predictedOutcome fxModel σ n o = if o = o₀ then 1 else 0) :
    stepRisk fxModel σ n C = ↑(Real.log (1 / C o₀)) := by
  have hne : ¬ ∃ o, 0 < predictedOutcome fxModel σ n o ∧ C o = 0 := by
    rintro ⟨o, h1, h2⟩
    cases o
    · exact hCf.ne' h2
    · exact hCt.ne' h2
  rw [stepRisk, if_neg hne]
  congr 1
  rw [Fintype.sum_bool, hq true, hq false]
  cases o₀ <;> simp

private theorem fx_rollout (σ : ℕ → Bool) (n : ℕ) (b : Bool)
    (h : rolloutState fxModel σ n = fun s => if s = b then 1 else 0) (o : Bool) :
    predictedOutcome fxModel σ n o = if o = b then 1 else 0 := by
  rw [predictedOutcome, h, Fintype.sum_bool]
  cases o <;> cases b <;> simp [fxModel]

private theorem fx_stepAmbiguity (σ : ℕ → Bool) (n : ℕ) : stepAmbiguity fxModel σ n = 0 := by
  simp [stepAmbiguity, fx_rowEntropy]

private theorem fx_state_one (π : Fin 2 → Bool) (h0 : π 0 = false) :
    rolloutState fxModel (policySeq (by norm_num) π) 1 = fun s => if s = false then 1 else 0 := by
  funext s'
  rw [rolloutState_succ, rolloutState_zero, policySeq_lt _ π 0 (by norm_num)]
  have : π ⟨0, by norm_num⟩ = false := h0
  rw [this, Fintype.sum_bool]
  cases s' <;> simp [fxModel]

private theorem fx_state_two_stay :
    rolloutState fxModel (policySeq (by norm_num) πstay) 2 = fun s => if s = false then 1 else 0 := by
  funext s'
  rw [rolloutState_succ, fx_state_one πstay rfl, policySeq_lt _ πstay 1 (by norm_num)]
  rw [Fintype.sum_bool]
  cases s' <;> simp [fxModel, πstay]

private theorem fx_state_two_flip :
    rolloutState fxModel (policySeq (by norm_num) πflip) 2 = fun s => if s = true then 1 else 0 := by
  funext s'
  rw [rolloutState_succ, fx_state_one πflip rfl, policySeq_lt _ πflip 1 (by norm_num)]
  rw [Fintype.sum_bool]
  cases s' <;> simp [fxModel, πflip]

/-- The two depth-2 policies share their first action, so their first-step terms
are equal: `ln (4/3)` each. -/
theorem fixture_first_step_equal :
    stepTerm fxModel (policySeq (by norm_num) πstay) 1 (fun _ => fxC)
      = stepTerm fxModel (policySeq (by norm_num) πflip) 1 (fun _ => fxC) := by
  simp only [stepTerm, fx_stepAmbiguity]
  rw [fx_stepRisk_point fxC (by norm_num [fxC]) (by norm_num [fxC]) _ 1 false (fx_rollout _ 1 false (fx_state_one πstay rfl)),
    fx_stepRisk_point fxC (by norm_num [fxC]) (by norm_num [fxC]) _ 1 false (fx_rollout _ 1 false (fx_state_one πflip rfl))]

/-- At depth 2 they differ: `2 ln (4/3)` against `ln (4/3) + ln 4`. -/
theorem fixture_depth_two_differs :
    horizonEFE fxModel (by norm_num) πstay (fun _ => fxC) = ↑(2 * Real.log (4 / 3)) ∧
      horizonEFE fxModel (by norm_num) πflip (fun _ => fxC) = ↑(Real.log (4 / 3) + Real.log 4) ∧
      (2 * Real.log (4 / 3) : ℝ) ≠ Real.log (4 / 3) + Real.log 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [horizonEFE, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, zero_add, stepTerm, fx_stepAmbiguity]
    rw [fx_stepRisk_point fxC (by norm_num [fxC]) (by norm_num [fxC]) _ 1 false (fx_rollout _ 1 false (fx_state_one πstay rfl)),
      fx_stepRisk_point fxC (by norm_num [fxC]) (by norm_num [fxC]) _ 2 false (fx_rollout _ 2 false fx_state_two_stay)]
    simp only [fxC, Bool.false_eq_true, if_false, EReal.coe_zero, add_zero]
    rw [← EReal.coe_add]
    norm_num
    norm_cast
    ring
  · rw [horizonEFE, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, zero_add, stepTerm, fx_stepAmbiguity]
    rw [fx_stepRisk_point fxC (by norm_num [fxC]) (by norm_num [fxC]) _ 1 false (fx_rollout _ 1 false (fx_state_one πflip rfl)),
      fx_stepRisk_point fxC (by norm_num [fxC]) (by norm_num [fxC]) _ 2 true (fx_rollout _ 2 true fx_state_two_flip)]
    simp only [fxC, Bool.false_eq_true, if_false, if_true, EReal.coe_zero, add_zero]
    rw [← EReal.coe_add]
    norm_num
  · intro h
    have h3 : Real.log (4 / 3) = Real.log 4 := by linarith
    have := Real.log_injOn_pos (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num : (0 : ℝ) < 4) h3
    norm_num at this

/-- The reversed preference: outcome `true` preferred 3/4. -/
private noncomputable def fxC' : Bool → ℝ := fun o => if o then 3 / 4 else 1 / 4

/-- **The preference is indexed by step.** With `C_1 = fxC` and `C_2 = fxC'` the
ranking reverses against a constant `C`: the policy that flips at step 2 now scores
`2 ln (4/3)`, and the one that stays `ln (4/3) + ln 4`. No constant `C` gives both. -/
theorem fixture_stepIndexed_preference :
    horizonEFE fxModel (by norm_num) πstay (fun n => if n = 2 then fxC' else fxC)
        = ↑(Real.log (4 / 3) + Real.log 4) ∧
      horizonEFE fxModel (by norm_num) πflip (fun n => if n = 2 then fxC' else fxC)
        = ↑(2 * Real.log (4 / 3)) := by
  refine ⟨?_, ?_⟩
  · rw [horizonEFE, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, zero_add, stepTerm, fx_stepAmbiguity]
    simp only [show (1 : ℕ) ≠ 2 by decide, if_false, if_true, Nat.reduceAdd]
    rw [fx_stepRisk_point fxC (by norm_num [fxC]) (by norm_num [fxC]) _ 1 false
        (fx_rollout _ 1 false (fx_state_one πstay rfl)),
      fx_stepRisk_point fxC' (by norm_num [fxC']) (by norm_num [fxC']) _ 2 false
        (fx_rollout _ 2 false fx_state_two_stay)]
    simp only [fxC, fxC', Bool.false_eq_true, if_false, EReal.coe_zero, add_zero]
    rw [← EReal.coe_add]
    norm_num
  · rw [horizonEFE, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, zero_add, stepTerm, fx_stepAmbiguity]
    simp only [show (1 : ℕ) ≠ 2 by decide, if_false, if_true, Nat.reduceAdd]
    rw [fx_stepRisk_point fxC (by norm_num [fxC]) (by norm_num [fxC]) _ 1 false
        (fx_rollout _ 1 false (fx_state_one πflip rfl)),
      fx_stepRisk_point fxC' (by norm_num [fxC']) (by norm_num [fxC']) _ 2 true
        (fx_rollout _ 2 true fx_state_two_flip)]
    simp only [fxC, fxC', Bool.false_eq_true, if_false, if_true, EReal.coe_zero, add_zero]
    rw [← EReal.coe_add]
    norm_num
    norm_cast
    ring

end DarkTower.WarMachine.PolicyHorizon
