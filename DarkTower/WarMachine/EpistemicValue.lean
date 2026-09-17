import DarkTower.WarMachine.PolicyHorizon

/-!
# Epistemic value of a check: why P7's G gives none, and the form that does

Joe's D3 amendment (2026-09-17, `PROPOSAL-pattern-interpretation.md` under D3):
an unknown fact is a belief spread over f⁺ and f⁻, a check is a candidate, and
its result enters as an observation. claude-4 asked whether `horizonEFE` values
such a check.

**It does not, and the reason is exact.** In `PolicyHorizon` the likelihood `A`
is one kernel for every action, so a policy affects `G` only through the
transition kernel `B` (`horizonEFE_eq_of_B` below). A pure check changes no
state (its `B` equals doing nothing), so its `G` equals doing nothing's.

**The epistemic term is already inside risk plus ambiguity.** For a fixed
observation channel, `KL[Q(o)‖C] + E_Q(s) H[A(·|s)] = −E_Q(o) ln C(o) − I(s; o)`:
expected preference cost minus the mutual information between the predicted
state and its observation (the standard pragmatic/epistemic split). So no
separate information-gain term is needed. What is missing is that the
observation made at a step does not depend on what the agent did.

**The form adopted here: the acting pattern selects the observation channel.**
`ActiveModel` adds `Aᵤ : U → S → O → ℝ`. The observation at step `n` is made
through the channel of the action taken into that step, `σ (n − 1)`. Risk and
ambiguity are unchanged in shape. P7's `horizonEFE` is the special case where
every `Aᵤ u = A` (`activeHorizonEFE_eq_horizonEFE`).

The fixture: one unknown binary fact with belief (1/2, 1/2), identity dynamics,
indifferent preference. Doing nothing observes a constant, `G = ln 2`. Checking
observes the fact, `G = 0`. The difference `ln 2` is exactly the information
the check gains. Under P7's form the two policies score the same
(`fixture_p7_check_no_value`).

**Not adopted here (decided, not deferred by accident).**
- A belief-conditioned (sophisticated) rollout, where predicted observations
  update belief before later steps. That gives a check *instrumental* value (the
  answer changes what is done next). This module gives it the *intrinsic*
  epistemic value of standard EFE. Instrumental value is a later extension, needed
  when a check's worth is mostly in what it unlocks; it requires the posterior
  over states given o to feed the next step's prior.
- Information gain about *parameters and interpretations* (novelty; e.g. which
  reading of a pattern is right, a pattern's θ). That is not state information
  and is not in risk plus ambiguity. It needs an explicit Dirichlet novelty term
  (`DirichletLearning`), and it is the epistemic value construction moves need.
-/

namespace DarkTower.WarMachine.EpistemicValue

open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.PolicyHorizon
open scoped Classical

variable {S O U : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-! ## Under P7's form, a policy acts on G only through B -/

theorem rolloutState_eq_of_B (M : ForwardModel S O U) (σ σ' : ℕ → U)
    (h : ∀ n, M.B (σ n) = M.B (σ' n)) (n : ℕ) :
    rolloutState M σ n = rolloutState M σ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext s'
    rw [rolloutState_succ, rolloutState_succ, h n, ih]

/-- Two policies with the same transition kernels at every step have the same
`horizonEFE`, whatever else distinguishes them. A check whose `B` is doing
nothing's therefore has doing nothing's `G`. -/
theorem horizonEFE_eq_of_B (M : ForwardModel S O U) {T : ℕ} (hT : 0 < T)
    (π π' : Fin T → U) (C : ℕ → O → ℝ)
    (h : ∀ n, M.B (policySeq hT π n) = M.B (policySeq hT π' n)) :
    horizonEFE M hT π C = horizonEFE M hT π' C := by
  have hr := rolloutState_eq_of_B M _ _ h
  simp only [horizonEFE, stepTerm, stepRisk, stepAmbiguity, predictedOutcome, hr]

/-! ## The observation channel chosen by the acting pattern -/

/-- A forward model whose observation kernel is selected by the action. -/
structure ActiveModel (S O U : Type*) [Fintype S] [DecidableEq S] [Fintype O]
    [DecidableEq O] extends ForwardModel S O U where
  Aᵤ : U → S → O → ℝ
  Aᵤ_nonneg : ∀ u s o, 0 ≤ Aᵤ u s o
  Aᵤ_colsum : ∀ u s, ∑ o : O, Aᵤ u s o = 1

/-- `Q(o_n | π)` observed through the channel of the action taken into step `n`. -/
noncomputable def activePredictedOutcome (M : ActiveModel S O U) (σ : ℕ → U) (n : ℕ)
    (o : O) : ℝ :=
  ∑ s, M.Aᵤ (σ (n - 1)) s o * rolloutState M.toForwardModel σ n s

/-- `H[Aᵤ(·|s)]`. -/
noncomputable def activeRowEntropy (M : ActiveModel S O U) (u : U) (s : S) : ℝ :=
  -∑ o, M.Aᵤ u s o * Real.log (M.Aᵤ u s o)

noncomputable def activeStepAmbiguity (M : ActiveModel S O U) (σ : ℕ → U) (n : ℕ) : ℝ :=
  ∑ s, rolloutState M.toForwardModel σ n s * activeRowEntropy M (σ (n - 1)) s

noncomputable def activeStepRisk (M : ActiveModel S O U) (σ : ℕ → U) (n : ℕ)
    (C : O → ℝ) : EReal :=
  if ∃ o, 0 < activePredictedOutcome M σ n o ∧ C o = 0 then ⊤
  else ↑(∑ o, if 0 < activePredictedOutcome M σ n o then
      activePredictedOutcome M σ n o * Real.log (activePredictedOutcome M σ n o / C o) else 0)

noncomputable def activeStepTerm (M : ActiveModel S O U) (σ : ℕ → U) (n : ℕ)
    (C : ℕ → O → ℝ) : EReal :=
  activeStepRisk M σ n (C n) + ↑(activeStepAmbiguity M σ n)

/-- `G(π) = Σ_{τ=1}^{T} [KL(Q(o_τ|π) ‖ C_τ) + E_{Q(s_τ|π)} H[A_{π(τ−1)}]]`. -/
noncomputable def activeHorizonEFE (M : ActiveModel S O U) {T : ℕ} (hT : 0 < T)
    (π : Fin T → U) (C : ℕ → O → ℝ) : EReal :=
  ∑ i : Fin T, activeStepTerm M (policySeq hT π) (i.val + 1) C

/-- P7's `horizonEFE` is the special case with one channel for every action. -/
theorem activeHorizonEFE_eq_horizonEFE (M : ActiveModel S O U) (hA : ∀ u, M.Aᵤ u = M.A)
    {T : ℕ} (hT : 0 < T) (π : Fin T → U) (C : ℕ → O → ℝ) :
    activeHorizonEFE M hT π C = horizonEFE M.toForwardModel hT π C := by
  simp only [activeHorizonEFE, activeStepTerm, activeStepRisk, activeStepAmbiguity,
    activePredictedOutcome, activeRowEntropy, hA, horizonEFE, stepTerm, stepRisk,
    stepAmbiguity, predictedOutcome, rowEntropy]

/-! ## Fixture: checking an unknown fact -/

/-- One binary fact, unknown: belief (1/2, 1/2). Both actions leave the state
unchanged. Action `false` (do nothing) observes a constant; action `true`
(check) observes the fact. -/
noncomputable def ckModel : ActiveModel Bool Bool Bool where
  B := fun _ s s' => if s' = s then 1 else 0
  B_nonneg := by intro u s s'; split_ifs <;> norm_num
  B_rowsum := by intro u s; cases s <;> simp
  A := fun _ o => if o = false then 1 else 0
  A_nonneg := by intro s o; split_ifs <;> norm_num
  A_colsum := by intro s; simp
  q₀ := fun _ => 1 / 2
  q₀_nonneg := by intro s; norm_num
  q₀_sum := by rw [Fintype.sum_bool]; norm_num
  Aᵤ := fun u s o => if u then (if s = o then 1 else 0) else (if o = false then 1 else 0)
  Aᵤ_nonneg := by intro u s o; split_ifs <;> norm_num
  Aᵤ_colsum := by intro u s; cases u <;> cases s <;> simp

/-- Indifferent preference over the observation. -/
noncomputable def ckC : ℕ → Bool → ℝ := fun _ _ => 1 / 2

def πnoop : Fin 1 → Bool := fun _ => false
def πcheck : Fin 1 → Bool := fun _ => true

private theorem ck_state_one (σ : ℕ → Bool) (s : Bool) :
    rolloutState ckModel.toForwardModel σ 1 s = 1 / 2 := by
  rw [rolloutState_succ, Fintype.sum_bool]
  cases s <;> simp [rolloutState, ckModel]

private theorem ck_seq_zero (π : Fin 1 → Bool) : policySeq (by norm_num) π 0 = π 0 :=
  policySeq_lt _ π 0 (by norm_num)

private theorem ck_noop_outcome (o : Bool) :
    activePredictedOutcome ckModel (policySeq (by norm_num) πnoop) 1 o
      = if o = false then 1 else 0 := by
  simp only [activePredictedOutcome, Nat.sub_self, ck_seq_zero, ck_state_one,
    Fintype.sum_bool]
  cases o <;> norm_num [ckModel, πnoop]

private theorem ck_check_outcome (o : Bool) :
    activePredictedOutcome ckModel (policySeq (by norm_num) πcheck) 1 o = 1 / 2 := by
  simp only [activePredictedOutcome, Nat.sub_self, ck_seq_zero, ck_state_one,
    Fintype.sum_bool]
  cases o <;> simp [ckModel, πcheck]

private theorem ck_entropy (u s : Bool) : activeRowEntropy ckModel u s = 0 := by
  cases u <;> cases s <;> simp [activeRowEntropy, ckModel]

private theorem ck_ambiguity (σ : ℕ → Bool) (n : ℕ) :
    activeStepAmbiguity ckModel σ n = 0 := by
  simp [activeStepAmbiguity, ck_entropy]

/-- Doing nothing: the observation is constant, so the predicted outcome is a point
mass against an indifferent preference, `G = ln 2`. -/
theorem fixture_noop_G :
    activeHorizonEFE ckModel (by norm_num) πnoop ckC = ↑(Real.log 2) := by
  rw [activeHorizonEFE, Fin.sum_univ_one]
  simp only [Fin.val_zero, zero_add, activeStepTerm, ck_ambiguity, EReal.coe_zero, add_zero]
  have hne : ¬ ∃ o, 0 < activePredictedOutcome ckModel (policySeq (by norm_num) πnoop) 1 o
      ∧ ckC 1 o = 0 := by
    rintro ⟨o, -, h⟩; norm_num [ckC] at h
  rw [activeStepRisk, if_neg hne, Fintype.sum_bool, ck_noop_outcome, ck_noop_outcome]
  congr 1
  simp [ckC]

/-- Checking: the observation reveals the fact, the predicted outcome matches the
indifferent preference, and ambiguity is zero, `G = 0`. -/
theorem fixture_check_G :
    activeHorizonEFE ckModel (by norm_num) πcheck ckC = 0 := by
  rw [activeHorizonEFE, Fin.sum_univ_one]
  simp only [Fin.val_zero, zero_add, activeStepTerm, ck_ambiguity, EReal.coe_zero, add_zero]
  have hne : ¬ ∃ o, 0 < activePredictedOutcome ckModel (policySeq (by norm_num) πcheck) 1 o
      ∧ ckC 1 o = 0 := by
    rintro ⟨o, -, h⟩; norm_num [ckC] at h
  rw [activeStepRisk, if_neg hne, Fintype.sum_bool, ck_check_outcome, ck_check_outcome]
  simp [ckC]

/-- The check is strictly preferred, by exactly the information it gains (`ln 2`). -/
theorem fixture_check_strictly_better :
    activeHorizonEFE ckModel (by norm_num) πcheck ckC
      < activeHorizonEFE ckModel (by norm_num) πnoop ckC := by
  rw [fixture_check_G, fixture_noop_G]
  exact_mod_cast Real.log_pos (by norm_num)

/-- Under P7's form (one channel for every action) the same two policies score
the same: `B` is identical, so `horizonEFE_eq_of_B` applies. -/
theorem fixture_p7_check_no_value :
    horizonEFE ckModel.toForwardModel (by norm_num) πcheck ckC
      = horizonEFE ckModel.toForwardModel (by norm_num) πnoop ckC :=
  horizonEFE_eq_of_B _ _ _ _ _ (fun _ => rfl)

end DarkTower.WarMachine.EpistemicValue
