import DarkTower.WarMachine.StatePredictionError
import DarkTower.WarMachine.Proof2.RolloutAtMachine

/-!
# The state prediction error at the machine's own rollout (W5, registry `:state-prediction-error`, R3a)

## What the row says

`:state-prediction-error`'s `:formal` is Parr et al. 2022 eq. 4.13, the mean-field form:

`ε_π,τ(x) := ln A(o_τ|x) + Σ_{s₀} s_π,τ−1(s₀) ln B_π,τ(x|s₀) + Σ_{s₁} s_π,τ+1(s₁) ln B_π,τ+1(s₁|x) − ln s_π,τ(x)`.

Its `:imports` are `[:A :B :o :s]`, and its declared domain is: `A(o|·) > 0`, and
`B`, `B_next > 0` on the support of `s_prev`, `s_next` (the source's `ln 0 = −∞` is not
represented; Lean's `Real.log 0 = 0` would count a zero probability as one).
`StatePredictionError.statePredictionError` takes `A`, `B`, `B'`, `o` and the three
state marginals as free arguments, so the registry edges R4→R3a (`A`, `B`) were
parametric.

## What this module supplies

* `A`, `B`: the model's own (`M.A`, and `M.B` at the policy's actions, `plan π (τ−1)`
  into step `τ` and `plan π τ` out of it: the `rolloutState` index convention);
* `s_π,τ−1`, `s_π,τ`, `s_π,τ+1`: the marginals of W4's rollout, started at the machine's
  CURRENT belief (`withBelief`, W3's `machineTrajectory`), not at `q₀`;
* `o_τ := obs τ`, the recorded observation. The error needs `o` as an element of the
  model's observation type `O` (for the token carriers `Finset V`, all of `V`); nothing
  here restricts it to the checked tokens. C5's `TokenLikelihoodRestrict` is not used:
  the model's `M.A` is applied as it stands.

The rollout marginals are the model's PREDICTED state marginals, so `ε` here is the
error of eq. 4.13 evaluated at the rollout's `s_π,τ`, not at a converged posterior.

## The domain, stated as a refusal

The row's domain is a hypothesis of `LogDefined`, and the error also takes `ln s(x)`,
which the row's domain does not list; positivity of `s_π,τ` is required here too, and
said so. Where it fails the result is `ErrorAbsence.logUndefined`, not a value. A step
outside `1 ≤ τ` and `τ + 1 ≤ T` is `outOfHorizon` (eq. 4.13 needs both neighbours).
No default belief, policy, horizon or error.

## At the stationary posterior

By the module's own definition, at `s = σ(v)` the error is `ln Z` at every state, with
`Z = Σ_y exp (logMessage y)`. It is `0` only when `Z = 1`, not in general
(`StatePredictionError.error_at_posterior`; `errorAtPosterior_eq_logZ` states it for the
machine's inputs).
-/

namespace DarkTower.WarMachine.Proof2.StatePredictionErrorAtMachine

open DarkTower.WarMachine
open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.StatePredictionError
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
open DarkTower.WarMachine.Proof2.ObservationAtMachine
open DarkTower.WarMachine.Proof2.BeliefAtMachine
open DarkTower.WarMachine.Proof2.BeliefStepAtMachine
open DarkTower.WarMachine.Proof2.RolloutAtMachine

noncomputable section

variable {S O U PolicyIndex : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- Why there is no error. -/
inductive ErrorAbsence (PolicyIndex : Type*) where
  | rollout (a : RolloutAbsence PolicyIndex)
  | outOfHorizon
  | logUndefined

section
variable [LinearOrder U] [DecidableEq PolicyIndex]

open Classical in
/-- **The rollout's state marginals at the machine's current belief**, with the guards of
`machineRollout` (same absences). `τ ↦ Q(s_τ | π)`. -/
def machineStates (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) :
    Except (RolloutAbsence PolicyIndex) (ℕ → S → ℝ) :=
  match h : machineTrajectory M inputsAt world obs t with
  | .error a => .error (.belief a)
  | .ok μ =>
    if T = 0 then .error .zeroDepth
    else if π ∈ (inputsAt t μ).policies then
      .ok fun τ => rolloutState
        (withBelief M μ (machineTrajectory_isDistribution M inputsAt world obs t μ h).1
          (machineTrajectory_isDistribution M inputsAt world obs t μ h).2)
        (plan π) τ
    else .error .notInPolicySet

end

/-- The error of eq. 4.13 at the states of a rollout: `A`, `B` from the model, `B` at the
policy's actions into and out of step `τ`. -/
def errorAtStates (M : ForwardModel S O U) (st : ℕ → S → ℝ) (π : ℕ → U) (τ : ℕ) (o : O) :
    S → ℝ :=
  statePredictionError M.A (M.B (π (τ - 1))) (M.B (π τ)) o (st (τ - 1)) (st (τ + 1)) (st τ)

/-- The declared domain of the row, and positivity of `s_π,τ` whose log is also taken. -/
def InDomain (M : ForwardModel S O U) (st : ℕ → S → ℝ) (π : ℕ → U) (τ : ℕ) (o : O) : Prop :=
  LogDefined M.A (M.B (π (τ - 1))) (M.B (π τ)) o (st (τ - 1)) (st (τ + 1)) ∧ ∀ x, 0 < st τ x

section
variable [LinearOrder U] [DecidableEq PolicyIndex]

open Classical in
/-- **The state prediction error at the machine's own inputs.** -/
def machineStatePredictionError (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ : ℕ) :
    Except (ErrorAbsence PolicyIndex) (S → ℝ) :=
  match machineStates M inputsAt world obs t T π plan with
  | .error a => .error (.rollout a)
  | .ok st =>
    if 1 ≤ τ ∧ τ + 1 ≤ T then
      if InDomain M st (plan π) τ (obs τ) then .ok (errorAtStates M st (plan π) τ (obs τ))
      else .error .logUndefined
    else .error .outOfHorizon

/-- **`machineStatePredictionError_eq` — the instantiation.** On the ok arm the error IS
`statePredictionError` at the machine's inputs: the rollout's marginals from the current
belief, the model's `A` and `B` at the policy's actions, the recorded observation. -/
theorem machineStatePredictionError_eq (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ : ℕ) (ε : S → ℝ)
    (h : machineStatePredictionError M inputsAt world obs t T π plan τ = .ok ε) :
    ∃ st, machineStates M inputsAt world obs t T π plan = .ok st ∧
      (1 ≤ τ ∧ τ + 1 ≤ T) ∧ InDomain M st (plan π) τ (obs τ) ∧
      ε = statePredictionError M.A (M.B (plan π (τ - 1))) (M.B (plan π τ)) (obs τ)
            (st (τ - 1)) (st (τ + 1)) (st τ) := by
  unfold machineStatePredictionError at h
  cases hs : machineStates M inputsAt world obs t T π plan with
  | error a => rw [hs] at h; cases h
  | ok st =>
    simp only [hs] at h
    by_cases hτ : 1 ≤ τ ∧ τ + 1 ≤ T
    · by_cases hd : InDomain M st (plan π) τ (obs τ)
      · rw [if_pos hτ, if_pos hd] at h
        have := Except.ok.inj h
        exact ⟨st, rfl, hτ, hd, this.symm⟩
      · rw [if_pos hτ, if_neg hd] at h; cases h
    · rw [if_neg hτ] at h; cases h

/-- An absent rollout gives an absent error, carrying the rollout's absence. -/
theorem machineStatePredictionError_absentRollout (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ : ℕ) (a : RolloutAbsence PolicyIndex)
    (h : machineStates M inputsAt world obs t T π plan = .error a) :
    machineStatePredictionError M inputsAt world obs t T π plan τ = .error (.rollout a) := by
  simp [machineStatePredictionError, h]

/-- A step outside the horizon is refused, not extrapolated. -/
theorem machineStatePredictionError_outOfHorizon (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ : ℕ) (st : ℕ → S → ℝ)
    (hs : machineStates M inputsAt world obs t T π plan = .ok st)
    (hτ : ¬ (1 ≤ τ ∧ τ + 1 ≤ T)) :
    machineStatePredictionError M inputsAt world obs t T π plan τ = .error .outOfHorizon := by
  simp only [machineStatePredictionError, hs]
  rw [if_neg hτ]

/-- **The domain is a refusal, not a default.** Where a log would be taken of a
non-positive probability, the result is `logUndefined`. -/
theorem machineStatePredictionError_logUndefined (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ : ℕ) (st : ℕ → S → ℝ)
    (hs : machineStates M inputsAt world obs t T π plan = .ok st)
    (hτ : 1 ≤ τ ∧ τ + 1 ≤ T) (hd : ¬ InDomain M st (plan π) τ (obs τ)) :
    machineStatePredictionError M inputsAt world obs t T π plan τ = .error .logUndefined := by
  simp [machineStatePredictionError, hs, hτ, hd]

/-- **The states are W4's rollout.** The outcome `machineRollout` returns is `A` applied
to these marginals: the marginals here and the rollout there are the same object. -/
theorem machineRollout_eq_states (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (f : Fin (T + 1) → O → ℝ)
    (h : machineRollout M inputsAt world obs t T π plan = .ok f) :
    ∃ st, machineStates M inputsAt world obs t T π plan = .ok st ∧
      ∀ (τ : Fin (T + 1)) o, f τ o = ∑ s, M.A s o * st τ s := by
  obtain ⟨μ, hd, hμ, hT, hπ, hf⟩ :=
    machineRollout_eq_predictedOutcome M inputsAt world obs t T π plan f h
  refine ⟨fun τ => rolloutState (withBelief M μ hd.1 hd.2) (plan π) τ, ?_, ?_⟩
  · unfold machineStates
    split
    · rename_i a ha; rw [hμ] at ha; cases ha
    · rename_i μ' hμ'
      rw [hμ] at hμ'; cases hμ'
      rw [if_neg hT, if_pos hπ]
  · intro τ o; rw [hf τ o]; rfl

omit [LinearOrder U] in
/-- **At the stationary posterior the error is `ln Z`, at every state** — not `0`. For
the machine's messages (`logMessage` at the rollout's marginals): `ε = ln Σ_y exp(v_y)`,
which is `0` only when the weights already sum to one. -/
theorem errorAtPosterior_eq_logZ [Nonempty S] (M : ForwardModel S O U) (st : ℕ → S → ℝ)
    (π : ℕ → U) (τ : ℕ) (o : O)
    (hdom : LogDefined M.A (M.B (π (τ - 1))) (M.B (π τ)) o (st (τ - 1)) (st (τ + 1))) (x : S) :
    statePredictionError M.A (M.B (π (τ - 1))) (M.B (π τ)) o (st (τ - 1)) (st (τ + 1))
        (statePosterior M.A (M.B (π (τ - 1))) (M.B (π τ)) o (st (τ - 1)) (st (τ + 1))) x
      = Real.log (∑ y, Real.exp (logMessage M.A (M.B (π (τ - 1))) (M.B (π τ)) o
          (st (τ - 1)) (st (τ + 1)) y)) :=
  error_at_posterior M.A (M.B (π (τ - 1))) (M.B (π τ)) o (st (τ - 1)) (st (τ + 1)) hdom x

end

/-! ## The error depends on the policy's B -/

/-- The fixture model: two states, `A` uniform, action `true` with rows `(1/2, 1/2)`,
action `false` with rows `(1/4, 3/4)` (both independent of the source state, so the
rollout after one step is that row whatever the belief). -/
def fxModel : ForwardModel Bool Bool Bool where
  B := fun u _ s' => if u then 1 / 2 else (if s' = true then 3 / 4 else 1 / 4)
  B_nonneg := by intro u s s'; cases u <;> cases s' <;> simp <;> norm_num
  B_rowsum := by intro u s; cases u <;> simp [Fintype.sum_bool] <;> norm_num
  A := fun _ _ => 1 / 2
  A_nonneg := by intro s o; norm_num
  A_colsum := by intro s; simp [Fintype.sum_bool]
  q₀ := fun _ => 1 / 2
  q₀_nonneg := by intro s; norm_num
  q₀_sum := by simp [Fintype.sum_bool]

/-- Under a constant policy on the fixture the marginal at step `n + 1` is the action's row. -/
theorem fx_state_succ (u : Bool) (n : ℕ) (s' : Bool) :
    rolloutState fxModel (fun _ => u) (n + 1) s' = if u then 1 / 2 else (if s' = true then 3 / 4 else 1 / 4) := by
  rw [rolloutState_succ]
  have hB : ∀ s, fxModel.B u s s' = if u then 1 / 2 else (if s' = true then 3 / 4 else 1 / 4) := by
    intro s; rfl
  simp only [hB]
  rw [← Finset.mul_sum, rolloutState_sum, mul_one]

/-- The row `u` puts on the next state. -/
def fxRow (u : Bool) (s' : Bool) : ℝ := if u then 1 / 2 else (if s' = true then 3 / 4 else 1 / 4)

theorem fx_B (u s s' : Bool) : fxModel.B u s s' = fxRow u s' := rfl

theorem fx_A (s o : Bool) : fxModel.A s o = 1 / 2 := rfl

theorem fx_st0 (u : Bool) : rolloutState fxModel (fun _ => u) 0 = fun _ => 1 / 2 := rfl

theorem fx_st1 (u : Bool) : rolloutState fxModel (fun _ => u) 1 = fxRow u :=
  funext (fx_state_succ u 0)

theorem fx_st2 (u : Bool) : rolloutState fxModel (fun _ => u) 2 = fxRow u :=
  funext (fx_state_succ u 1)

theorem fxRow_pos (u s' : Bool) : 0 < fxRow u s' := by
  cases u <;> cases s' <;> simp [fxRow] <;> norm_num

theorem fx_inDomain (u : Bool) :
    InDomain fxModel (rolloutState fxModel (fun _ => u)) (fun _ => u) 1 true := by
  refine ⟨⟨fun x => by rw [fx_A]; norm_num, fun s₀ x _ => by rw [fx_B]; exact fxRow_pos u x,
    fun x s₁ _ => by rw [fx_B]; exact fxRow_pos u s₁⟩, fun x => ?_⟩
  show 0 < rolloutState fxModel (fun _ => u) 1 x
  rw [fx_st1]; exact fxRow_pos u x

/-- **`wrongRolloutChangesTheError`.** Two policies with different `B`, the same belief and
the same observation, give different errors at the same step and state. On the fixture, the
error at step 1 is `ln(1/2) + Σ b ln b − ln(1/2) ... = ln A + Σ b ln b` for the row `b`:
`−ln 2 − ln 2` for the uniform row against `−ln 2 − H(1/4, 3/4)`, and `H(1/4,3/4) ≠ ln 2`
because `3 ln 3 ≠ 4 ln 2` (27 ≠ 16). Both are inside the row's domain. -/
theorem wrongRolloutChangesTheError :
    InDomain fxModel (rolloutState fxModel (fun _ => true)) (fun _ => true) 1 true ∧
    InDomain fxModel (rolloutState fxModel (fun _ => false)) (fun _ => false) 1 true ∧
    errorAtStates fxModel (rolloutState fxModel (fun _ => true)) (fun _ => true) 1 true true
      ≠ errorAtStates fxModel (rolloutState fxModel (fun _ => false)) (fun _ => false) 1 true true := by
  refine ⟨fx_inDomain true, fx_inDomain false, ?_⟩
  have e1 : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
  have e3 : Real.log (1 / 4) = -2 * Real.log 2 := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have e2 : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  intro h
  simp only [errorAtStates, statePredictionError, logMessage, likTerm, pastTerm, futureTerm,
    show (1 : ℕ) - 1 = 0 from rfl, show (1 : ℕ) + 1 = 2 from rfl, fx_st0, fx_st1, fx_st2, fx_B,
    fx_A, Fintype.sum_bool, fxRow] at h
  norm_num [e1, e2, e3] at h
  have h3 : 3 * Real.log 3 = 4 * Real.log 2 := by linarith
  have h4 : Real.log (3 ^ 3) = Real.log (2 ^ 4) := by
    rw [Real.log_pow, Real.log_pow]; push_cast; linarith
  have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by norm_num)) (Set.mem_Ioi.mpr (by norm_num)) h4
  norm_num at this

end

#print axioms ErrorAbsence
#print axioms machineStates
#print axioms errorAtStates
#print axioms InDomain
#print axioms machineStatePredictionError
#print axioms machineStatePredictionError_eq
#print axioms machineStatePredictionError_absentRollout
#print axioms machineStatePredictionError_outOfHorizon
#print axioms machineStatePredictionError_logUndefined
#print axioms machineRollout_eq_states
#print axioms errorAtPosterior_eq_logZ
#print axioms fxModel
#print axioms fx_state_succ
#print axioms fxRow
#print axioms fx_inDomain
#print axioms wrongRolloutChangesTheError

end DarkTower.WarMachine.Proof2.StatePredictionErrorAtMachine
