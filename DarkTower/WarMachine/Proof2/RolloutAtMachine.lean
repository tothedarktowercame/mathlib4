import DarkTower.WarMachine.PolicyRollout
import DarkTower.WarMachine.PolicyHorizon
import DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
import DarkTower.WarMachine.Proof2.ObservationAtMachine
import DarkTower.WarMachine.Proof2.BeliefAtMachine

/-!
# The rollout from the machine's CURRENT belief (W4, registry `:forward-model`)

What the row says. `:forward-model`'s `:formal` is
`Q(o|π) := Σ_s A(o|s) Q(s|π), Q(s|π) rolled forward by B from μ over depth T`, its
`:latex` starts the rollout at `Q(s_0|π) = μ`, and `:imports` is `[:mu :A :B :pi :T]`.
So the row starts the rollout from the belief `μ`, not from a model constant. (The
`:depth` row's own `:formal` still writes `Q(s_0|π) = q0` for the same rollout; the
two rows disagree about the start, and this module follows `:forward-model`, the row
that owns the rollout.)

What the Lean had. `PolicyRollout.predictedOutcome M π n` rolls forward from `M.q₀`,
a field of the model. Nothing put the machine's current belief there, so the registry
edge R1→R4 (`μ`) was absent; R13→R4 (`T`, the depth of `PolicyHorizon.horizonEFE`) and
R6→R4 (`π`, the machine's policy set) were parametric.

This module applies the rollout to the machine's own terms: the belief is the value
of W3's `machineTrajectory` at time `t` (a distribution, by
`machineTrajectory_isDistribution`), the policy is one of the machine's policy list
`(inputsAt t μ).policies` (W1's list, the one the posterior is over), and the depth
`T` is the one `horizonEFE` takes.

* `withBelief M μ` is `M` with `q₀ := μ`; `predictedOutcome (withBelief M μ) π n` is the
  rollout from `μ`. The rollout `machineRollout` returns is that family for
  `τ = 0..T`.
* **`T = 0` is a refusal**, `RolloutAbsence.zeroDepth`, not an empty rollout: the depth
  binder of `horizonEFE` is `0 < T` (`policySeq` has no last action to pad with at depth
  zero), so a depth-zero policy is not one the row's depth admits.
* No default belief, policy or horizon on any arm: an absent belief gives an absent
  rollout carrying the belief's own absence; a policy not in the machine's list is
  refused (`notInPolicySet`).
* `plan π : ℕ → U` is the policy's action sequence. Only its first `T` entries are read
  (`PolicyRollout.rolloutAt_eq_of_extends`).

NOT done here: `:r`, the containment order, enters R4 through the
`:co-application-kernel` row (its own module, `Proof2/CoApplicationKernel`), not through
`:forward-model`, whose `:imports` do not include it.
-/

namespace DarkTower.WarMachine.Proof2.RolloutAtMachine

open DarkTower.WarMachine
open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
open DarkTower.WarMachine.Proof2.ObservationAtMachine
open DarkTower.WarMachine.Proof2.BeliefAtMachine

noncomputable section

variable {S O U PolicyIndex : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- The model started from the belief `μ`: `q₀ := μ`. -/
def withBelief (M : ForwardModel S O U) (μ : S → ℝ) (h0 : ∀ s, 0 ≤ μ s)
    (h1 : ∑ s, μ s = 1) : ForwardModel S O U :=
  { M with q₀ := μ, q₀_nonneg := h0, q₀_sum := h1 }

/-- Why there is no rollout. Each arm names what is missing. -/
inductive RolloutAbsence (PolicyIndex : Type*) where
  | belief (a : StepAbsence PolicyIndex)
  | zeroDepth
  | notInPolicySet

section
variable [LinearOrder U] [DecidableEq PolicyIndex]

open Classical in
/-- **The predicted outcome distribution over the horizon, from the machine's current
belief.** `τ ↦ Q(o_τ | π)` for `τ = 0..T`, at the belief `machineTrajectory … t`, the
policy `π` from the machine's own list, and depth `T`. -/
def machineRollout (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t : ℕ) (T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) :
    Except (RolloutAbsence PolicyIndex) (Fin (T + 1) → O → ℝ) :=
  match h : machineTrajectory M inputsAt world obs t with
  | .error a => .error (.belief a)
  | .ok μ =>
    if T = 0 then .error .zeroDepth
    else if π ∈ (inputsAt t μ).policies then
      .ok fun τ o => predictedOutcome
        (withBelief M μ (machineTrajectory_isDistribution M inputsAt world obs t μ h).1
          (machineTrajectory_isDistribution M inputsAt world obs t μ h).2)
        (plan π) τ o
    else .error .notInPolicySet

end

/-- **The predicted outcome at the machine's current belief is `predictedOutcome` at
that belief.** On the ok arm the belief is `machineTrajectory … t`, and every
`τ`, `o` entry is `predictedOutcome` of the model started there. The parametric
declaration applied to the machine's own terms. -/
theorem machineRollout_eq_predictedOutcome [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (f : Fin (T + 1) → O → ℝ)
    (hrun : machineRollout M inputsAt world obs t T π plan = .ok f) :
    ∃ μ, ∃ hd : (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1,
      machineTrajectory M inputsAt world obs t = .ok μ ∧ T ≠ 0 ∧
      π ∈ (inputsAt t μ).policies ∧
      ∀ τ o, f τ o = predictedOutcome (withBelief M μ hd.1 hd.2) (plan π) τ o := by
  unfold machineRollout at hrun
  split at hrun
  · simp at hrun
  · rename_i μ hμ
    by_cases hT : T = 0
    · rw [if_pos hT] at hrun; cases hrun
    · by_cases hπ : π ∈ (inputsAt t μ).policies
      · rw [if_neg hT, if_pos hπ] at hrun
        have hf := Except.ok.inj hrun
        subst hf
        exact ⟨μ, machineTrajectory_isDistribution M inputsAt world obs t μ hμ, hμ, hT, hπ,
          fun τ o => rfl⟩
      · rw [if_neg hT, if_neg hπ] at hrun; cases hrun

/-- **`machineRollout_startsAtCurrentBelief`.** The step-0 state is the current belief,
not `q₀`: the step-0 outcome is `Σ_s A(s,o) μ(s)` for `μ` the machine's belief at `t`. -/
theorem machineRollout_startsAtCurrentBelief [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (f : Fin (T + 1) → O → ℝ)
    (hrun : machineRollout M inputsAt world obs t T π plan = .ok f) :
    ∃ μ, machineTrajectory M inputsAt world obs t = .ok μ ∧
      ∀ o, f 0 o = ∑ s, M.A s o * μ s := by
  obtain ⟨μ, hd, hμ, _, _, hf⟩ := machineRollout_eq_predictedOutcome M inputsAt world obs t T π
    plan f hrun
  refine ⟨μ, hμ, fun o => ?_⟩
  rw [hf 0 o]
  rfl

/-- **The bad case of the absent edge.** A rollout from the model's `q₀` and a rollout
from a different belief start at different states: if `μ ≠ q₀`, step 0 differs. A
rollout that ignored the current belief could not satisfy this. -/
theorem rolloutFromQ0_ne_rolloutFromBelief (M : ForwardModel S O U) (μ : S → ℝ)
    (h0 : ∀ s, 0 ≤ μ s) (h1 : ∑ s, μ s = 1) (hne : μ ≠ M.q₀) (π : ℕ → U) :
    rolloutState (withBelief M μ h0 h1) π 0 ≠ rolloutState M π 0 := by
  simpa [rolloutState, withBelief] using hne

/-- And at the OUTCOME: on a two-state model with the identity likelihood and the
keeping action, the model's `q₀` (a point mass at `false`) predicts outcome `true` at
step 1 with probability `0`, while the belief that is a point mass at `true` predicts
it with probability `1`. -/
theorem rolloutFromBelief_changes_the_outcome :
    ∃ (M : ForwardModel Bool Bool Bool) (μ : Bool → ℝ) (h0 : ∀ s, 0 ≤ μ s) (h1 : ∑ s, μ s = 1),
      predictedOutcome M (fun _ => true) 1 true = 0 ∧
      predictedOutcome (withBelief M μ h0 h1) (fun _ => true) 1 true = 1 := by
  let M : ForwardModel Bool Bool Bool :=
    { B := fun _ s s' => if s' = s then 1 else 0
      B_nonneg := by intro u s s'; split_ifs <;> norm_num
      B_rowsum := by intro u s; cases s <;> simp
      A := fun s o => if s = o then 1 else 0
      A_nonneg := by intro s o; split_ifs <;> norm_num
      A_colsum := by intro s; cases s <;> simp
      q₀ := fun s => if s = false then 1 else 0
      q₀_nonneg := by intro s; split_ifs <;> norm_num
      q₀_sum := by simp }
  refine ⟨M, fun s => if s = true then 1 else 0, by intro s; dsimp only; split_ifs <;> norm_num,
    by simp, ?_, ?_⟩
  · simp [predictedOutcome, rolloutState, M]
  · simp [predictedOutcome, rolloutState, withBelief, M]

/-- **Each step is a distribution**, inherited from `PolicyRollout`. -/
theorem machineRollout_isDistribution [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (f : Fin (T + 1) → O → ℝ)
    (hrun : machineRollout M inputsAt world obs t T π plan = .ok f) (τ : Fin (T + 1)) :
    (∀ o, 0 ≤ f τ o) ∧ ∑ o, f τ o = 1 := by
  obtain ⟨μ, hd, _, _, _, hf⟩ := machineRollout_eq_predictedOutcome M inputsAt world obs t T π
    plan f hrun
  refine ⟨fun o => ?_, ?_⟩
  · rw [hf τ o]; exact predictedOutcome_nonneg _ _ _ _
  · simp only [hf τ]; exact predictedOutcome_sum _ _ _

/-! ## The absences, carried and reachable -/

theorem machineRollout_absentBelief [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (a : StepAbsence PolicyIndex)
    (h : machineTrajectory M inputsAt world obs t = .error a) :
    machineRollout M inputsAt world obs t T π plan = .error (.belief a) := by
  unfold machineRollout
  split
  · rename_i a' ha'; rw [h] at ha'; cases ha'; rfl
  · rename_i μ hμ; rw [h] at hμ; cases hμ

theorem machineRollout_zeroDepth [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (μ : S → ℝ)
    (h : machineTrajectory M inputsAt world obs t = .ok μ) :
    machineRollout M inputsAt world obs t 0 π plan = .error .zeroDepth := by
  unfold machineRollout
  split
  · rename_i a ha; rw [h] at ha; cases ha
  · simp

theorem machineRollout_notInPolicySet [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (μ : S → ℝ) (hT : T ≠ 0)
    (h : machineTrajectory M inputsAt world obs t = .ok μ)
    (hπ : π ∉ (inputsAt t μ).policies) :
    machineRollout M inputsAt world obs t T π plan = .error .notInPolicySet := by
  unfold machineRollout
  split
  · rename_i a ha; rw [h] at ha; cases ha
  · rename_i μ' hμ'
    rw [h] at hμ'; cases hμ'
    simp [hT, hπ]

/-- **The horizon, as `PolicyHorizon` binds it.** The expected free energy of the
depth-`T` policy at the machine's current belief: `horizonEFE` (`0 < T`, the depth
binder the row's `:depth` names) on the model started from `μ`. -/
def machineHorizonEFE (M : ForwardModel S O U) (μ : S → ℝ) (h0 : ∀ s, 0 ≤ μ s)
    (h1 : ∑ s, μ s = 1) {T : ℕ} (hT : 0 < T) (π : Fin T → U) (C : ℕ → O → ℝ) : EReal :=
  PolicyHorizon.horizonEFE (withBelief M μ h0 h1) hT π C

end

#print axioms withBelief
#print axioms RolloutAbsence
#print axioms machineRollout
#print axioms machineRollout_eq_predictedOutcome
#print axioms machineRollout_startsAtCurrentBelief
#print axioms rolloutFromQ0_ne_rolloutFromBelief
#print axioms rolloutFromBelief_changes_the_outcome
#print axioms machineRollout_isDistribution
#print axioms machineRollout_absentBelief
#print axioms machineRollout_zeroDepth
#print axioms machineRollout_notInPolicySet
#print axioms machineHorizonEFE

end DarkTower.WarMachine.Proof2.RolloutAtMachine
