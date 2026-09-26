import DarkTower.WarMachine.ExactBeliefTrajectory
import DarkTower.WarMachine.ObservationProcess
import DarkTower.WarMachine.BeliefTrajectory
import DarkTower.WarMachine.Proof2.ActionAtMachine
import DarkTower.WarMachine.Proof2.ObservationAtMachine
import DarkTower.WarMachine.Proof2.BeliefStepAtMachine

/-!
# The closed-loop belief trajectory at the machine's own action (W3)

Registry rows `:belief-state` (R1), `:state-belief-update` (R3), `:observe` (R2).
`ExactBeliefTrajectory.exactBeliefAt` takes the action sequence `u` and the
observation sequence `o` as FREE PARAMETERS, and `ObservationProcess.observationAfter`
takes the action and the world as free arguments. Nothing in Lean supplied the
MACHINE's action (W2, `ActionAtMachine.machineAction`) or checked an observation
against what the process yields after it, so the registry edges R16→R1 (`u` into the
belief), R2→R1 and R2→R3 (`o` into the belief and its update) and R16→R2 (`u` and the
world into the observation) had the term in the consumer's signature and no import
behind it. This module is that application.

`machineObservationLaw` (the machine's action and the process's law for it, R16→R2)
lives in `Proof2/ObservationAtMachine.lean`, which this module imports, so the
observation's edges into the belief cross a module boundary.

`machineStep` (the update, R3) and `StepAbsence` live in
`Proof2/BeliefStepAtMachine.lean` (W3b), which this module imports, so this module is
placed at R1 (the trajectory) and the step module at R3.

## What is supplied and what is not

`observationAfter M w u o` is a PROBABILITY, `P(o | s_{t−1} = w, u)`, not an
observation. The observation itself is a realised draw, and no function in Lean
produces one. So the loop takes the realised world states `world : ℕ → S` and the
realised observations `obs : ℕ → O` as inputs, and what it does with them is CHECK:
an observation the process gives probability zero after the machine's action is
refused (`StepAbsence.processImpossible`), not absorbed. Nothing here draws an
observation, and none is defaulted.

The belief update uses the same `M.A` and `M.B` as the process. The identification
of the agent's model with the process is the stack assumption declared in
`ObservationProcess` (finite categorical process of the same form as eq. 2.1); it is
not proved here.

The policy inputs to `machineAction` (habit, grade, F, temperature options, the
policy list and each policy's head action) may depend on the time and on the current
belief (`inputsAt`), which is what closes the loop: the belief feeds the policy
posterior, the posterior gives the action, the action selects the transition row that
updates the belief.

## The absences, all typed

* `noAction a`: the machine's posterior (W1/W1b) was absent, so there is no action;
* `processImpossible`: the process gives the realised observation probability zero
  after the machine's action from the realised world;
* `updateRefused`: the observation has predictive probability zero under the belief's
  prediction, which is exactly when `exactUpdate` returns `none`
  (`exactUpdate_eq_none_iff`).
-/

namespace DarkTower.WarMachine.Proof2.BeliefAtMachine

open DarkTower.WarMachine
open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.ExactBeliefTrajectory
open DarkTower.WarMachine.ObservationProcess
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
open DarkTower.WarMachine.Proof2.ActionAtMachine
open DarkTower.WarMachine.Proof2.ObservationAtMachine
open DarkTower.WarMachine.Proof2.BeliefStepAtMachine

noncomputable section

variable {S O U PolicyIndex : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- **The `n`-step closed loop** from `μ_0 = q₀`. -/
def machineTrajectory [LinearOrder U] (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) : ℕ → Except (StepAbsence PolicyIndex) (S → ℝ)
  | 0 => .ok M.q₀
  | n + 1 => (machineTrajectory M inputsAt world obs n).bind
      (machineStep M inputsAt world obs n)

variable [LinearOrder U]
  (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
  (world : ℕ → S) (obs : ℕ → O)

theorem machineTrajectory_succ_ok (n : ℕ) (μ : S → ℝ)
    (h : machineTrajectory M inputsAt world obs (n + 1) = .ok μ) :
    ∃ μn, machineTrajectory M inputsAt world obs n = .ok μn ∧
      machineStep M inputsAt world obs n μn = .ok μ := by
  have h' : (machineTrajectory M inputsAt world obs n).bind
      (machineStep M inputsAt world obs n) = .ok μ := h
  cases hn : machineTrajectory M inputsAt world obs n with
  | error a =>
    rw [hn] at h'
    exact absurd h' (by simp [Except.bind])
  | ok μn =>
    rw [hn] at h'
    exact ⟨μn, rfl, h'⟩

/-- **`machineTrajectory_eq_exactBeliefAt` — the instantiation.** On the all-ok arm the
closed loop IS `exactBeliefAt` at an action sequence `us` that is the machine's own:
at every earlier step `t`, `us t` is the action `machineAction` returned at that step's
belief, and the process gave the realised observation positive probability after it.
The parametric declaration applied to the machine's own terms.

`[Nonempty U]` is needed only to write down `us` at `n = 0`, where no action has been
taken; the action at any step that happened is the machine's, never a default. -/
theorem machineTrajectory_eq_exactBeliefAt [Nonempty U] :
    ∀ (n : ℕ) (μ : S → ℝ), machineTrajectory M inputsAt world obs n = .ok μ →
      ∃ us : ℕ → U, exactBeliefAt M.A M.B M.q₀ us obs n = some μ ∧
        ∀ t < n, ∃ μt law, exactBeliefAt M.A M.B M.q₀ us obs t = some μt ∧
          machineObservationLaw M (inputsAt t μt) (world t) = .ok (us t, law) ∧
          law (obs (t + 1)) ≠ 0
  | 0, μ, h => by
    simp only [machineTrajectory, Except.ok.injEq] at h
    subst h
    exact ⟨fun _ => Classical.arbitrary U, rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | n + 1, μ, h => by
    obtain ⟨μn, hn, hs⟩ := machineTrajectory_succ_ok M inputsAt world obs n μ h
    obtain ⟨us, hb, hall⟩ := machineTrajectory_eq_exactBeliefAt n μn hn
    obtain ⟨u, law, hlaw, hpos, hup⟩ := machineStep_ok M inputsAt world obs n μn μ hs
    classical
    let us' : ℕ → U := fun t => if t < n then us t else u
    have hagree : ∀ t, t ≤ n → exactBeliefAt M.A M.B M.q₀ us' obs t
        = exactBeliefAt M.A M.B M.q₀ us obs t := fun t ht =>
      exactBeliefAt_congr M.A M.B M.q₀ t
        (fun m hm => by simp [us', show m < n by omega]) (fun m _ => rfl)
    have hu'n : us' n = u := by simp [us']
    refine ⟨us', ?_, ?_⟩
    · rw [exactBeliefAt_succ, hagree n le_rfl, hb, Option.bind_some, hu'n]
      exact hup
    · intro t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
      · obtain ⟨μt, law', h1, h2, h3⟩ := hall t hlt
        refine ⟨μt, law', by rw [hagree t hlt.le]; exact h1, ?_, h3⟩
        have : us' t = us t := by simp [us', hlt]
        rw [this]; exact h2
      · refine ⟨μn, law, by rw [hagree t le_rfl]; exact hb, ?_, hpos⟩
        rw [hu'n]; exact hlaw

/-- **Each step is a distribution.** The hypotheses are the forward model's own. -/
theorem machineTrajectory_isDistribution :
    ∀ (n : ℕ) (μ : S → ℝ), machineTrajectory M inputsAt world obs n = .ok μ →
      (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1
  | 0, μ, h => by
    simp only [machineTrajectory, Except.ok.injEq] at h
    subst h
    exact ⟨M.q₀_nonneg, M.q₀_sum⟩
  | n + 1, μ, h => by
    obtain ⟨μn, hn, hs⟩ := machineTrajectory_succ_ok M inputsAt world obs n μ h
    obtain ⟨u, law, _, _, hup⟩ := machineStep_ok M inputsAt world obs n μn μ hs
    have hd := machineTrajectory_isDistribution n μn hn
    exact exactUpdate_dist M.A (M.B u) (obs (n + 1)) μn (fun x => M.A_nonneg x _)
      (M.B_nonneg u) hd.1 hup

/-- **And the trajectory stops there**: no belief is carried past the refusal. -/
theorem impossibleObservationRefuses (n : ℕ) (μ : S → ℝ) (u : U) (law : O → ℝ)
    (hn : machineTrajectory M inputsAt world obs n = .ok μ)
    (hlaw : machineObservationLaw M (inputsAt n μ) (world n) = .ok (u, law))
    (hpos : law (obs (n + 1)) ≠ 0)
    (hz : observationProbability M.A (M.B u) (obs (n + 1)) μ = 0) :
    machineTrajectory M inputsAt world obs (n + 1) = .error .updateRefused := by
  show (machineTrajectory M inputsAt world obs n).bind (machineStep M inputsAt world obs n) = _
  rw [hn]
  exact machineStep_updateRefused M inputsAt world obs n μ u law hlaw hpos hz

end

#print axioms machineTrajectory
#print axioms machineTrajectory_succ_ok
#print axioms machineTrajectory_eq_exactBeliefAt
#print axioms machineTrajectory_isDistribution
#print axioms impossibleObservationRefuses

end DarkTower.WarMachine.Proof2.BeliefAtMachine
