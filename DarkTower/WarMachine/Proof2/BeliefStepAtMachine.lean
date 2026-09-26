import DarkTower.WarMachine.ExactBeliefTrajectory
import DarkTower.WarMachine.ObservationProcess
import DarkTower.WarMachine.BeliefTrajectory
import DarkTower.WarMachine.Proof2.ActionAtMachine
import DarkTower.WarMachine.Proof2.ObservationAtMachine

/-!
# One step of the machine's closed loop (W3b, registry `:state-belief-update`, R3)

`machineStep` is the belief UPDATE at the machine's own action and observation: W2's
`machineAction`, the process's law for the realised observation, then
`ExactBeliefTrajectory.exactUpdate` at the transition row of the action. It was
introduced in `BeliefAtMachine` (W3, mathlib4 `a53e948d45`) and is split out here so
that the trajectory module (`BeliefAtMachine`, R1) and the update module (this one,
R3) are different modules: a consumer of the trajectory (the rollout, R1→R4) then
imports a module placed at R1 only, not one shared by R1 and R3.

Every declaration here is moved from `BeliefAtMachine` unchanged; nothing in the
statements or proofs differs. See `BeliefAtMachine` for what is supplied (realised
world states and observations are inputs, checked, never drawn) and for the typed
absences.
-/

namespace DarkTower.WarMachine.Proof2.BeliefStepAtMachine

open DarkTower.WarMachine
open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.ExactBeliefTrajectory
open DarkTower.WarMachine.ObservationProcess
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
open DarkTower.WarMachine.Proof2.ActionAtMachine
open DarkTower.WarMachine.Proof2.ObservationAtMachine

noncomputable section

variable {S O U PolicyIndex : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- Why a step of the loop produced no belief. Each arm names what is missing. -/
inductive StepAbsence (PolicyIndex : Type*) where
  | noAction (a : Absence PolicyIndex)
  | processImpossible
  | updateRefused

/-- **One step of the closed loop** from belief `μ` at time `t`: the machine's action,
the process's law for the realised observation `obs (t+1)` from the realised world
`world t`, then `exactUpdate` of `μ` by the action's transition row and that
observation. No arm substitutes a default action, observation or belief. -/
def machineStep [LinearOrder U] (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t : ℕ) (μ : S → ℝ) :
    Except (StepAbsence PolicyIndex) (S → ℝ) :=
  match machineObservationLaw M (inputsAt t μ) (world t) with
  | .error a => .error (.noAction a)
  | .ok (u, law) =>
    if law (obs (t + 1)) = 0 then .error .processImpossible
    else
      match exactUpdate M.A (M.B u) (obs (t + 1)) μ with
      | none => .error .updateRefused
      | some μ' => .ok μ'

variable [LinearOrder U]
  (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
  (world : ℕ → S) (obs : ℕ → O)

/-- Inverting an ok step: an action, a law giving the observation positive
probability, and an update that returned. -/
theorem machineStep_ok (t : ℕ) (μ μ' : S → ℝ)
    (h : machineStep M inputsAt world obs t μ = .ok μ') :
    ∃ u law, machineObservationLaw M (inputsAt t μ) (world t) = .ok (u, law) ∧
      law (obs (t + 1)) ≠ 0 ∧ exactUpdate M.A (M.B u) (obs (t + 1)) μ = some μ' := by
  unfold machineStep at h
  cases hl : machineObservationLaw M (inputsAt t μ) (world t) with
  | error a => simp [hl] at h
  | ok p =>
    obtain ⟨u, law⟩ := p
    simp only [hl] at h
    by_cases hz : law (obs (t + 1)) = 0
    · simp [hz] at h
    · simp only [hz, if_false] at h
      cases hu : exactUpdate M.A (M.B u) (obs (t + 1)) μ with
      | none => simp [hu] at h
      | some μ'' =>
        simp only [hu, Except.ok.injEq] at h
        subst h
        exact ⟨u, law, rfl, hz, hu⟩

/-! ## The refusals are reachable -/

/-- **`impossibleObservationRefuses`, the step.** An observation the process can yield
after the machine's action, but that has predictive probability zero under the belief,
stops the step with `updateRefused`. It is `exactUpdate`'s own refusal
(`exactUpdate_eq_none_iff`), carried typed. -/
theorem machineStep_updateRefused (t : ℕ) (μ : S → ℝ) (u : U) (law : O → ℝ)
    (hlaw : machineObservationLaw M (inputsAt t μ) (world t) = .ok (u, law))
    (hpos : law (obs (t + 1)) ≠ 0)
    (hz : observationProbability M.A (M.B u) (obs (t + 1)) μ = 0) :
    machineStep M inputsAt world obs t μ = .error .updateRefused := by
  have hn : exactUpdate M.A (M.B u) (obs (t + 1)) μ = none :=
    (exactUpdate_eq_none_iff M.A (M.B u) (obs (t + 1)) μ).mpr hz
  simp [machineStep, hlaw, hpos, hn]

/-- An observation the process cannot yield after the machine's action is refused
BEFORE the update, with its own absence. -/
theorem machineStep_processImpossible (t : ℕ) (μ : S → ℝ) (u : U) (law : O → ℝ)
    (hlaw : machineObservationLaw M (inputsAt t μ) (world t) = .ok (u, law))
    (hz : law (obs (t + 1)) = 0) :
    machineStep M inputsAt world obs t μ = .error .processImpossible := by
  simp [machineStep, hlaw, hz]

/-- **An absent action stops the loop**, with the posterior's own absence and no
default action. -/
theorem machineStep_noAction (t : ℕ) (μ : S → ℝ) (a : Absence PolicyIndex)
    (h : actionAt (inputsAt t μ) = .error a) :
    machineStep M inputsAt world obs t μ = .error (.noAction a) := by
  simp [machineStep, machineObservationLaw, h]

/-! ## The machine's action is doing something in the update -/

/-- When the process yields the observation, the step's belief is `exactUpdate` at the
transition row of the machine's own action, and nothing else. -/
theorem machineStep_eq_update (t : ℕ) (μ : S → ℝ) (u : U) (law : O → ℝ)
    (hlaw : machineObservationLaw M (inputsAt t μ) (world t) = .ok (u, law))
    (hpos : law (obs (t + 1)) ≠ 0) (μ' : S → ℝ)
    (h : exactUpdate M.A (M.B u) (obs (t + 1)) μ = some μ') :
    machineStep M inputsAt world obs t μ = .ok μ' := by
  simp [machineStep, hlaw, hpos, h]

/-- **`wrongActionChangesTheBelief`.** From the same belief and the same observation,
two actions with different `B` rows give different next beliefs: from a point mass at
`false` observed `true` with the noisy likelihood, flipping gives the point mass at
`true` and keeping gives the point mass at `false`. A trajectory that ignored `u`
could not satisfy this; together with `machineStep_eq_update` it says the machine's
action is what selects the row. -/
theorem wrongActionChangesTheBelief :
    exactUpdate BeliefTrajectory.fxAnoisy (BeliefTrajectory.fxB true) true
        (fun s => if s = false then 1 else 0)
      = some (fun x => if x = true then 1 else 0) ∧
    exactUpdate BeliefTrajectory.fxAnoisy (BeliefTrajectory.fxB false) true
        (fun s => if s = false then 1 else 0)
      = some (fun x => if x = false then 1 else 0) ∧
    exactUpdate BeliefTrajectory.fxAnoisy (BeliefTrajectory.fxB true) true
        (fun s => if s = false then 1 else 0)
      ≠ exactUpdate BeliefTrajectory.fxAnoisy (BeliefTrajectory.fxB false) true
        (fun s => if s = false then 1 else 0) := by
  have h1 : exactUpdate BeliefTrajectory.fxAnoisy (BeliefTrajectory.fxB true) true
        (fun s => if s = false then 1 else 0)
      = some (fun x => if x = true then 1 else 0) := by
    unfold exactUpdate
    have hobs : observationProbability BeliefTrajectory.fxAnoisy (BeliefTrajectory.fxB true) true
        (fun s => if s = false then (1 : ℝ) else 0) = 9 / 10 := by
      simp [observationProbability, predictedState, BeliefTrajectory.fxAnoisy,
        BeliefTrajectory.fxB]
    rw [hobs, if_neg (by norm_num)]
    congr 1
    funext x
    cases x <;> simp [predictedState, BeliefTrajectory.fxAnoisy, BeliefTrajectory.fxB]
  have h2 : exactUpdate BeliefTrajectory.fxAnoisy (BeliefTrajectory.fxB false) true
        (fun s => if s = false then 1 else 0)
      = some (fun x => if x = false then 1 else 0) := by
    unfold exactUpdate
    have hobs : observationProbability BeliefTrajectory.fxAnoisy (BeliefTrajectory.fxB false) true
        (fun s => if s = false then (1 : ℝ) else 0) = 1 / 10 := by
      simp [observationProbability, predictedState, BeliefTrajectory.fxAnoisy,
        BeliefTrajectory.fxB]
    rw [hobs, if_neg (by norm_num)]
    congr 1
    funext x
    cases x <;> simp [predictedState, BeliefTrajectory.fxAnoisy, BeliefTrajectory.fxB]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  intro h
  have := congrFun (Option.some.inj h) true
  simp at this

/-- **The refusal has an input.** The certain-observation likelihood, the keeping
action, a point mass at `false`, observed `true`: predictive probability zero, so
`exactUpdate` is `none` — the input of `BeliefTrajectory.fixture_impossible_refused`
run through the exact update. -/
theorem fixtureImpossibleRefused :
    exactUpdate (fun (s : Bool) (ob : Bool) => if s = ob then (1 : ℝ) else 0)
      (BeliefTrajectory.fxB false) true (fun s => if s = false then 1 else 0) = none := by
  rw [exactUpdate_eq_none_iff]
  simp [observationProbability, predictedState, BeliefTrajectory.fxB]

end

#print axioms StepAbsence
#print axioms machineStep
#print axioms machineStep_ok
#print axioms machineStep_updateRefused
#print axioms machineStep_processImpossible
#print axioms machineStep_noAction
#print axioms machineStep_eq_update
#print axioms wrongActionChangesTheBelief
#print axioms fixtureImpossibleRefused

end DarkTower.WarMachine.Proof2.BeliefStepAtMachine
