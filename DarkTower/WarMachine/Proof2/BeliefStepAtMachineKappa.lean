import DarkTower.WarMachine.Proof2.BeliefStepAtMachine
import DarkTower.WarMachine.MachineBeliefUpdateNormalised

/-!
# The machine's step at the live precision κ (contract C2)

`BeliefStepAtMachine.machineStep` updates with `ExactBeliefTrajectory.exactUpdate`, the
untempered Bayes update. The live update (futon2 `belief.clj` `update-step`, since
`5df5853ea`) tempers the likelihood with a precision κ and renormalises each state's
column over outcomes; that update is specified by
`MachineBeliefUpdateNormalised.normalisedUpdate` (mathlib4 `e51605fa2d`). This module
states the machine's step with that update, at a supplied κ:

* `machineStepAt κ` — the same arms as `machineStep` (the machine's action, the
  process's law for the realised observation, refusal of an observation the process
  gives probability zero), with the update `normalisedUpdate κ A` applied to the
  predicted state `B_u μ`. The update's own refusals are carried typed.
* `machineStepAt_eq_update` — on success the belief is exact Bayes conditioning of the
  predicted state with the precision likelihood at κ (C2: "the next belief is the exact
  Bayes update on the realised observation", at the live likelihood).
* `machineStepAt_one_eq_machineStep` — at κ = 1, for a positive column-stochastic `A`,
  an ok step equals `machineStep`'s ok step. So `machineStep` is the κ = 1 case and the
  theorems proved about it (`machineStep_eq_update`, `wrongActionChangesTheBelief`) are
  about that case only.
* `machineStepAt_updateRefused` — an update refusal stops the step; no default belief.

κ is a supplied input. The machine's κ from an event weight is
`MachineBeliefUpdate.kappa` (`normalisedUpdateFromWeight_uses_machineKappa`). That the
tempered step differs from the untempered one is `categoricalUpdate_not_always_normalised`'s
2×2 case at the update level (κ = 2 gives 5/14, not the untempered value); it is not
restated here for a whole step.
-/

namespace DarkTower.WarMachine.Proof2.BeliefStepAtMachineKappa

open DarkTower.WarMachine
open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.ExactBeliefTrajectory
open DarkTower.WarMachine.ObservationProcess
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
open DarkTower.WarMachine.Proof2.ActionAtMachine
open DarkTower.WarMachine.Proof2.ObservationAtMachine
open DarkTower.WarMachine.Proof2.BeliefStepAtMachine
open DarkTower.WarMachine.MachineBeliefUpdateNormalised

noncomputable section

variable {S O U PolicyIndex : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- Why a step at κ produced no belief. The update arm carries the update's own
refusal (`invalidKappa`, `zeroTemperedColumn`, `zeroEvidence`). -/
inductive StepAbsenceAt (PolicyIndex : Type*) where
  | noAction (a : Absence PolicyIndex)
  | processImpossible
  | updateRefused (e : UpdateError)

/-- **One step of the closed loop at precision κ**: the machine's action, the process's
law for the realised observation, then `normalisedUpdate κ A` of the predicted state
`B_u μ` on that observation. No arm substitutes a default. -/
def machineStepAt [LinearOrder U] (kappa : ℝ) (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t : ℕ) (μ : S → ℝ) :
    Except (StepAbsenceAt PolicyIndex) (S → ℝ) :=
  match machineObservationLaw M (inputsAt t μ) (world t) with
  | .error a => .error (.noAction a)
  | .ok (u, law) =>
    if law (obs (t + 1)) = 0 then .error .processImpossible
    else
      match normalisedUpdate kappa M.A (predictedState (M.B u) μ) (obs (t + 1)) with
      | .error e => .error (.updateRefused e)
      | .ok μ' => .ok μ'

variable [LinearOrder U]
  (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
  (world : ℕ → S) (obs : ℕ → O)

/-- Inverting an ok step at κ: an action and law that give the observation positive
probability, and an update that returned. -/
theorem machineStepAt_ok (kappa : ℝ) (t : ℕ) (μ μ' : S → ℝ)
    (h : machineStepAt kappa M inputsAt world obs t μ = .ok μ') :
    ∃ u law, machineObservationLaw M (inputsAt t μ) (world t) = .ok (u, law) ∧
      law (obs (t + 1)) ≠ 0 ∧
      normalisedUpdate kappa M.A (predictedState (M.B u) μ) (obs (t + 1)) = .ok μ' := by
  unfold machineStepAt at h
  cases hl : machineObservationLaw M (inputsAt t μ) (world t) with
  | error a => rw [hl] at h; cases h
  | ok p =>
    obtain ⟨u, law⟩ := p
    rw [hl] at h
    simp only at h
    split_ifs at h with hz
    cases hu : normalisedUpdate kappa M.A (predictedState (M.B u) μ) (obs (t + 1)) with
    | error e => rw [hu] at h; cases h
    | ok q =>
      rw [hu] at h
      cases h
      exact ⟨u, law, rfl, hz, hu⟩

/-- **C2 at the live likelihood.** On success the step's belief is exact Bayes
conditioning of the predicted state `B_u μ` with the precision likelihood at κ. -/
theorem machineStepAt_eq_update [Nonempty S] [Nonempty O] (kappa : ℝ) (t : ℕ) (μ μ' : S → ℝ)
    (h : machineStepAt kappa M inputsAt world obs t μ = .ok μ') :
    ∃ u law, machineObservationLaw M (inputsAt t μ) (world t) = .ok (u, law) ∧
      μ' = exactBayesUpdate (LikelihoodPrecision.precisionLikelihood kappa M.A)
        (predictedState (M.B u) μ) (obs (t + 1)) := by
  obtain ⟨u, law, hl, -, hu⟩ := machineStepAt_ok M inputsAt world obs kappa t μ μ' h
  exact ⟨u, law, hl, normalisedUpdate_eq_exactBayes kappa M.A _ _ hu⟩

/-- An update refusal stops the step with that refusal, typed. -/
theorem machineStepAt_updateRefused (kappa : ℝ) (t : ℕ) (μ : S → ℝ) (u : U)
    (law : O → ℝ) (e : UpdateError)
    (hl : machineObservationLaw M (inputsAt t μ) (world t) = .ok (u, law))
    (hpos : law (obs (t + 1)) ≠ 0)
    (he : normalisedUpdate kappa M.A (predictedState (M.B u) μ) (obs (t + 1)) = .error e) :
    machineStepAt kappa M inputsAt world obs t μ = .error (.updateRefused e) := by
  unfold machineStepAt
  rw [hl]
  simp only [hpos, if_false, he]

/-- **`machineStep` is the κ = 1 case.** For a positive column-stochastic `A`, an ok
step at κ = 1 is an ok `machineStep` with the same belief. -/
theorem machineStepAt_one_eq_machineStep [Nonempty S] [Nonempty O] (t : ℕ) (μ μ' : S → ℝ)
    (Apos : ∀ s o, 0 < M.A s o) (Acol : ∀ s, ∑ o, M.A s o = 1)
    (h : machineStepAt 1 M inputsAt world obs t μ = .ok μ') :
    machineStep M inputsAt world obs t μ = .ok μ' := by
  obtain ⟨u, law, hl, hz, hu⟩ := machineStepAt_ok M inputsAt world obs 1 t μ μ' h
  have hq : μ' = exactBayesUpdate M.A (predictedState (M.B u) μ) (obs (t + 1)) :=
    normalisedUpdate_one_eq_untempered M.A _ _ Apos Acol hu
  -- the κ = 1 evidence is the observation probability, and it is nonzero
  have hev : observationProbability M.A (M.B u) (obs (t + 1)) μ ≠ 0 := by
    intro h0
    have hpl : LikelihoodPrecision.precisionLikelihood 1 M.A = M.A := by
      funext s o
      exact LikelihoodPrecision.precisionLikelihood_one M.A Apos Acol s o
    unfold normalisedUpdate at hu
    simp only [zero_le_one, dite_true, hpl] at hu
    split_ifs at hu with hcol hzero
    exact hzero h0
  have hex : exactUpdate M.A (M.B u) (obs (t + 1)) μ = some μ' := by
    unfold exactUpdate
    rw [if_neg hev, hq]
    rfl
  unfold machineStep
  rw [hl]
  simp only [hz, if_false, hex]

#print axioms machineStepAt_eq_update
#print axioms machineStepAt_updateRefused
#print axioms machineStepAt_one_eq_machineStep

end

end DarkTower.WarMachine.Proof2.BeliefStepAtMachineKappa
