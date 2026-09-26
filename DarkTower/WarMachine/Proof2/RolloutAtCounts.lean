import DarkTower.WarMachine.Proof2.RolloutAtMachine
import DarkTower.WarMachine.Proof2.KernelAtCounts

/-!
# The rollout at the counted kernel (W8, registry `:forward-model` at `:token-likelihood`, R7→R4)

W4's `machineRollout` starts the rollout at the machine's current belief and takes the
model's `A` as it stands. `machineRolloutAtCounts` is that rollout with `A :=
tokenLikelihood` of the COUNTED rates (`KernelAtCounts.machineKernel`): both the belief
(`machineTrajectory`, whose steps are `exactUpdate` at `A`) and the predicted outcomes use
the counted kernel. A refused kernel gives no rollout, carrying the kernel's own absence.

A sibling module: `RolloutAtMachine` (W4) is unchanged. It reaches the counter through its
imports (`BeliefAtMachine` → `BeliefStepAtMachine` → `KernelAtCounts` →
`AdjudicationCounts`), so the map's [R7 R4] entry imports through the R4 module the
rollout lives in.
-/

namespace DarkTower.WarMachine.Proof2.RolloutAtCounts

open DarkTower.WarMachine
open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.Proof2.ObservationAtMachine
open DarkTower.WarMachine.Proof2.RolloutAtMachine
open DarkTower.WarMachine.Proof2.KernelAtCounts

noncomputable section

variable {κ V U PolicyIndex : Type*} [DecidableEq κ] [Fintype V] [DecidableEq V]
  [LinearOrder U] [DecidableEq PolicyIndex]

/-- Why there is no rollout at the counted rates. -/
inductive RolloutAtCountsAbsence (V PolicyIndex : Type*) where
  | kernel (a : KernelAbsence V)
  | rollout (a : RolloutAbsence PolicyIndex)

/-- **W4's rollout at the counted kernel.** -/
def machineRolloutAtCounts (records : List (AdjudicationCounts.Record κ V)) (classOf : V → κ)
    (kindOf : κ → AdjudicationCounts.ClassKind)
    (M : ForwardModel (Finset V) (Finset V) U)
    (inputsAt : ℕ → (Finset V → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → Finset V) (obs : ℕ → Finset V) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) :
    Except (RolloutAtCountsAbsence V PolicyIndex) (Fin (T + 1) → Finset V → ℝ) :=
  match machineKernel records classOf kindOf with
  | .error a => .error (.kernel a)
  | .ok k =>
    match machineRollout (withKernel M k) inputsAt world obs t T π plan with
    | .error a => .error (.rollout a)
    | .ok f => .ok f

/-- **The instantiation.** On the ok arm the rollout IS `machineRollout` at the model whose
likelihood is the counted kernel. -/
theorem machineRolloutAtCounts_eq (records : List (AdjudicationCounts.Record κ V))
    (classOf : V → κ) (kindOf : κ → AdjudicationCounts.ClassKind)
    (M : ForwardModel (Finset V) (Finset V) U)
    (inputsAt : ℕ → (Finset V → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → Finset V) (obs : ℕ → Finset V) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (f : Fin (T + 1) → Finset V → ℝ)
    (h : machineRolloutAtCounts records classOf kindOf M inputsAt world obs t T π plan = .ok f) :
    ∃ k, machineKernel records classOf kindOf = .ok k ∧
      machineRollout (withKernel M k) inputsAt world obs t T π plan = .ok f := by
  unfold machineRolloutAtCounts at h
  cases hk : machineKernel records classOf kindOf with
  | error a => simp only [hk] at h; cases h
  | ok k =>
    simp only [hk] at h
    cases hr : machineRollout (withKernel M k) inputsAt world obs t T π plan with
    | error a => simp only [hr] at h; cases h
    | ok x => simp only [hr] at h; exact ⟨k, rfl, by rw [hr, Except.ok.inj h]⟩

/-- **The rollout at the counted rates is a distribution at every step**, whose likelihood is
the counted kernel's: inherited from `machineRollout_isDistribution`. -/
theorem machineRolloutAtCounts_isDistribution (records : List (AdjudicationCounts.Record κ V))
    (classOf : V → κ) (kindOf : κ → AdjudicationCounts.ClassKind)
    (M : ForwardModel (Finset V) (Finset V) U)
    (inputsAt : ℕ → (Finset V → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → Finset V) (obs : ℕ → Finset V) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (f : Fin (T + 1) → Finset V → ℝ)
    (h : machineRolloutAtCounts records classOf kindOf M inputsAt world obs t T π plan = .ok f)
    (τ : Fin (T + 1)) :
    (∀ o, 0 ≤ f τ o) ∧ ∑ o, f τ o = 1 := by
  obtain ⟨k, _, hr⟩ := machineRolloutAtCounts_eq records classOf kindOf M inputsAt world obs t T π
    plan f h
  exact machineRollout_isDistribution (withKernel M k) inputsAt world obs t T π plan f hr τ

/-- **A refused kernel gives no rollout**, carrying the kernel's absence. -/
theorem machineRolloutAtCounts_absentKernel (records : List (AdjudicationCounts.Record κ V))
    (classOf : V → κ) (kindOf : κ → AdjudicationCounts.ClassKind)
    (M : ForwardModel (Finset V) (Finset V) U)
    (inputsAt : ℕ → (Finset V → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → Finset V) (obs : ℕ → Finset V) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (a : KernelAbsence V)
    (h : machineKernel records classOf kindOf = .error a) :
    machineRolloutAtCounts records classOf kindOf M inputsAt world obs t T π plan
      = .error (.kernel a) := by
  simp [machineRolloutAtCounts, h]

end

#print axioms RolloutAtCountsAbsence
#print axioms machineRolloutAtCounts
#print axioms machineRolloutAtCounts_eq
#print axioms machineRolloutAtCounts_isDistribution
#print axioms machineRolloutAtCounts_absentKernel

end DarkTower.WarMachine.Proof2.RolloutAtCounts
