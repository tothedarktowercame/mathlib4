import DarkTower.WarMachine.ChannelPrecision
import DarkTower.WarMachine.Proof2.StatePredictionErrorAtMachine

/-!
# The channel precision of the machine's own state prediction errors (W5, registry `:precision`, R7)

`ChannelPrecision.channelPrecision eps0 h0 errors` is the eq. (84) precision
`1 / max (Var errors) eps0` of a WINDOW of prediction errors `errors : Fin (n+1) → ℝ`,
taken free. Nothing in Lean supplied the machine's own errors to it, so the registry
edge R3a→R7 (`ε` into the precision) had the term in the consumer's signature and no
import behind it.

`machineChannelPrecision` applies it: the window is the machine's state prediction
error (`StatePredictionErrorAtMachine.machineStatePredictionError`) at the steps
`τ₀, τ₀+1, …, τ₀+n`, read at one state `x`. If ANY step of the window has no error
(`outOfHorizon`, `logUndefined`, an absent rollout) the precision is absent and carries
that step's own absence: no step is dropped or defaulted, so the window is the whole
window or nothing.

This module is separate from `StatePredictionErrorAtMachine` on purpose: the error
(R3a) and the precision (R7) are different registry nodes, and one module holding both
would count as an import only through a module placed at both.
-/

namespace DarkTower.WarMachine.Proof2.ChannelPrecisionAtMachine

open DarkTower.WarMachine
open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.Proof2.BeliefAtMachine
open DarkTower.WarMachine.Proof2.BeliefStepAtMachine
open DarkTower.WarMachine.Proof2.ObservationAtMachine
open DarkTower.WarMachine.Proof2.RolloutAtMachine
open DarkTower.WarMachine.Proof2.StatePredictionErrorAtMachine

noncomputable section

/-- Sequence `k` fallible values into one fallible tuple, stopping at the first
absence in index order. -/
def collect {E α : Type*} : (k : ℕ) → (Fin k → Except E α) → Except E (Fin k → α)
  | 0, _ => .ok Fin.elim0
  | k + 1, f =>
    match f 0 with
    | .error e => .error e
    | .ok a =>
      match collect k (fun i => f i.succ) with
      | .error e => .error e
      | .ok rest => .ok (Fin.cons a rest)

/-- A collected tuple was made of the values. -/
theorem collect_ok {E α : Type*} :
    ∀ (k : ℕ) (f : Fin k → Except E α) (g : Fin k → α), collect k f = .ok g →
      ∀ i, f i = .ok (g i)
  | 0, _, _, _, i => i.elim0
  | k + 1, f, g, h, i => by
    unfold collect at h
    cases h0 : f 0 with
    | error e => rw [h0] at h; cases h
    | ok a =>
      rw [h0] at h
      cases hr : collect k (fun i => f i.succ) with
      | error e => rw [hr] at h; cases h
      | ok rest =>
        rw [hr] at h
        have hg := Except.ok.inj h
        subst hg
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using h0
        · have := collect_ok k (fun i => f i.succ) rest hr j
          simpa using this

section
variable {S O U PolicyIndex : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
  [LinearOrder U] [DecidableEq PolicyIndex]

/-- **The precision of the machine's state prediction errors over a window.** The window is
the errors at steps `τ₀ + i`, `i = 0..n`, read at state `x`; `eps0` and its positivity are
the row's floor. -/
def machineChannelPrecision (eps0 : ℝ) (h0 : 0 < eps0) (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ₀ n : ℕ) (x : S) :
    Except (ErrorAbsence PolicyIndex) ℝ :=
  match collect (n + 1) (fun i : Fin (n + 1) =>
      machineStatePredictionError M inputsAt world obs t T π plan (τ₀ + i)) with
  | .error e => .error e
  | .ok errs => .ok (ChannelPrecision.channelPrecision eps0 h0 (fun i => errs i x))

/-- **`machineChannelPrecision_eq` — the instantiation.** On the ok arm the precision IS
`channelPrecision` of the window of the machine's errors. -/
theorem machineChannelPrecision_eq (eps0 : ℝ) (h0 : 0 < eps0) (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ₀ n : ℕ) (x : S) (p : ℝ)
    (h : machineChannelPrecision eps0 h0 M inputsAt world obs t T π plan τ₀ n x = .ok p) :
    ∃ errs : Fin (n + 1) → S → ℝ,
      (∀ i : Fin (n + 1), machineStatePredictionError M inputsAt world obs t T π plan (τ₀ + i) = .ok (errs i)) ∧
      p = ChannelPrecision.channelPrecision eps0 h0 (fun i => errs i x) := by
  unfold machineChannelPrecision at h
  cases hc : collect (n + 1) (fun i : Fin (n + 1) =>
      machineStatePredictionError M inputsAt world obs t T π plan (τ₀ + i)) with
  | error e => rw [hc] at h; cases h
  | ok errs =>
    rw [hc] at h
    exact ⟨errs, collect_ok _ _ _ hc, (Except.ok.inj h).symm⟩

/-- The precision is positive and at most `1 / eps0` (the floor), by
`ChannelPrecision`'s own theorems. -/
theorem machineChannelPrecision_bounds (eps0 : ℝ) (h0 : 0 < eps0) (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ₀ n : ℕ) (x : S) (p : ℝ)
    (h : machineChannelPrecision eps0 h0 M inputsAt world obs t T π plan τ₀ n x = .ok p) :
    0 < p ∧ p ≤ 1 / eps0 := by
  obtain ⟨errs, _, rfl⟩ := machineChannelPrecision_eq eps0 h0 M inputsAt world obs t T π plan τ₀ n x p h
  exact ⟨ChannelPrecision.channelPrecision_pos eps0 h0 _,
    ChannelPrecision.channelPrecision_le_inv_eps0 eps0 h0 _⟩

/-- **A window with any absent step is absent**, carrying the first such step's absence:
no error is dropped from the window or defaulted. -/
theorem machineChannelPrecision_absentStep (eps0 : ℝ) (h0 : 0 < eps0) (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ₀ n : ℕ) (x : S) (i : Fin (n + 1)) (e : ErrorAbsence PolicyIndex)
    (hi : machineStatePredictionError M inputsAt world obs t T π plan (τ₀ + i) = .error e) :
    ∃ e', machineChannelPrecision eps0 h0 M inputsAt world obs t T π plan τ₀ n x = .error e' := by
  cases h : machineChannelPrecision eps0 h0 M inputsAt world obs t T π plan τ₀ n x with
  | error e' => exact ⟨e', rfl⟩
  | ok p =>
    obtain ⟨errs, hall, _⟩ := machineChannelPrecision_eq eps0 h0 M inputsAt world obs t T π plan
      τ₀ n x p h
    rw [hall i] at hi; cases hi

end

end

#print axioms collect
#print axioms collect_ok
#print axioms machineChannelPrecision
#print axioms machineChannelPrecision_eq
#print axioms machineChannelPrecision_bounds
#print axioms machineChannelPrecision_absentStep

end DarkTower.WarMachine.Proof2.ChannelPrecisionAtMachine
