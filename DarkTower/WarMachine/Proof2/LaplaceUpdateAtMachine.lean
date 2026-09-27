import DarkTower.WarMachine.LaplaceBeliefUpdate
import DarkTower.WarMachine.Proof2.ChannelPrecisionAtMachine

/-!
# Laplace update at the machine's windowed precision (P-inst-Pi)

The registry consumer is `:belief-update`, not the categorical `machineStep`.
The precision source reads a state; the Laplace consumer updates a channel.
`xOf` explicitly supplies that correspondence, without asserting that the two
carriers coincide or choosing a default state. Each channel retains the source's
absence unchanged. This is a Lean instantiation, not a claim about the live
arena update or a choice of its observation model.
-/
namespace DarkTower.WarMachine.Proof2.LaplaceUpdateAtMachine

open DarkTower.WarMachine
open Holes PolicyRollout LaplaceBeliefUpdate
open Proof2.ObservationAtMachine Proof2.StatePredictionErrorAtMachine
open Proof2.ChannelPrecisionAtMachine

/-- Evaluate the actual Laplace consumer at one supplied precision coordinate.
No absent precision becomes a number or an unchanged belief. -/
def updateAtPrecision {E : Type*} (α : ℝ) (o : ObservationVector)
    (μ : Channel → ℝ) (k : Channel) (source : Except E ℝ) : Except E ℝ :=
  match source with
  | .error e => .error e
  | .ok p => .ok (LaplaceBeliefUpdate.beliefUpdate α (fun _ => p) o μ k)

section
variable {S O U PolicyIndex : Type*} [Fintype S] [DecidableEq S]
  [Fintype O] [DecidableEq O] [LinearOrder U] [DecidableEq PolicyIndex]

noncomputable def machineBeliefUpdate (eps0 : ℝ) (h0 : 0 < eps0)
    (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ₀ n : ℕ) (xOf : Channel → S)
    (α : ℝ) (o : ObservationVector) (μ : Channel → ℝ) :
    Channel → Except (ErrorAbsence PolicyIndex) ℝ :=
  fun k => updateAtPrecision α o μ k
    (machineChannelPrecision eps0 h0 M inputsAt world obs t T π plan τ₀ n (xOf k))

/-- Every available source coordinate gives precisely the parametric consumer
at that precision. All-ok coordinates therefore agree with the whole vector. -/
theorem machineBeliefUpdate_eq (eps0 : ℝ) (h0 : 0 < eps0)
    (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ₀ n : ℕ) (xOf : Channel → S)
    (α : ℝ) (o : ObservationVector) (μ prec : Channel → ℝ) (k : Channel)
    (h : machineChannelPrecision eps0 h0 M inputsAt world obs t T π plan τ₀ n
      (xOf k) = .ok (prec k)) :
    machineBeliefUpdate eps0 h0 M inputsAt world obs t T π plan τ₀ n xOf α o μ k =
      .ok (LaplaceBeliefUpdate.beliefUpdate α prec o μ k) := by
  simp [machineBeliefUpdate, h, updateAtPrecision, LaplaceBeliefUpdate.beliefUpdate]

/-- A refused source window is carried, never filled with a default precision. -/
theorem machineBeliefUpdate_absent (eps0 : ℝ) (h0 : 0 < eps0)
    (M : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (τ₀ n : ℕ) (xOf : Channel → S)
    (α : ℝ) (o : ObservationVector) (μ : Channel → ℝ) (k : Channel)
    (e : ErrorAbsence PolicyIndex)
    (h : machineChannelPrecision eps0 h0 M inputsAt world obs t T π plan τ₀ n
      (xOf k) = .error e) :
    machineBeliefUpdate eps0 h0 M inputsAt world obs t T π plan τ₀ n xOf α o μ k =
      .error e := by
  simp [machineBeliefUpdate, h, updateAtPrecision]
end

/-- Different supplied precisions change the consumer whenever the step and
channel residual are nonzero; equality cannot hide an ignored source value. -/
theorem different_precision_changes_update {E : Type*} (α p q : ℝ)
    (o : ObservationVector) (μ : Channel → ℝ) (k : Channel)
    (hα : α ≠ 0) (herr : o.value k - μ k ≠ 0) (hpq : p ≠ q) :
    updateAtPrecision (E := E) α o μ k (.ok p) ≠
      updateAtPrecision α o μ k (.ok q) := by
  intro h
  have hv := Except.ok.inj h
  simp only [LaplaceBeliefUpdate.beliefUpdate, sensoryPredictionError_identityMap] at hv
  have hz : α * (p - q) * (o.value k - μ k) = 0 := by nlinarith [hv]
  exact (mul_ne_zero (mul_ne_zero hα (sub_ne_zero.mpr hpq)) herr) hz

/-- Concrete bad case at the real consumer: source 2 gives 7/10, source 3
 gives 4/5. Both are positive; no domain failure explains the difference. -/
theorem different_precision_fixture (k : Channel) :
    updateAtPrecision (E := Unit) (1/10) ⟨fun _ => 3/2⟩ (fun _ => 1/2) k (.ok 2)
      = .ok (7/10) ∧
    updateAtPrecision (E := Unit) (1/10) ⟨fun _ => 3/2⟩ (fun _ => 1/2) k (.ok 3)
      = .ok (4/5) := by
  norm_num [updateAtPrecision, LaplaceBeliefUpdate.beliefUpdate, sensoryPredictionError_identityMap]

#print axioms updateAtPrecision
#print axioms machineBeliefUpdate
#print axioms machineBeliefUpdate_eq
#print axioms machineBeliefUpdate_absent
#print axioms different_precision_changes_update
#print axioms different_precision_fixture
end DarkTower.WarMachine.Proof2.LaplaceUpdateAtMachine
