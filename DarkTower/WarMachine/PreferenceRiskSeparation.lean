import DarkTower.WarMachine.PreferenceLadderDraft

/-! Joe's 2026-09-09 FoldC sitting (futon2 SESSION-FoldC-separation-2026-09-09.md):
preferences and scalar KL risk are distinct. Finite probability/prediction
composition precedes risk evaluation. This uses the existing finite kernel
carrier; it does not claim an instance of Mathlib's Stoch category or close
E-C-realization §1b. The constant adapter discards its input explicitly. -/
namespace DarkTower.WarMachine.PreferenceRiskSeparation
open Holes
noncomputable section

/-- Constant conditional: the explicitly commissioned adapter, not an inferred
    checkpoint-to-channel observation bridge. Zero masses remain unchanged. -/
def constantConditional {Observation Disposition : Type*}
    (distribution : ProbabilityKernel Unit Disposition) :
    ProbabilityKernel Observation Disposition where
  support := fun _ => distribution.support ()
  mass := fun _ => distribution.mass ()
  nonnegative := fun _ => distribution.nonnegative ()
  normalised := fun _ => distribution.normalised ()

/-- Finite stochastic composition, with the same marginalisation as the ladder. -/
def predictiveMass {Policy Observation Disposition : Type*}
    (Q : ProbabilityKernel Policy Observation)
    (K : ProbabilityKernel Observation Disposition) (p : Policy) (d : Disposition) : ℝ :=
  ((Q.support p).map (fun o => K.mass o d * Q.mass p o)).sum

/-- Discard followed by a constant distribution absorbs every normalised
    upstream prediction. This establishes the adapter's non-discrimination. -/
theorem constant_absorbs_prediction {Policy Observation Disposition : Type*}
    (Q : ProbabilityKernel Policy Observation)
    (distribution : ProbabilityKernel Unit Disposition) (p : Policy) (d : Disposition) :
    predictiveMass Q (constantConditional distribution) p d = distribution.mass () d := by
  simp only [predictiveMass, constantConditional]
  rw [List.sum_map_mul_left, Q.normalised]
  simp

/-- A risk is policy-indexed scalar data, not a preference kernel or layer. -/
structure RiskContribution (Policy : Type*) where
  value : Policy → ℝ

/-- All named outcomes remain in the sum. Positive Q at preferred zero is
    inadmissible; zero Q contributes zero without changing the preference. -/
def riskAdmissible {Policy Disposition : Type*}
    (Q : ProbabilityKernel Policy Disposition)
    (C : ProbabilityKernel Unit Disposition) : Prop :=
  ∀ p d, d ∈ Q.support p → Q.mass p d ≠ 0 → 0 < C.mass () d

def scalarKL {Policy Disposition : Type*}
    (Q : ProbabilityKernel Policy Disposition)
    (C : ProbabilityKernel Unit Disposition)
    (_admitted : riskAdmissible Q C) : RiskContribution Policy where
  value := fun p => ((Q.support p).map (fun d =>
    if Q.mass p d = 0 then 0 else Q.mass p d * Real.log (Q.mass p d / C.mass () d))).sum

theorem preferred_zero_refuses {Policy Disposition : Type*}
    (Q : ProbabilityKernel Policy Disposition)
    (C : ProbabilityKernel Unit Disposition) (p : Policy) (d : Disposition)
    (hd : d ∈ Q.support p) (hq : Q.mass p d ≠ 0) (hc : C.mass () d = 0) :
    ¬ riskAdmissible Q C := by
  intro h
  have impossible := h p d hd hq
  rw [hc] at impossible
  exact (lt_irrefl 0) impossible

/-- The measured constant-adapter arithmetic: delta prediction at seed mass 1/2.
    This is a scalar result, not a preference assignment to every outcome. -/
theorem grounded_seed_risk : (1 : ℝ) * Real.log (1 / (1 / 2)) = Real.log 2 := by
  norm_num

#print axioms constantConditional
#print axioms predictiveMass
#print axioms constant_absorbs_prediction
#print axioms RiskContribution
#print axioms riskAdmissible
#print axioms scalarKL
#print axioms preferred_zero_refuses
#print axioms grounded_seed_risk
end
end DarkTower.WarMachine.PreferenceRiskSeparation
