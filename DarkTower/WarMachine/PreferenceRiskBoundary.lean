import DarkTower.WarMachine.PreferenceRiskWitness

/-! Era-2 risk boundary under Joe's 2026-09-09 separation ruling.
The role of futon2/src/futon2/aif/efe.clj:702-713 is weighted scalar addition
AFTER disposition prediction and preference comparison. It does not insert a
KL scalar into PreferenceLayer.prefers. These are exact-real model statements;
the finite runtime execution certificate is a separate correspondence check.
The declared list below records the risk axis only, not preference layers. -/
namespace DarkTower.WarMachine.PreferenceRiskBoundary
open Holes PreferenceRiskSeparation PreferenceRiskWitness
noncomputable section

/-- Declaration counterpart of the enabled ruled-outcome-c scorer contribution.
This is not a claim that a particular live run enabled it. -/
def runtimeRiskContributionIds : List String := ["ruled-outcome-c"]

/-- The recorded scorer operation: add a weighted scalar to existing risk. -/
def addRisk {Policy : Type*} (base : Policy → ℝ) (weight : ℝ)
    (risk : RiskContribution Policy) : Policy → ℝ :=
  fun p => base p + weight * risk.value p

theorem contribution_delta {Policy : Type*} (base : Policy → ℝ) (weight : ℝ)
    (risk : RiskContribution Policy) (p : Policy) :
    addRisk base weight risk p - base p = weight * risk.value p := by
  simp [addRisk]

theorem zero_weight_preserves {Policy : Type*} (base : Policy → ℝ)
    (risk : RiskContribution Policy) : addRisk base 0 risk = base := by
  funext p
  simp [addRisk]

/-- Keep both products explicitly typed. Adding a computed risk changes only
risk accounting; it neither changes nor recomputes the preference fold. This
conditional statement holds the computed contribution fixed, and does NOT say
KL is insensitive to changing the preference distribution used to compute it. -/
def separatedOutputs {Policy Outcome : Type*}
    (preference : Outcome → ℝ) (layers : List (PreferenceLayer Outcome))
    (baseRisk : Policy → ℝ) (weight : ℝ) (risk : RiskContribution Policy) :
    (Outcome → ℝ) × (Policy → ℝ) :=
  (foldC preference layers, addRisk baseRisk weight risk)

theorem preference_projection_unchanged {Policy Outcome : Type*}
    (preference : Outcome → ℝ) (layers : List (PreferenceLayer Outcome))
    (baseRisk : Policy → ℝ) (weight : ℝ) (risk : RiskContribution Policy) :
    (separatedOutputs preference layers baseRisk weight risk).1 =
      foldC preference layers := rfl

theorem grounded_risk_sum (base : Unit → ℝ) (weight : ℝ) :
    addRisk base weight
      (scalarKL groundedPrediction F10RuledCarrier.seed grounded_admissible) () =
    base () + weight * Real.log 2 := by
  simp only [addRisk, concrete_scalarKL]

/-- Reject the variant that omits a known nonzero contribution. -/
theorem dropped_contribution_refused :
    addRisk (fun _ : Unit => 0) 1 ⟨fun _ => 1⟩ () ≠ 0 := by
  norm_num [addRisk]

#print axioms dropped_contribution_refused
#print axioms contribution_delta
#print axioms zero_weight_preserves
#print axioms preference_projection_unchanged
#print axioms grounded_risk_sum
end
end DarkTower.WarMachine.PreferenceRiskBoundary
