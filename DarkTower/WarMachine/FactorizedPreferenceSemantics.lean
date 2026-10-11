import Mathlib.Tactic

/-!
# Factorized criterion-completion preference

Completion is the primary dimension.  Strategic relevance is conditional on
truthful completion and cannot trade against it.  Unknown/unmeasured is not an
observed failure class.
-/

namespace DarkTower.WarMachine.FactorizedPreferenceSemantics

abbrev Id := Nat

inductive Completion where
  | completed | notCompleted | unmeasured
  deriving DecidableEq, Repr

inductive Relevance where
  | focused | related | unrelated
  deriving DecidableEq, Repr

structure Outcome where
  completion : Completion
  relevance : Option Relevance
  deriving DecidableEq, Repr

/-- Externally authorized calibration of the conditional relevance order.
The numbers are parameters; validity states only their ordinal law. -/
structure RelevanceCalibration where
  identity : Id
  version : Nat
  authority : Id
  registrationToken : Id
  focusedCost : Nat
  relatedCost : Nat
  unrelatedCost : Nat
  deriving DecidableEq, Repr

def RelevanceCalibration.Valid (selectorAuthority : Id)
    (c : RelevanceCalibration) : Prop :=
  c.identity ≠ 0 ∧ c.registrationToken ≠ 0 ∧
  c.authority ≠ selectorAuthority ∧
  c.focusedCost < c.relatedCost ∧ c.relatedCost < c.unrelatedCost

instance (selectorAuthority : Id) (c : RelevanceCalibration) :
    Decidable (c.Valid selectorAuthority) := by
  unfold RelevanceCalibration.Valid
  infer_instance

def relevanceCost (c : RelevanceCalibration) : Relevance → Nat
  | .focused => c.focusedCost
  | .related => c.relatedCost
  | .unrelated => c.unrelatedCost

/-- Lexicographic preference.  Unknown is incomparable; relevance participates
only when both outcomes are truthfully completed. -/
def Preferred (c : RelevanceCalibration) (a b : Outcome) : Prop :=
  match a.completion, b.completion with
  | .completed, .notCompleted => True
  | .completed, .completed => match a.relevance, b.relevance with
      | some ar, some br => relevanceCost c ar < relevanceCost c br
      | _, _ => False
  | _, _ => False

instance (c : RelevanceCalibration) (a b : Outcome) : Decidable (Preferred c a b) := by
  cases a with
  | mk ac ar =>
    cases b with
    | mk bc br =>
      cases ac <;> cases bc <;> cases ar <;> cases br <;>
        simp only [Preferred] <;> infer_instance

structure Certificate where
  calibration : RelevanceCalibration
  selectorAuthority : Id
  factorizationIdentity : Id
  factorizationVersion : Nat
  calibrationAuthorization : Id
  completionObservedSeparately : Bool
  unknownSeparatedFromNonCompletion : Bool
  deriving DecidableEq, Repr

structure CalibrationAuthorization where
  receipt : Id
  calibration : RelevanceCalibration
  authorizedBy : Id
  deriving DecidableEq, Repr

def Certificate.Valid (registry : List CalibrationAuthorization) (c : Certificate) : Prop :=
  c.calibration.Valid c.selectorAuthority ∧
  c.factorizationIdentity ≠ 0 ∧
  (∃ authorization ∈ registry,
    authorization.receipt = c.calibrationAuthorization ∧
    authorization.calibration = c.calibration ∧
    authorization.authorizedBy = c.calibration.authority) ∧
  c.completionObservedSeparately = true ∧
  c.unknownSeparatedFromNonCompletion = true

instance (registry : List CalibrationAuthorization) (c : Certificate) :
    Decidable (c.Valid registry) := by
  unfold Certificate.Valid
  infer_instance

theorem completion_always_outranks_noncompletion
    (c : RelevanceCalibration) (completedRelevance : Option Relevance)
    (noncompletionRelevance : Option Relevance) :
    Preferred c ⟨.completed, completedRelevance⟩
      ⟨.notCompleted, noncompletionRelevance⟩ := by
  simp [Preferred]

theorem relevance_cannot_reverse_completion
    (c : RelevanceCalibration) (completedRelevance noncompletionRelevance : Option Relevance) :
    ¬ Preferred c ⟨.notCompleted, noncompletionRelevance⟩
      ⟨.completed, completedRelevance⟩ := by
  simp [Preferred]

theorem focused_before_related (c : RelevanceCalibration) (h : c.Valid 99) :
    Preferred c ⟨.completed, some .focused⟩ ⟨.completed, some .related⟩ := by
  simp [Preferred, relevanceCost, h.2.2.2.1]

theorem related_before_unrelated (c : RelevanceCalibration) (h : c.Valid 99) :
    Preferred c ⟨.completed, some .related⟩ ⟨.completed, some .unrelated⟩ := by
  simp [Preferred, relevanceCost, h.2.2.2.2]

theorem unmeasured_is_not_observed_noncompletion
    (c : RelevanceCalibration) (r₁ r₂ : Option Relevance) :
    ¬ Preferred c ⟨.unmeasured, r₁⟩ ⟨.notCompleted, r₂⟩ ∧
    ¬ Preferred c ⟨.notCompleted, r₂⟩ ⟨.unmeasured, r₁⟩ := by
  simp [Preferred]

theorem unmeasured_is_incomparable
    (c : RelevanceCalibration) (r₁ r₂ : Option Relevance) (other : Completion) :
    ¬ Preferred c ⟨.unmeasured, r₁⟩ ⟨other, r₂⟩ ∧
    ¬ Preferred c ⟨other, r₂⟩ ⟨.unmeasured, r₁⟩ := by
  cases other <;> simp [Preferred]

/-- A flat four-way table alone supplies neither factorization nor calibration
authorization and therefore cannot discharge Q9. -/
theorem flat_table_without_receipt_is_not_certificate
    (_focused _related _unrelated _stop : Nat) :
    ¬ ∃ certificate : Certificate, Certificate.Valid [] certificate := by
  rintro ⟨certificate, _, _, ⟨authorization, member, _⟩, _⟩
  simp at member

/-- Positive witness without fixing calibration values: any externally
authorized strict calibration yields a valid certificate. -/
theorem authorized_factorization_valid
    (calibration : RelevanceCalibration) (selectorAuthority factorizationIdentity receipt : Id)
    (hcalibration : calibration.Valid selectorAuthority)
    (hfactorization : factorizationIdentity ≠ 0) :
    let authorization : CalibrationAuthorization :=
      ⟨receipt, calibration, calibration.authority⟩
    let certificate : Certificate :=
      ⟨calibration, selectorAuthority, factorizationIdentity, 1, receipt, true, true⟩
    certificate.Valid [authorization] := by
  simp [Certificate.Valid, hcalibration, hfactorization]

theorem self_authorized_calibration_invalid
    (registry : List CalibrationAuthorization) (certificate : Certificate)
    (hself : certificate.selectorAuthority = certificate.calibration.authority) :
    ¬ certificate.Valid registry := by
  intro h
  exact h.1.2.2.1 hself.symm

theorem substituted_calibration_not_authorized
    (authorization : CalibrationAuthorization) (certificate : Certificate)
    (hsubstitution : authorization.calibration ≠ certificate.calibration) :
    ¬ certificate.Valid [authorization] := by
  intro h
  rcases h.2.2.1 with ⟨registered, member, _, heq, _⟩
  simp only [List.mem_singleton] at member
  subst registered
  exact hsubstitution heq

end DarkTower.WarMachine.FactorizedPreferenceSemantics
