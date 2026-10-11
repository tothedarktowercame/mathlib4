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

def Outcome.Valid (o : Outcome) : Prop :=
  match o.completion with
  | .completed => o.relevance.isSome
  | .notCompleted | .unmeasured => o.relevance = none

instance (o : Outcome) : Decidable o.Valid := by
  unfold Outcome.Valid
  split <;> infer_instance

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
  c.identity ≠ 0 ∧ c.version ≠ 0 ∧ c.authority ≠ 0 ∧ c.registrationToken ≠ 0 ∧
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
  a.Valid ∧ b.Valid ∧
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
  factorizationAuthority : Id
  calibrationAuthorization : Id
  factorizationAuthorization : Id
  deriving DecidableEq, Repr

structure CalibrationAuthorization where
  receipt : Id
  calibration : RelevanceCalibration
  authorizedBy : Id
  deriving DecidableEq, Repr

inductive FactorizationLaw where
  | completionThenConditionalRelevance
  deriving DecidableEq, Repr

structure FactorizationAuthorization where
  receipt : Id
  identity : Id
  version : Nat
  authority : Id
  law : FactorizationLaw
  deriving DecidableEq, Repr

def CalibrationAuthorized (registry : List CalibrationAuthorization)
    (receipt : Id) (calibration : RelevanceCalibration) : Prop :=
  receipt ≠ 0 ∧
  ∃ authorization ∈ registry,
    authorization.receipt = receipt ∧
    authorization.calibration = calibration ∧
    authorization.authorizedBy = calibration.authority

def FactorizationAuthorized (registry : List FactorizationAuthorization)
    (selectorAuthority identity : Id) (version : Nat) (authority receipt : Id) : Prop :=
  identity ≠ 0 ∧ version ≠ 0 ∧ authority ≠ 0 ∧ receipt ≠ 0 ∧
  ∃ authorization ∈ registry,
    authorization.receipt = receipt ∧
    authorization.identity = identity ∧
    authorization.version = version ∧
    authorization.authority = authority ∧
    authorization.authority ≠ selectorAuthority ∧
    authorization.law = .completionThenConditionalRelevance

def Certificate.Valid (calibrationRegistry : List CalibrationAuthorization)
    (factorizationRegistry : List FactorizationAuthorization) (c : Certificate) : Prop :=
  c.calibration.Valid c.selectorAuthority ∧
  CalibrationAuthorized calibrationRegistry c.calibrationAuthorization c.calibration ∧
  FactorizationAuthorized factorizationRegistry c.selectorAuthority
    c.factorizationIdentity c.factorizationVersion c.factorizationAuthority
    c.factorizationAuthorization

noncomputable instance (calibrationRegistry : List CalibrationAuthorization)
    (factorizationRegistry : List FactorizationAuthorization) (c : Certificate) :
    Decidable (c.Valid calibrationRegistry factorizationRegistry) := by
  classical
  unfold Certificate.Valid
  infer_instance

theorem completion_always_outranks_noncompletion
    (c : RelevanceCalibration) (completed noncompletion : Outcome)
    (hc : completed.Valid) (hn : noncompletion.Valid)
    (hcKind : completed.completion = .completed)
    (hnKind : noncompletion.completion = .notCompleted) :
    Preferred c completed noncompletion := by
  rcases completed with ⟨completedKind, completedRelevance⟩
  rcases noncompletion with ⟨noncompletionKind, noncompletionRelevance⟩
  cases completedKind <;> cases noncompletionKind <;>
    simp_all [Preferred, Outcome.Valid]

theorem relevance_cannot_reverse_completion
    (c : RelevanceCalibration) (completed noncompletion : Outcome)
    (hcKind : completed.completion = .completed)
    (hnKind : noncompletion.completion = .notCompleted) :
    ¬ Preferred c noncompletion completed := by
  rcases completed with ⟨completedKind, completedRelevance⟩
  rcases noncompletion with ⟨noncompletionKind, noncompletionRelevance⟩
  cases completedKind <;> cases noncompletionKind <;>
    simp_all [Preferred, Outcome.Valid]

theorem focused_before_related (c : RelevanceCalibration) (selectorAuthority : Id)
    (h : c.Valid selectorAuthority) :
    Preferred c ⟨.completed, some .focused⟩ ⟨.completed, some .related⟩ := by
  simp [Preferred, Outcome.Valid, relevanceCost, h.2.2.2.2.2.1]

theorem related_before_unrelated (c : RelevanceCalibration) (selectorAuthority : Id)
    (h : c.Valid selectorAuthority) :
    Preferred c ⟨.completed, some .related⟩ ⟨.completed, some .unrelated⟩ := by
  simp [Preferred, Outcome.Valid, relevanceCost, h.2.2.2.2.2.2]

theorem unmeasured_is_not_observed_noncompletion
    (c : RelevanceCalibration) (r₁ r₂ : Option Relevance) :
    ¬ Preferred c ⟨.unmeasured, r₁⟩ ⟨.notCompleted, r₂⟩ ∧
    ¬ Preferred c ⟨.notCompleted, r₂⟩ ⟨.unmeasured, r₁⟩ := by
  simp [Preferred, Outcome.Valid]

theorem unmeasured_is_incomparable
    (c : RelevanceCalibration) (r₁ r₂ : Option Relevance) (other : Completion) :
    ¬ Preferred c ⟨.unmeasured, r₁⟩ ⟨other, r₂⟩ ∧
    ¬ Preferred c ⟨other, r₂⟩ ⟨.unmeasured, r₁⟩ := by
  cases other <;> simp [Preferred, Outcome.Valid]

theorem completed_without_relevance_invalid :
    ¬ (Outcome.mk .completed none).Valid := by
  simp [Outcome.Valid]

theorem noncompletion_with_relevance_invalid (r : Relevance) :
    ¬ (Outcome.mk .notCompleted (some r)).Valid := by
  simp [Outcome.Valid]

/-- A flat four-way table alone supplies neither factorization nor calibration
authorization and therefore cannot discharge Q9. -/
theorem flat_table_without_receipt_is_not_certificate
    (_focused _related _unrelated _stop : Nat) :
    ¬ ∃ certificate : Certificate, Certificate.Valid [] [] certificate := by
  rintro ⟨certificate, h⟩
  rcases h.2.1 with ⟨_, authorization, member, _⟩
  simp at member

/-- Positive witness without fixing calibration values: any externally
authorized strict calibration yields a valid certificate. -/
theorem authorized_factorization_valid
    (calibration : RelevanceCalibration) (selectorAuthority factorizationIdentity receipt : Id)
    (factorizationAuthority factorizationReceipt : Id) (factorizationVersion : Nat)
    (hcalibration : calibration.Valid selectorAuthority)
    (hfactorization : factorizationIdentity ≠ 0)
    (hversion : factorizationVersion ≠ 0)
    (hreceipt : receipt ≠ 0)
    (hfactorizationReceipt : factorizationReceipt ≠ 0)
    (hfactorizationAuthority : factorizationAuthority ≠ 0)
    (hauthority : factorizationAuthority ≠ selectorAuthority) :
    let calibrationAuthorization : CalibrationAuthorization :=
      ⟨receipt, calibration, calibration.authority⟩
    let factorizationAuthorization : FactorizationAuthorization :=
      ⟨factorizationReceipt, factorizationIdentity, factorizationVersion,
        factorizationAuthority, .completionThenConditionalRelevance⟩
    let certificate : Certificate :=
      ⟨calibration, selectorAuthority, factorizationIdentity, factorizationVersion,
        factorizationAuthority, receipt, factorizationReceipt⟩
    certificate.Valid [calibrationAuthorization] [factorizationAuthorization] := by
  simp [Certificate.Valid, CalibrationAuthorized, FactorizationAuthorized,
    hcalibration, hfactorization, hversion, hreceipt, hfactorizationReceipt,
    hfactorizationAuthority, hauthority]

theorem self_authorized_calibration_invalid
    (calibrationRegistry : List CalibrationAuthorization)
    (factorizationRegistry : List FactorizationAuthorization) (certificate : Certificate)
    (hself : certificate.selectorAuthority = certificate.calibration.authority) :
    ¬ certificate.Valid calibrationRegistry factorizationRegistry := by
  intro h
  exact h.1.2.2.2.2.1 hself.symm

theorem matching_calibration_singleton_authorized
    (authorization : CalibrationAuthorization)
    (hreceipt : authorization.receipt ≠ 0)
    (hauthority : authorization.authorizedBy = authorization.calibration.authority) :
    CalibrationAuthorized [authorization] authorization.receipt authorization.calibration := by
  exact ⟨hreceipt, authorization, by simp, rfl, rfl, hauthority⟩

theorem substituted_calibration_not_authorized
    (authorization : CalibrationAuthorization) (receipt : Id)
    (certificateCalibration : RelevanceCalibration)
    (_hreceipt : authorization.receipt = receipt) (_hreceiptPresent : receipt ≠ 0)
    (_hauthority : authorization.authorizedBy = certificateCalibration.authority)
    (hsubstitution : authorization.calibration ≠ certificateCalibration) :
    ¬ CalibrationAuthorized [authorization] receipt certificateCalibration := by
  intro h
  rcases h with ⟨_, registered, member, _, heq, _⟩
  simp only [List.mem_singleton] at member
  subst registered
  exact hsubstitution heq

theorem matching_factorization_singleton_authorized
    (authorization : FactorizationAuthorization) (selectorAuthority : Id)
    (hidentity : authorization.identity ≠ 0) (hversion : authorization.version ≠ 0)
    (hauthority : authorization.authority ≠ 0)
    (hreceipt : authorization.receipt ≠ 0)
    (hseparate : authorization.authority ≠ selectorAuthority)
    (hlaw : authorization.law = .completionThenConditionalRelevance) :
    FactorizationAuthorized [authorization] selectorAuthority authorization.identity
      authorization.version authorization.authority authorization.receipt := by
  exact ⟨hidentity, hversion, hauthority, hreceipt, authorization, by simp,
    rfl, rfl, rfl, rfl, hseparate, hlaw⟩

theorem substituted_factorization_not_authorized
    (authorization : FactorizationAuthorization) (selectorAuthority identity : Id)
    (version : Nat) (authority receipt : Id)
    (_hidentityPresent : identity ≠ 0) (_hversionPresent : version ≠ 0)
    (_hauthorityPresent : authority ≠ 0) (_hreceiptPresent : receipt ≠ 0)
    (_hreceipt : authorization.receipt = receipt)
    (_hauthority : authorization.authority = authority)
    (_hseparate : authorization.authority ≠ selectorAuthority)
    (_hlaw : authorization.law = .completionThenConditionalRelevance)
    (hidentity : authorization.identity ≠ identity ∨ authorization.version ≠ version) :
    ¬ FactorizationAuthorized [authorization] selectorAuthority identity version authority receipt := by
  intro h
  rcases h with ⟨_, _, _, _, registered, member, _, hid, hver, _⟩
  simp only [List.mem_singleton] at member
  subst registered
  exact hidentity.elim (fun bad => bad hid) (fun bad => bad hver)

theorem unauthorized_factorization_invalid
    (calibrationRegistry : List CalibrationAuthorization) (certificate : Certificate) :
    ¬ certificate.Valid calibrationRegistry [] := by
  intro h
  rcases h.2.2 with ⟨_, _, _, _, authorization, member, _⟩
  simp at member

end DarkTower.WarMachine.FactorizedPreferenceSemantics
