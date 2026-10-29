/-!
Out-of-band fixing attribution, separate from pinned-admission replay.
The Boolean checks are verifier results, not assertions supplied by an author.
A passing guard-only counterfactual cannot qualify. No historical self-heal
receipt is rewritten by this closing law.
-/
namespace DarkTower.WarMachine.OutOfBandFix

structure OutOfBandFixReceipt where
  historicalPinVerified : Bool
  historicalCauseMatches : Bool
  canonicalCommitReachable : Bool
  productionPathsNonempty : Bool
  currentSourceLoads : Bool
  currentStoreIsolated : Bool
  currentTests : Nat
  currentFailures : Nat
  currentErrors : Nat
  sameSource : Bool
  sameBase : Bool
  reverseApplySucceeded : Bool
  conflictFree : Bool
  counterfactualSourceLoads : Bool
  counterfactualStoreIsolated : Bool
  counterfactualTests : Nat
  counterfactualFailures : Nat
  counterfactualErrors : Nat
  deriving DecidableEq, Repr

def historicalChecked (r : OutOfBandFixReceipt) : Prop :=
  r.historicalPinVerified = true ∧ r.historicalCauseMatches = true

def currentChecked (r : OutOfBandFixReceipt) : Prop :=
  r.currentSourceLoads = true ∧ r.currentStoreIsolated = true ∧
  r.currentTests > 0 ∧ r.currentFailures = 0 ∧ r.currentErrors = 0

def counterfactualChecked (r : OutOfBandFixReceipt) : Prop :=
  r.canonicalCommitReachable = true ∧ r.productionPathsNonempty = true ∧
  r.sameSource = true ∧ r.sameBase = true ∧
  r.reverseApplySucceeded = true ∧ r.conflictFree = true ∧
  r.counterfactualSourceLoads = true ∧ r.counterfactualStoreIsolated = true ∧
  r.counterfactualTests > 0 ∧ r.counterfactualFailures > 0 ∧
  r.counterfactualErrors = 0

instance (r : OutOfBandFixReceipt) : Decidable (historicalChecked r) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (r : OutOfBandFixReceipt) : Decidable (currentChecked r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
instance (r : OutOfBandFixReceipt) : Decidable (counterfactualChecked r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def discharges (r : OutOfBandFixReceipt) : Bool :=
  decide (historicalChecked r ∧ currentChecked r ∧ counterfactualChecked r)

theorem outOfBandFix_dischargesIffChecked (r : OutOfBandFixReceipt) :
    discharges r = true ↔
      historicalChecked r ∧ currentChecked r ∧ counterfactualChecked r := by
  simp [discharges]

theorem outOfBandFix_guardOnlyRefused (r : OutOfBandFixReceipt)
    (h : r.counterfactualFailures = 0) : discharges r = false := by
  simp [discharges, counterfactualChecked, h]

theorem outOfBandFix_errorOnlyRefused (r : OutOfBandFixReceipt)
    (h : r.counterfactualErrors ≠ 0) : discharges r = false := by
  simp [discharges, counterfactualChecked, h]

theorem outOfBandFix_conflictRefused (r : OutOfBandFixReceipt)
    (h : r.conflictFree = false) : discharges r = false := by
  simp [discharges, counterfactualChecked, h]

/-! An open injury consults retained out-of-band evidence before diagnosis.
Absence preserves the ordinary route. A presented artifact never falls
through: malformed, mismatched, or unchecked evidence holds for inspection. -/

inductive OpenArtifact where
  | absent
  | malformed
  | mismatched
  | checked (receipt : OutOfBandFixReceipt)
  deriving DecidableEq, Repr

inductive OpenRoute where
  | diagnosis
  | hold
  | medicDischarge
  deriving DecidableEq, Repr

def routeOpen : OpenArtifact → OpenRoute
  | .absent => .diagnosis
  | .malformed => .hold
  | .mismatched => .hold
  | .checked receipt => if discharges receipt then .medicDischarge else .hold

theorem openInjury_medicDischargesIffChecked (r : OutOfBandFixReceipt) :
    routeOpen (.checked r) = .medicDischarge ↔
      historicalChecked r ∧ currentChecked r ∧ counterfactualChecked r := by
  simp [routeOpen, outOfBandFix_dischargesIffChecked]

theorem malformedArtifact_holdsBeforeDiagnosis :
    routeOpen .malformed = .hold := rfl

theorem mismatchedArtifact_holdsBeforeDiagnosis :
    routeOpen .mismatched = .hold := rfl

theorem missingArtifact_preservesDiagnosis :
    routeOpen .absent = .diagnosis := rfl

theorem uncheckedArtifact_holdsBeforeDiagnosis (r : OutOfBandFixReceipt)
    (h : discharges r = false) : routeOpen (.checked r) = .hold := by
  simp [routeOpen, h]

end DarkTower.WarMachine.OutOfBandFix
