import DarkTower.WarMachine.MedicLedgerBridge

/-!
# Guarded same-cause recurrence after medic coverage

The guard is derived from the actual bridge projection: the bound predecessor
must be `latestFor`, and its exact occurrence must be in projected corrections.
No caller-supplied `cleared` Boolean exists.

Futon2's current `append-retry-result` strips `:new-cause-pin` at attempt-limit
exhaustion.  Medic recurrence needs the fresh classified cause as evidence, so
this proposed model retains it in the exhausted result and inactive transition.
That is an explicit integration choice still requiring code review, not a claim
about current runtime behavior.
-/

namespace DarkTower.WarMachine.MedicRecurrence

open HistoricalMisclassificationCorrection
open MedicLedgerBridge

abbrev RecordPin := Nat
abbrev ClickId := Nat

inductive Origin where
  | open
  | enacted (retryClick : ClickId)
  deriving DecidableEq, Repr

structure LatestBinding where
  entry : InjuryEntry
  attempt : Nat
  origin : Origin
  deriving DecidableEq, Repr

structure InjuryClassification where
  injury : InjuryId
  recordPin : RecordPin
  click : ClickId
  deriving DecidableEq, Repr

structure RecurrenceRequest where
  latest : LatestBinding
  classification : InjuryClassification
  freshEntry : InjuryEntry
  attemptLimit : Nat
  seenRecords : List RecordPin
  deriving DecidableEq, Repr

inductive RecurrenceStatus where
  | duplicate | attributableRetry | refused | reopened | exhausted
  deriving DecidableEq, Repr

structure RecurrenceResult where
  status : RecurrenceStatus
  ledger : List LedgerEntry
  attempt : Nat
  freshCause : Option RecordPin

def actuallyCovered (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (ledger : List LedgerEntry)
    (latest : InjuryEntry) : Bool :=
  let state := project misclassification genuine ledger
  decide (latestFor state.history latest.injury = some latest) &&
  decide (latest.occurrence ∈ state.corrections.map MedicCorrection.occurrence)

def validFreshEntry (request : RecurrenceRequest) : Bool :=
  request.freshEntry.injury = request.latest.entry.injury &&
  request.freshEntry.predecessor = request.latest.entry.entry &&
  request.freshEntry.entry ≠ request.latest.entry.entry &&
  request.freshEntry.causePin = request.classification.recordPin &&
  request.freshEntry.active

def recurrenceGuard (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (ledger : List LedgerEntry)
    (request : RecurrenceRequest) : RecurrenceResult :=
  if request.classification.injury ≠ request.latest.entry.injury ||
     ! actuallyCovered misclassification genuine ledger request.latest.entry ||
     ! validFreshEntry request then
    ⟨.refused, ledger, request.latest.attempt, none⟩
  else
    let nextAttempt := request.latest.attempt + 1
    if nextAttempt > request.attemptLimit then
      let exhaustedEntry := { request.freshEntry with active := false }
      ⟨.exhausted, .transition exhaustedEntry :: ledger,
        request.attemptLimit, some request.classification.recordPin⟩
    else
      ⟨.reopened, .transition request.freshEntry :: ledger,
        nextAttempt, some request.classification.recordPin⟩

def integrateRecurrence (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (ledger : List LedgerEntry)
    (request : RecurrenceRequest) : RecurrenceResult :=
  if request.classification.recordPin ∈ request.seenRecords then
    ⟨.duplicate, ledger, request.latest.attempt, none⟩
  else match request.latest.origin with
    | .enacted retryClick =>
        if request.classification.click = retryClick then
          ⟨.attributableRetry, ledger, request.latest.attempt, none⟩
        else recurrenceGuard misclassification genuine ledger request
    | .open => recurrenceGuard misclassification genuine ledger request

theorem old_record_replay_inert
    (request : RecurrenceRequest)
    (seen : request.classification.recordPin ∈ request.seenRecords) :
    integrateRecurrence misclassification genuine ledger request =
      ⟨.duplicate, ledger, request.latest.attempt, none⟩ := by
  simp [integrateRecurrence, seen]

theorem exact_attributable_retry_preserved
    (request : RecurrenceRequest) (retryClick : ClickId)
    (origin : request.latest.origin = .enacted retryClick)
    (fresh : request.classification.recordPin ∉ request.seenRecords)
    (click : request.classification.click = retryClick) :
    integrateRecurrence misclassification genuine ledger request =
      ⟨.attributableRetry, ledger, request.latest.attempt, none⟩ := by
  simp [integrateRecurrence, fresh, origin, click]

theorem reopened_has_increment_and_fresh_cause
    (request : RecurrenceRequest)
    (h : (integrateRecurrence misclassification genuine ledger request).status =
      .reopened) :
    (integrateRecurrence misclassification genuine ledger request).attempt =
        request.latest.attempt + 1 ∧
      (integrateRecurrence misclassification genuine ledger request).freshCause =
        some request.classification.recordPin := by
  unfold integrateRecurrence recurrenceGuard at h ⊢
  grind

theorem reopened_appends_exact_fresh_occurrence
    (request : RecurrenceRequest)
    (h : (integrateRecurrence misclassification genuine ledger request).status =
      .reopened) :
    (integrateRecurrence misclassification genuine ledger request).ledger =
      .transition request.freshEntry :: ledger := by
  unfold integrateRecurrence recurrenceGuard at h ⊢
  grind

theorem exhausted_retains_cause_and_is_not_repair
    (request : RecurrenceRequest)
    (h : (integrateRecurrence misclassification genuine ledger request).status =
      .exhausted) :
    (integrateRecurrence misclassification genuine ledger request).freshCause =
        some request.classification.recordPin ∧
      (integrateRecurrence misclassification genuine ledger request).status ≠
        .reopened := by
  unfold integrateRecurrence recurrenceGuard at h ⊢
  grind

theorem exhausted_appends_inactive_fresh_occurrence
    (request : RecurrenceRequest)
    (h : (integrateRecurrence misclassification genuine ledger request).status =
      .exhausted) :
    (integrateRecurrence misclassification genuine ledger request).ledger =
        .transition { request.freshEntry with active := false } :: ledger ∧
      (integrateRecurrence misclassification genuine ledger request).attempt =
        request.attemptLimit := by
  unfold integrateRecurrence recurrenceGuard at h ⊢
  grind

theorem retry_closing_law_unchanged (b : Bool) (o : SelfHealRoute.RetryClickOutcome) :
    o.closing b = SelfHealRoute.ClosingStatus.discharged ↔
      o = .successfulTaskOutcome :=
  SelfHealRoute.closing_dischargesOnlyOnSuccess b o

/-! Full-field controls over the accepted bridge fixture. -/

def recurrenceFresh : InjuryEntry :=
  ⟨MedicLedgerBridge.current.injury, 12, MedicLedgerBridge.current.entry,
    MedicLedgerBridge.current.causeRecord, 99, true⟩

def openRequest : RecurrenceRequest :=
  ⟨⟨MedicLedgerBridge.current, 1, .open⟩,
    ⟨MedicLedgerBridge.current.injury, 99, 501⟩, recurrenceFresh, 3, [41]⟩

def enactedRequest : RecurrenceRequest :=
  { openRequest with latest := ⟨MedicLedgerBridge.current, 1, .enacted 700⟩ }

example : actuallyCovered MedicLedgerBridge.authority MedicLedgerBridge.noGenuine
    MedicLedgerBridge.appendedLedger MedicLedgerBridge.current = true := by native_decide

example : (integrateRecurrence MedicLedgerBridge.authority MedicLedgerBridge.noGenuine
    MedicLedgerBridge.appendedLedger openRequest).status = .reopened := by native_decide

example : (integrateRecurrence MedicLedgerBridge.authority MedicLedgerBridge.noGenuine
    MedicLedgerBridge.appendedLedger enactedRequest).status = .reopened := by native_decide

def exactRetry : RecurrenceRequest :=
  { enactedRequest with classification := { enactedRequest.classification with click := 700 } }

example : (integrateRecurrence MedicLedgerBridge.authority MedicLedgerBridge.noGenuine
    MedicLedgerBridge.appendedLedger exactRetry).status = .attributableRetry := by native_decide

def duplicateRequest : RecurrenceRequest :=
  { openRequest with seenRecords := [99] }

example : (integrateRecurrence MedicLedgerBridge.authority MedicLedgerBridge.noGenuine
    MedicLedgerBridge.appendedLedger duplicateRequest).status = .duplicate := by native_decide

def exhaustedRequest : RecurrenceRequest :=
  { openRequest with latest := ⟨MedicLedgerBridge.current, 3, .open⟩ }

example : (integrateRecurrence MedicLedgerBridge.authority MedicLedgerBridge.noGenuine
    MedicLedgerBridge.appendedLedger exhaustedRequest).status = .exhausted := by native_decide

def staleLedger : List LedgerEntry := [.transition recurrenceFresh] ++ MedicLedgerBridge.appendedLedger

example : (integrateRecurrence MedicLedgerBridge.authority MedicLedgerBridge.noGenuine
    staleLedger openRequest).status = .refused := by native_decide

example : recurrenceFresh.occurrence ∈ effectiveActive MedicLedgerBridge.authority
    MedicLedgerBridge.noGenuine
    (integrateRecurrence MedicLedgerBridge.authority MedicLedgerBridge.noGenuine
      MedicLedgerBridge.appendedLedger openRequest).ledger := by native_decide

end DarkTower.WarMachine.MedicRecurrence
