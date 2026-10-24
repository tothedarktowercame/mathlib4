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

/-!
`InjuryEntry` deliberately has no attempt, origin, limit, or retained
classification fields.  A runtime adapter must therefore supply and validate
those fields.  `SnapshotAuthority` is that explicit boundary; it is not
derived from a payload Boolean and this module makes no authenticity claim.
The remaining fields that *are* present in the projected ledger are checked
again by `BoundAdmission`.
-/

structure AuthoritativeSnapshot where
  latest : LatestBinding
  attemptLimit : Nat
  seenRecords : List RecordPin
  deriving DecidableEq, Repr

abbrev SnapshotAuthority := List LedgerEntry → AuthoritativeSnapshot → Bool

structure BoundRecurrenceRequest where
  snapshot : AuthoritativeSnapshot
  classification : InjuryClassification
  freshEntry : InjuryEntry
  deriving DecidableEq, Repr

def asRecurrenceRequest (request : BoundRecurrenceRequest) : RecurrenceRequest :=
  ⟨request.snapshot.latest, request.classification, request.freshEntry,
    request.snapshot.attemptLimit, request.snapshot.seenRecords⟩

def boundAdmission (snapshotAuthority : SnapshotAuthority)
    (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (ledger : List LedgerEntry)
    (request : BoundRecurrenceRequest) : Bool :=
  snapshotAuthority ledger request.snapshot &&
  decide (latestFor (project misclassification genuine ledger).history
    request.classification.injury = some request.snapshot.latest.entry) &&
  decide (request.snapshot.seenRecords =
    (project misclassification genuine ledger).history.map InjuryEntry.causePin) &&
  decide (request.classification.injury = request.snapshot.latest.entry.injury) &&
  decide (request.freshEntry.predecessor = request.snapshot.latest.entry.entry) &&
  (project misclassification genuine ledger).history.all
    (fun old => decide (old.entry ≠ request.freshEntry.entry)) &&
  decide (request.freshEntry.entry ≠ request.snapshot.latest.entry.entry) &&
  decide (request.freshEntry.injury = request.snapshot.latest.entry.injury) &&
  decide (request.freshEntry.causePin = request.classification.recordPin) &&
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

def integrateBoundRecurrence (snapshotAuthority : SnapshotAuthority)
    (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (ledger : List LedgerEntry)
    (request : BoundRecurrenceRequest) : RecurrenceResult :=
  if boundAdmission snapshotAuthority misclassification genuine ledger request then
    integrateRecurrence misclassification genuine ledger (asRecurrenceRequest request)
  else
    ⟨.refused, ledger, request.snapshot.latest.attempt, none⟩

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

theorem unbound_snapshot_refuses
    (request : BoundRecurrenceRequest)
    (h : boundAdmission snapshotAuthority misclassification genuine ledger request = false) :
    integrateBoundRecurrence snapshotAuthority misclassification genuine ledger request =
      ⟨.refused, ledger, request.snapshot.latest.attempt, none⟩ := by
  simp [integrateBoundRecurrence, h]

theorem bound_reopened_preserves_valid_ledger
    (request : BoundRecurrenceRequest)
    (valid : ValidLedger root prefixValid misclassification genuine ledger)
    (actualLatest : latestFor (project misclassification genuine ledger).history
      request.classification.injury = some request.snapshot.latest.entry)
    (sameInjury : request.classification.injury = request.snapshot.latest.entry.injury)
    (predecessor : request.freshEntry.predecessor = request.snapshot.latest.entry.entry)
    (ordinalFresh : ∀ old ∈ (project misclassification genuine ledger).history,
      old.entry ≠ request.freshEntry.entry)
    (freshInjury : request.freshEntry.injury = request.snapshot.latest.entry.injury)
    (prefixProof : prefixValid (.transition request.freshEntry :: ledger))
    (h : (integrateBoundRecurrence snapshotAuthority misclassification genuine ledger
      request).status = .reopened) :
    ValidLedger root prefixValid misclassification genuine
      (.transition request.freshEntry :: ledger) := by
  have admitted : boundAdmission snapshotAuthority misclassification genuine ledger request =
      true := by
    cases ha : boundAdmission snapshotAuthority misclassification genuine ledger request with
    | false => simp [integrateBoundRecurrence, ha] at h
    | true => rfl
  have routed : (integrateRecurrence misclassification genuine ledger
      (asRecurrenceRequest request)).status = .reopened := by
    simpa [integrateBoundRecurrence, admitted] using h
  apply ValidLedger.transition valid request.freshEntry
  · exact ordinalFresh
  · right
    refine ⟨request.snapshot.latest.entry, ?_, predecessor.symm⟩
    simpa [sameInjury, freshInjury] using actualLatest
  · exact prefixProof

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

/-! Executable authoritative-adapter controls.  The fixture authority stands
for a runtime adapter check; it is deliberately external to ledger projection. -/

def openSnapshot : AuthoritativeSnapshot :=
  ⟨⟨MedicLedgerBridge.current, 1, .open⟩, 3, [41]⟩

def enactedSnapshot : AuthoritativeSnapshot :=
  ⟨⟨MedicLedgerBridge.current, 1, .enacted 700⟩, 3, [41]⟩

def exhaustedSnapshot : AuthoritativeSnapshot :=
  ⟨⟨MedicLedgerBridge.current, 3, .open⟩, 3, [41]⟩

def fixtureSnapshotAuthority : SnapshotAuthority := fun ledger snapshot =>
  decide (ledger.length = MedicLedgerBridge.appendedLedger.length) &&
  decide (snapshot = openSnapshot ∨ snapshot = enactedSnapshot ∨ snapshot = exhaustedSnapshot)

def boundOpenRequest : BoundRecurrenceRequest :=
  ⟨openSnapshot, openRequest.classification, recurrenceFresh⟩

def boundEnactedRequest : BoundRecurrenceRequest :=
  ⟨enactedSnapshot, enactedRequest.classification, recurrenceFresh⟩

def boundExactRetry : BoundRecurrenceRequest :=
  { boundEnactedRequest with classification := exactRetry.classification }

example : (integrateBoundRecurrence fixtureSnapshotAuthority MedicLedgerBridge.authority
    MedicLedgerBridge.noGenuine MedicLedgerBridge.appendedLedger boundOpenRequest).status =
    .reopened := by native_decide

example : (integrateBoundRecurrence fixtureSnapshotAuthority MedicLedgerBridge.authority
    MedicLedgerBridge.noGenuine MedicLedgerBridge.appendedLedger boundExactRetry).status =
    .attributableRetry := by native_decide

def boundOriginalReplay : BoundRecurrenceRequest :=
  { boundOpenRequest with
    classification := { boundOpenRequest.classification with recordPin := 41 }
    freshEntry := { recurrenceFresh with causePin := 41 } }

example : (integrateBoundRecurrence fixtureSnapshotAuthority MedicLedgerBridge.authority
    MedicLedgerBridge.noGenuine MedicLedgerBridge.appendedLedger boundOriginalReplay).status =
    .duplicate := by native_decide

def callerAttemptMutation : BoundRecurrenceRequest :=
  { boundOpenRequest with snapshot :=
      { boundOpenRequest.snapshot with latest :=
          { boundOpenRequest.snapshot.latest with attempt := 0 } } }

example : (integrateBoundRecurrence fixtureSnapshotAuthority MedicLedgerBridge.authority
    MedicLedgerBridge.noGenuine MedicLedgerBridge.appendedLedger callerAttemptMutation).status =
    .refused := by native_decide

example : (integrateBoundRecurrence fixtureSnapshotAuthority MedicLedgerBridge.authority
    MedicLedgerBridge.noGenuine staleLedger boundExactRetry).status = .refused := by native_decide

def reusedOrdinal : BoundRecurrenceRequest :=
  { boundOpenRequest with freshEntry := { recurrenceFresh with entry := MedicLedgerBridge.current.entry } }

example : (integrateBoundRecurrence fixtureSnapshotAuthority MedicLedgerBridge.authority
    MedicLedgerBridge.noGenuine MedicLedgerBridge.appendedLedger reusedOrdinal).status =
    .refused := by native_decide

end DarkTower.WarMachine.MedicRecurrence
