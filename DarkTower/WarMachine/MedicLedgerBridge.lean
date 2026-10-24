import DarkTower.WarMachine.MedicSweepProvenance

/-!
# Append-only medic ledger bridge

An interleaved ledger projects to the existing `MedicState`.  Transition rows
append history, admitted medic rows run the existing `medicProcess`, and audit
rows are inert.  Root hashes, predecessor seals, ordinal uniqueness, and
authority authenticity remain supplied premises; no Boolean field proves them.

This module does not model terminal-injury recurrence or retry budgets.
-/

namespace DarkTower.WarMachine.MedicLedgerBridge

open HistoricalMisclassificationCorrection

abbrev Root := Nat
abbrev OperationId := Nat

structure MedicOperation where
  operationId : OperationId
  expectedRoot : Root
  request : MedicRequest

inductive LedgerEntry where
  | transition (entry : InjuryEntry)
  | medic (operation : MedicOperation)
  | audit (auditId : Nat)

/-- The formal list is newest-first. Runtime append vectors are oldest-first
and must pass through this explicit adapter. -/
def fromChronological (entries : List LedgerEntry) : List LedgerEntry := entries.reverse

def requestEq (left right : MedicRequest) : Bool :=
  decide (left.candidate = right.candidate) && decide (left.evidence = right.evidence)

def operationEq (left right : MedicOperation) : Bool :=
  decide (left.operationId = right.operationId) &&
  decide (left.expectedRoot = right.expectedRoot) && requestEq left.request right.request

def sameOccurrence (left right : MedicRequest) : Bool :=
  decide (left.candidate.occurrence = right.candidate.occurrence)

def project (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) : List LedgerEntry → MedicState
  | [] => ⟨[], []⟩
  | entry :: rest =>
      let before := project misclassification genuine rest
      match entry with
      | .transition transition => { before with history := before.history ++ [transition] }
      | .medic operation =>
          (medicProcess misclassification genuine operation.request.evidence before
            operation.request.candidate).state
      | .audit _ => before

def effectiveActive (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (ledger : List LedgerEntry) : List Occurrence :=
  medicEffectiveActiveOccurrences (project misclassification genuine ledger)

inductive ValidLedger (root : List LedgerEntry → Root)
    (prefixValid : List LedgerEntry → Prop)
    (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) : List LedgerEntry → Prop
  | nil (emptyValid : prefixValid []) : ValidLedger root prefixValid misclassification genuine []
  | transition {ledger : List LedgerEntry}
      (valid : ValidLedger root prefixValid misclassification genuine ledger)
      (entry : InjuryEntry)
      (ordinalUnique : ∀ old ∈ (project misclassification genuine ledger).history,
        old.entry ≠ entry.entry)
      (predecessorValid :
        (entry.predecessor = 0 ∧ latestFor
          (project misclassification genuine ledger).history entry.injury = none) ∨
        ∃ old, latestFor (project misclassification genuine ledger).history entry.injury =
          some old ∧ old.entry = entry.predecessor)
      (prefixProof : prefixValid (.transition entry :: ledger)) :
      ValidLedger root prefixValid misclassification genuine (.transition entry :: ledger)
  | audit {ledger : List LedgerEntry}
      (valid : ValidLedger root prefixValid misclassification genuine ledger)
      (auditId : Nat) (prefixProof : prefixValid (.audit auditId :: ledger)) :
      ValidLedger root prefixValid misclassification genuine (.audit auditId :: ledger)
  | medic {ledger : List LedgerEntry}
      (valid : ValidLedger root prefixValid misclassification genuine ledger)
      (operation : MedicOperation)
      (rootMatches : operation.expectedRoot = root ledger)
      (current : InjuryEntry) (evidence : MedicEvidence)
      (present : operation.request.evidence = some evidence)
      (latest : latestFor (project misclassification genuine ledger).history
        operation.request.candidate.injury = some current)
      (authority : medicQualified misclassification genuine current
        operation.request.candidate evidence = true)
      (fresh : ∀ prior, LedgerEntry.medic prior ∈ ledger →
        prior.request.candidate.occurrence ≠ operation.request.candidate.occurrence)
      (prefixProof : prefixValid (.medic operation :: ledger)) :
      ValidLedger root prefixValid misclassification genuine (.medic operation :: ledger)

theorem effectiveActive_eq_landed
    (_valid : ValidLedger root prefixValid misclassification genuine ledger) :
    effectiveActive misclassification genuine ledger =
      medicEffectiveActiveOccurrences (project misclassification genuine ledger) := rfl

theorem audit_projection_inert :
    project misclassification genuine (.audit auditId :: ledger) =
      project misclassification genuine ledger := rfl

inductive AppendStatus where | appended | duplicate | stale | conflict | refused
  deriving DecidableEq, Repr

structure AppendResult where
  status : AppendStatus
  ledger : List LedgerEntry

def exactOperationPresent (ledger : List LedgerEntry) (operation : MedicOperation) : Bool :=
  ledger.any (fun entry => match entry with
    | .medic prior => operationEq prior operation
    | _ => false)

def occurrencePresent (ledger : List LedgerEntry) (request : MedicRequest) : Bool :=
  ledger.any (fun entry => match entry with
    | .medic prior => sameOccurrence prior.request request
    | _ => false)

def appendMedic (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (root : List LedgerEntry → Root)
    (ledger : List LedgerEntry) (operation : MedicOperation) : AppendResult :=
  if exactOperationPresent ledger operation then ⟨.duplicate, ledger⟩
  else if operation.expectedRoot ≠ root ledger then ⟨.stale, ledger⟩
  else
    let before := project misclassification genuine ledger
    match latestFor before.history operation.request.candidate.injury,
        operation.request.evidence with
    | some current, some evidence =>
        if ! medicQualified misclassification genuine current
            operation.request.candidate evidence then ⟨.refused, ledger⟩
        else if occurrencePresent ledger operation.request then ⟨.conflict, ledger⟩
        else
          let processed := medicProcess misclassification genuine
            operation.request.evidence before operation.request.candidate
          if processed.outcome = .appended then ⟨.appended, .medic operation :: ledger⟩
          else ⟨.refused, ledger⟩
    | _, _ => ⟨.refused, ledger⟩

theorem exact_replay_before_stale
    (present : exactOperationPresent ledger operation = true) :
    appendMedic misclassification genuine root ledger operation = ⟨.duplicate, ledger⟩ := by
  simp [appendMedic, present]

theorem changed_operation_stale_before_conflict
    (notExact : exactOperationPresent ledger operation = false)
    (stale : operation.expectedRoot ≠ root ledger) :
    appendMedic misclassification genuine root ledger operation = ⟨.stale, ledger⟩ := by
  simp [appendMedic, notExact, stale]

theorem appendMedic_appended_admission
    (h : appendMedic misclassification genuine root ledger operation =
      ⟨.appended, .medic operation :: ledger⟩) :
    operation.expectedRoot = root ledger ∧
      ∃ current evidence,
        operation.request.evidence = some evidence ∧
        latestFor (project misclassification genuine ledger).history
          operation.request.candidate.injury = some current ∧
        medicQualified misclassification genuine current
          operation.request.candidate evidence = true ∧
        occurrencePresent ledger operation.request = false ∧
        (medicProcess misclassification genuine operation.request.evidence
          (project misclassification genuine ledger)
          operation.request.candidate).outcome = .appended := by
  unfold appendMedic at h
  grind

theorem appendMedic_appended_process
    (h : appendMedic misclassification genuine root ledger operation =
      ⟨.appended, .medic operation :: ledger⟩) :
    (medicProcess misclassification genuine operation.request.evidence
      (project misclassification genuine ledger)
      operation.request.candidate).outcome = .appended := by
  rcases appendMedic_appended_admission h with
    ⟨_, current, evidence, _, _, _, _, processed⟩
  exact processed

theorem appendMedic_preserves_validity
    (valid : ValidLedger root prefixValid misclassification genuine ledger)
    (prefixProof : prefixValid (.medic operation :: ledger))
    (h : appendMedic misclassification genuine root ledger operation =
      ⟨.appended, .medic operation :: ledger⟩) :
    ValidLedger root prefixValid misclassification genuine
      (.medic operation :: ledger) := by
  rcases appendMedic_appended_admission h with
    ⟨rootMatches, current, evidence, present, latest, qualified, freshBool, processed⟩
  apply ValidLedger.medic valid operation rootMatches current evidence present latest qualified
  · intro prior hprior same
    have : occurrencePresent ledger operation.request = true := by
      simp only [occurrencePresent, List.any_eq_true]
      refine ⟨.medic prior, hprior, ?_⟩
      simp [sameOccurrence, same]
    simp [freshBool] at this
  · exact prefixProof

theorem appended_projects_through_existing_process
    (_h : appendMedic misclassification genuine root ledger operation =
      ⟨.appended, .medic operation :: ledger⟩) :
    project misclassification genuine (.medic operation :: ledger) =
      (medicProcess misclassification genuine operation.request.evidence
        (project misclassification genuine ledger) operation.request.candidate).state := rfl

theorem fresh_transition_history_visible :
    (project misclassification genuine (.transition entry :: ledger)).history =
      (project misclassification genuine ledger).history ++ [entry] := rfl

theorem old_correction_does_not_mask_fresh_occurrence
    (old : MedicCorrection) (fresh : InjuryEntry) (state : MedicState)
    (different : old.occurrence ≠ fresh.occurrence)
    (latest : latestEntries (state.history ++ [fresh]) = [fresh])
    (active : fresh.active = true)
    (oldOnly : state.corrections.map MedicCorrection.occurrence = [old.occurrence]) :
    fresh.occurrence ∈ medicEffectiveActiveOccurrences
      { history := state.history ++ [fresh], corrections := state.corrections } := by
  simp [medicEffectiveActiveOccurrences, latest, active, oldOnly]
  exact Ne.symm different

theorem inactive_latest_not_effective
    (latest : latestEntries state.history = [entry]) (inactive : entry.active = false) :
    entry.occurrence ∉ medicEffectiveActiveOccurrences state := by
  simp [medicEffectiveActiveOccurrences, latest, inactive]

theorem retry_closing_law_unchanged (b : Bool) (o : SelfHealRoute.RetryClickOutcome) :
    o.closing b = SelfHealRoute.ClosingStatus.discharged ↔
      o = .successfulTaskOutcome :=
  SelfHealRoute.closing_dischargesOnlyOnSuccess b o

/-! Concrete controls use full ledger entries and complete medic payloads. -/

def current : InjuryEntry := ⟨7, 11, 0, 31, 41, true⟩
def fresh : InjuryEntry := ⟨7, 12, 11, 31, 42, true⟩

def payload : MisclassificationPayload :=
  ⟨current.occurrence, 0, 31, 41, 51, .producerQualifiedNonInjury, 61, 71, 72, 81⟩
def evidence : MisclassificationEvidence :=
  ⟨current.occurrence, 0, 31, 41, 51, .producerQualifiedNonInjury, 61, 71, 72, 81⟩
def request : MedicRequest :=
  ⟨.historicalMisclassification payload, some (.historicalMisclassification evidence)⟩
def authority : MisclassificationAdmission := fun _ _ _ => true
def noGenuine : GenuineRepairAdmission := fun _ _ _ => false
def root : List LedgerEntry → Root := List.length
def operation : MedicOperation := ⟨91, 1, request⟩
def baseLedger : List LedgerEntry := [.transition current]
def suppliedPrefixValidity : List LedgerEntry → Prop := fun _ => True

theorem baseLedgerValid :
    ValidLedger root suppliedPrefixValidity authority noGenuine baseLedger := by
  apply ValidLedger.transition (.nil trivial) current
  · simp [project]
  · left
    simp [project, current, latestFor, latestEntries]
  · trivial

example : (appendMedic authority noGenuine root baseLedger operation).status = .appended := by
  native_decide

theorem admitted_append_valid :
    ValidLedger root suppliedPrefixValidity authority noGenuine
      (.medic operation :: baseLedger) := by
  apply appendMedic_preserves_validity baseLedgerValid trivial
  rfl

def appendedLedger : List LedgerEntry := [.medic operation, .transition current]

def wrongRoot : MedicOperation := { operation with expectedRoot := 999 }

theorem stale_root_entry_not_valid :
    ¬ ValidLedger root suppliedPrefixValidity authority noGenuine
      (.medic wrongRoot :: baseLedger) := by
  intro valid
  cases valid with
  | medic _ _ rootMatches _ _ _ _ _ _ _ => simp [wrongRoot, root, baseLedger] at rootMatches

example : (appendMedic authority noGenuine root appendedLedger operation).status = .duplicate := by
  native_decide

def forgedSameId : MedicOperation :=
  ⟨91, 2, { request with candidate := .historicalMisclassification { payload with patch := 62 } }⟩

example : exactOperationPresent appendedLedger forgedSameId = false := by native_decide
example : (appendMedic authority noGenuine root appendedLedger forgedSameId).status = .refused := by
  native_decide

def staleNew : MedicOperation := ⟨92, 1, request⟩
example : (appendMedic authority noGenuine root appendedLedger staleNew).status = .stale := by
  native_decide

def conflictPayload : MisclassificationPayload := { payload with patch := 62 }
def conflictEvidence : MisclassificationEvidence := { evidence with patch := 62 }
def conflictRequest : MedicRequest :=
  ⟨.historicalMisclassification conflictPayload,
    some (.historicalMisclassification conflictEvidence)⟩
def conflictOp : MedicOperation := ⟨92, 2, conflictRequest⟩
example : (appendMedic authority noGenuine root appendedLedger conflictOp).status = .conflict := by
  native_decide

example : fresh.occurrence ∈ effectiveActive authority noGenuine
    (.transition fresh :: appendedLedger) := by native_decide

example : project authority noGenuine (.audit 99 :: appendedLedger) =
    project authority noGenuine appendedLedger := rfl

def current2 : InjuryEntry := ⟨8, 21, 0, 32, 43, true⟩
def payload2 : MisclassificationPayload :=
  ⟨current2.occurrence, 0, 32, 43, 52, .producerQualifiedNonInjury, 63, 73, 74, 82⟩
def evidence2 : MisclassificationEvidence :=
  ⟨current2.occurrence, 0, 32, 43, 52, .producerQualifiedNonInjury, 63, 73, 74, 82⟩
def request2 : MedicRequest :=
  ⟨.historicalMisclassification payload2,
    some (.historicalMisclassification evidence2)⟩
def baseTwo : List LedgerEntry := [.transition current2, .transition current]
def op1Two : MedicOperation := ⟨101, 2, request⟩
def partialLedger : List LedgerEntry := [.medic op1Two, .transition current2, .transition current]
def op2Two : MedicOperation := ⟨102, 3, request2⟩
def allLedger : List LedgerEntry :=
  [.medic op2Two, .medic op1Two, .transition current2, .transition current]

example : (appendMedic authority noGenuine root baseTwo op1Two).status = .appended := by
  native_decide
example : effectiveActive authority noGenuine partialLedger = [current2.occurrence] := by
  native_decide
example : (appendMedic authority noGenuine root partialLedger op2Two).status = .appended := by
  native_decide
example : effectiveActive authority noGenuine allLedger = [] := by native_decide

end DarkTower.WarMachine.MedicLedgerBridge
