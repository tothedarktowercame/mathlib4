import DarkTower.WarMachine.SelfHealRoute

/-!
# Proposed medic-repaired disposition

Candidate policy only.  A qualified append-only disposition excludes one exact
latest injury occurrence from the effective active set.  Historical
misclassification and genuine external repair are distinct evidence kinds.
Neither asserts task success or creates learning credit.  Authority and pin
authenticity are supplied admission predicates, not payload self-attestation.
-/

namespace DarkTower.WarMachine.HistoricalMisclassificationCorrection

abbrev InjuryId := Nat
abbrev EntryId := Nat
abbrev RecordId := Nat
abbrev Pin := Nat
abbrev Revision := Nat
abbrev PatchId := Nat
abbrev Principal := Nat

structure Occurrence where
  injury : InjuryId
  entry : EntryId
  deriving DecidableEq, Repr

structure InjuryEntry where
  injury : InjuryId
  entry : EntryId
  predecessor : EntryId
  causeRecord : RecordId
  causePin : Pin
  active : Bool
  deriving DecidableEq, Repr

def InjuryEntry.occurrence (entry : InjuryEntry) : Occurrence :=
  ⟨entry.injury, entry.entry⟩

inductive ReplayResult where
  | producerQualifiedNonInjury
  | unsupportedAuthorRefusal
  | doneAtBaseRevision
  | injury
  deriving DecidableEq, Repr

structure MisclassificationPayload where
  occurrence : Occurrence
  predecessor : EntryId
  originalRecord : RecordId
  originalPin : Pin
  classifierRevision : Revision
  replay : ReplayResult
  patch : PatchId
  reviewer : Principal
  evaluator : Principal
  evidencePin : Pin
  deriving DecidableEq, Repr

structure MisclassificationEvidence where
  occurrence : Occurrence
  predecessor : EntryId
  originalRecord : RecordId
  originalPin : Pin
  classifierRevision : Revision
  replay : ReplayResult
  patch : PatchId
  reviewer : Principal
  evaluator : Principal
  evidencePin : Pin
  deriving DecidableEq, Repr

structure GenuineRepairPayload where
  occurrence : Occurrence
  predecessor : EntryId
  causeRecord : RecordId
  causePin : Pin
  acceptanceContract : Pin
  preReplayReceipt : Pin
  postReplayReceipt : Pin
  negativeControlReceipt : Pin
  patch : PatchId
  sourceRevision : Revision
  evaluator : Principal
  reviewer : Principal
  originalAcceptanceRepaired : Bool
  deriving DecidableEq, Repr

structure GenuineRepairEvidence where
  occurrence : Occurrence
  predecessor : EntryId
  causeRecord : RecordId
  causePin : Pin
  acceptanceContract : Pin
  preReplayReceipt : Pin
  postReplayReceipt : Pin
  negativeControlReceipt : Pin
  patch : PatchId
  sourceRevision : Revision
  evaluator : Principal
  reviewer : Principal
  originalAcceptanceRepaired : Bool
  deriving DecidableEq, Repr

inductive MedicCorrection where
  | historicalMisclassification (payload : MisclassificationPayload)
  | genuineDefect (payload : GenuineRepairPayload)
  deriving DecidableEq, Repr

inductive MedicEvidence where
  | historicalMisclassification (evidence : MisclassificationEvidence)
  | genuineDefect (evidence : GenuineRepairEvidence)
  deriving DecidableEq, Repr

def MedicCorrection.occurrence : MedicCorrection → Occurrence
  | .historicalMisclassification payload => payload.occurrence
  | .genuineDefect payload => payload.occurrence

def MedicCorrection.injury (candidate : MedicCorrection) : InjuryId :=
  candidate.occurrence.injury

def upsertLatest (entries : List InjuryEntry) (entry : InjuryEntry) : List InjuryEntry :=
  entries.filter (fun old => old.injury != entry.injury) ++ [entry]

def latestEntries (history : List InjuryEntry) : List InjuryEntry :=
  history.foldl upsertLatest []

def latestFor (history : List InjuryEntry) (injury : InjuryId) : Option InjuryEntry :=
  (latestEntries history).find? (fun entry => entry.injury = injury)

abbrev MisclassificationAdmission :=
  InjuryEntry → MisclassificationPayload → MisclassificationEvidence → Bool
abbrev GenuineRepairAdmission :=
  InjuryEntry → GenuineRepairPayload → GenuineRepairEvidence → Bool

def exactMisclassificationBinding (payload : MisclassificationPayload)
    (evidence : MisclassificationEvidence) : Bool := decide (payload = {
  occurrence := evidence.occurrence
  predecessor := evidence.predecessor
  originalRecord := evidence.originalRecord
  originalPin := evidence.originalPin
  classifierRevision := evidence.classifierRevision
  replay := evidence.replay
  patch := evidence.patch
  reviewer := evidence.reviewer
  evaluator := evidence.evaluator
  evidencePin := evidence.evidencePin })

def exactGenuineBinding (payload : GenuineRepairPayload)
    (evidence : GenuineRepairEvidence) : Bool := decide (payload = {
  occurrence := evidence.occurrence
  predecessor := evidence.predecessor
  causeRecord := evidence.causeRecord
  causePin := evidence.causePin
  acceptanceContract := evidence.acceptanceContract
  preReplayReceipt := evidence.preReplayReceipt
  postReplayReceipt := evidence.postReplayReceipt
  negativeControlReceipt := evidence.negativeControlReceipt
  patch := evidence.patch
  sourceRevision := evidence.sourceRevision
  evaluator := evidence.evaluator
  reviewer := evidence.reviewer
  originalAcceptanceRepaired := evidence.originalAcceptanceRepaired })

def misclassificationQualified (admit : MisclassificationAdmission)
    (current : InjuryEntry) (payload : MisclassificationPayload)
    (evidence : MisclassificationEvidence) : Bool :=
  current.active && decide (current.occurrence = payload.occurrence) &&
  decide (current.predecessor = payload.predecessor) &&
  decide (current.causeRecord = payload.originalRecord) &&
  decide (current.causePin = payload.originalPin) &&
  decide (payload.replay = .producerQualifiedNonInjury) &&
  decide (payload.reviewer ≠ payload.evaluator) &&
  exactMisclassificationBinding payload evidence && admit current payload evidence

def genuineQualified (admit : GenuineRepairAdmission) (current : InjuryEntry)
    (payload : GenuineRepairPayload) (evidence : GenuineRepairEvidence) : Bool :=
  current.active && decide (current.occurrence = payload.occurrence) &&
  decide (current.predecessor = payload.predecessor) &&
  decide (current.causeRecord = payload.causeRecord) &&
  decide (current.causePin = payload.causePin) &&
  payload.originalAcceptanceRepaired &&
  decide (payload.evaluator ≠ payload.reviewer) &&
  exactGenuineBinding payload evidence && admit current payload evidence

def medicQualified (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (current : InjuryEntry)
    (candidate : MedicCorrection) (evidence : MedicEvidence) : Bool :=
  match candidate, evidence with
  | .historicalMisclassification payload, .historicalMisclassification proof =>
      misclassificationQualified misclassification current payload proof
  | .genuineDefect payload, .genuineDefect proof =>
      genuineQualified genuine current payload proof
  | _, _ => false

structure MedicState where
  history : List InjuryEntry
  corrections : List MedicCorrection
  deriving DecidableEq, Repr

inductive Outcome where | appended | duplicate | conflict | refused
  deriving DecidableEq, Repr

structure MedicResult where
  outcome : Outcome
  state : MedicState
  deriving DecidableEq, Repr

def medicProcess (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (evidence : Option MedicEvidence)
    (state : MedicState) (candidate : MedicCorrection) : MedicResult :=
  match latestFor state.history candidate.injury, evidence with
  | some current, some proof =>
      if ! medicQualified misclassification genuine current candidate proof then
        ⟨.refused, state⟩
      else if candidate ∈ state.corrections then
        ⟨.duplicate, state⟩
      else if state.corrections.any
          (fun old => old.occurrence = candidate.occurrence) then
        ⟨.conflict, state⟩
      else ⟨.appended, { state with corrections := state.corrections ++ [candidate] }⟩
  | _, _ => ⟨.refused, state⟩

def medicEffectiveActiveOccurrences (state : MedicState) : List Occurrence :=
  (latestEntries state.history).filter (·.active) |>.map (·.occurrence) |>.filter
    (fun occurrence => occurrence ∉ state.corrections.map MedicCorrection.occurrence)

def medicEffectiveActive (state : MedicState) : List InjuryId :=
  (medicEffectiveActiveOccurrences state).map (·.injury)

structure MedicRequest where
  candidate : MedicCorrection
  evidence : Option MedicEvidence

def medicSweep (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) : MedicState → List MedicRequest → MedicState
  | state, [] => state
  | state, request :: rest => medicSweep misclassification genuine
      (medicProcess misclassification genuine request.evidence state request.candidate).state rest

theorem medicProcess_preserves_history :
    (medicProcess misclassification genuine evidence state candidate).state.history =
      state.history := by
  unfold medicProcess
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem missing_evidence_refuses :
    medicProcess misclassification genuine none state candidate = ⟨.refused, state⟩ := by
  simp [medicProcess]

theorem medic_appended_only_from_actual_latest
    (h : (medicProcess misclassification genuine (some evidence) state candidate).outcome =
      .appended) :
    ∃ current, latestFor state.history candidate.injury = some current ∧
      medicQualified misclassification genuine current candidate evidence = true := by
  simp only [medicProcess] at h
  split at h <;> simp_all
  split at h <;> simp_all

theorem medic_duplicate_inert
    (hlatest : latestFor state.history candidate.injury = some current)
    (hq : medicQualified misclassification genuine current candidate evidence = true)
    (hmem : candidate ∈ state.corrections) :
    medicProcess misclassification genuine (some evidence) state candidate =
      ⟨.duplicate, state⟩ := by simp [medicProcess, hlatest, hq, hmem]

theorem medic_conflict_inert
    (hlatest : latestFor state.history candidate.injury = some current)
    (hq : medicQualified misclassification genuine current candidate evidence = true)
    (hnew : candidate ∉ state.corrections)
    (hold : ∃ old ∈ state.corrections, old.occurrence = candidate.occurrence) :
    medicProcess misclassification genuine (some evidence) state candidate =
      ⟨.conflict, state⟩ := by
  simp only [medicProcess, hlatest, hq, hnew, List.any_eq_true]
  simp_all

/-! Synthetic examples.  Numerals resemble no certified live identity. -/

def a9Entry : InjuryEntry := ⟨9, 34, 33, 60, 600, true⟩
def a9Payload : MisclassificationPayload :=
  ⟨a9Entry.occurrence, 33, 60, 600, 36, .producerQualifiedNonInjury, 361, 11, 12, 700⟩
def a9Evidence : MisclassificationEvidence :=
  ⟨a9Entry.occurrence, 33, 60, 600, 36, .producerQualifiedNonInjury, 361, 11, 12, 700⟩
def otherEntry : InjuryEntry := ⟨41, 18, 17, 70, 701, true⟩
def admitA9 : MisclassificationAdmission := fun current payload evidence =>
  decide (current = a9Entry ∧ payload = a9Payload ∧ evidence = a9Evidence)

def realEntry : InjuryEntry := ⟨84, 37, 36, 25, 846, true⟩
def realRepair : GenuineRepairPayload :=
  ⟨realEntry.occurrence, 36, 25, 846, 900, 901, 902, 903, 560, 561, 21, 22, true⟩
def realEvidence : GenuineRepairEvidence :=
  ⟨realEntry.occurrence, 36, 25, 846, 900, 901, 902, 903, 560, 561, 21, 22, true⟩
def admitReal : GenuineRepairAdmission := fun current payload evidence =>
  decide (current = realEntry ∧ payload = realRepair ∧ evidence = realEvidence)

def noMisclassification : MisclassificationAdmission := fun _ _ _ => false
def noGenuine : GenuineRepairAdmission := fun _ _ _ => false
def a9Candidate := MedicCorrection.historicalMisclassification a9Payload
def a9Proof := MedicEvidence.historicalMisclassification a9Evidence
def realCandidate := MedicCorrection.genuineDefect realRepair
def realProof := MedicEvidence.genuineDefect realEvidence
def mixedInitial : MedicState := ⟨[a9Entry, realEntry, otherEntry], []⟩

theorem latest_projection_uses_last_occurrence :
    let closed := { a9Entry with entry := 35, predecessor := 34, active := false }
    latestFor [a9Entry, closed] 9 = some closed ∧
      medicEffectiveActive ⟨[a9Entry, closed], []⟩ = [] := by decide

theorem stale_actual_history_refuses_matching_old_evidence :
    let reopened := { a9Entry with entry := 35, predecessor := 34 }
    let state : MedicState := ⟨[a9Entry, reopened, otherEntry], []⟩
    (medicProcess admitA9 noGenuine (some a9Proof) state a9Candidate).outcome = .refused ∧
      medicEffectiveActive state = [9, 41] := by decide

theorem a9_composed_correction_removes_only_exact_occurrence :
    let result := medicProcess admitA9 noGenuine (some a9Proof)
      ⟨[a9Entry, otherEntry], []⟩ a9Candidate
    result.outcome = .appended ∧ result.state.history = [a9Entry, otherEntry] ∧
      medicEffectiveActive result.state = [41] := by decide

theorem later_reopening_remains_active :
    let corrected := (medicProcess admitA9 noGenuine (some a9Proof)
      ⟨[a9Entry, otherEntry], []⟩ a9Candidate).state
    let reopened := { a9Entry with entry := 35, predecessor := 34 }
    medicEffectiveActive { corrected with history := corrected.history ++ [reopened] } = [41, 9] := by decide

theorem missing_a9_evidence_refuses_and_preserves_active :
    let state : MedicState := ⟨[a9Entry, otherEntry], []⟩
    (medicProcess admitA9 noGenuine none state a9Candidate).outcome = .refused ∧
      medicEffectiveActive state = [9, 41] := by decide

theorem unsupported_refusal_and_done_base_refuse :
    let unsupported := { a9Payload with replay := .unsupportedAuthorRefusal }
    let doneBase := { a9Payload with replay := .doneAtBaseRevision }
    let state : MedicState := ⟨[a9Entry, otherEntry], []⟩
    (medicProcess admitA9 noGenuine (some a9Proof) state
      (.historicalMisclassification unsupported)).outcome = .refused ∧
    (medicProcess admitA9 noGenuine (some a9Proof) state
      (.historicalMisclassification doneBase)).outcome = .refused := by decide

theorem external_authority_cannot_bypass_historical_structure :
    let badPayload := { a9Payload with originalRecord := 999 }
    let badEvidence := { a9Evidence with originalRecord := 999 }
    let permissive : MisclassificationAdmission := fun _ _ _ => true
    let state : MedicState := ⟨[a9Entry, otherEntry], []⟩
    (medicProcess permissive noGenuine
      (some (.historicalMisclassification badEvidence)) state
      (.historicalMisclassification badPayload)).outcome = .refused := by decide

theorem duplicate_inert_and_conflict_refuses :
    let once := (medicProcess admitA9 noGenuine (some a9Proof)
      ⟨[a9Entry, otherEntry], []⟩ a9Candidate).state
    let conflict := MedicCorrection.historicalMisclassification { a9Payload with patch := 362 }
    let conflictProof := MedicEvidence.historicalMisclassification { a9Evidence with patch := 362 }
    let admitConflict : MisclassificationAdmission := fun current payload evidence =>
      decide (current = a9Entry ∧ payload = { a9Payload with patch := 362 } ∧
        evidence = { a9Evidence with patch := 362 })
    (medicProcess admitA9 noGenuine (some a9Proof) once a9Candidate).outcome = .duplicate ∧
    (medicProcess admitConflict noGenuine (some conflictProof) once conflict).outcome = .conflict := by decide

def a9Request : MedicRequest := ⟨a9Candidate, some a9Proof⟩
def realRequest : MedicRequest := ⟨realCandidate, some realProof⟩

theorem composed_medic_sweep_clears_only_qualified :
    medicEffectiveActive (medicSweep admitA9 admitReal mixedInitial
      [a9Request, realRequest]) = [41] := by decide

theorem unresolved_injury_prevents_clear_all :
    medicEffectiveActive (medicSweep admitA9 admitReal mixedInitial [a9Request]) =
      [84, 41] := by decide

theorem genuine_requires_original_acceptance_and_three_receipts :
    let badVerdict := { realRepair with originalAcceptanceRepaired := false }
    let badReceipt := { realRepair with negativeControlReceipt := 0 }
    (medicProcess noMisclassification admitReal (some realProof) mixedInitial
      (.genuineDefect badVerdict)).outcome = .refused ∧
    (medicProcess noMisclassification admitReal (some realProof) mixedInitial
      (.genuineDefect badReceipt)).outcome = .refused := by decide

/-- The proposal does not modify the established retry closing law. -/
theorem medic_preserves_success_only_retry_law (b : Bool)
    (o : SelfHealRoute.RetryClickOutcome) :
    o.closing b = SelfHealRoute.ClosingStatus.discharged ↔
      o = SelfHealRoute.RetryClickOutcome.successfulTaskOutcome :=
  SelfHealRoute.closing_dischargesOnlyOnSuccess b o

end DarkTower.WarMachine.HistoricalMisclassificationCorrection
