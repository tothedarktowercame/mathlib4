import DarkTower.WarMachine.SelfHealRoute
import DarkTower.WarMachine.CloseOutcomeImage

/-!
# Proposed medic-repaired disposition

Candidate policy only.  A qualified append-only disposition excludes one exact
latest injury occurrence from the effective active set.  Historical
misclassification and genuine external repair are distinct evidence kinds.
Neither asserts task success or creates learning credit.  Authority and pin
authenticity are supplied admission predicates, not payload self-attestation.

## The successful-close replay value (R23, ledger entry 45; 2026-10-26)

Source: `~/notes/wm-next/outer-selection/packets/R23-medic-replay-successful-close-packet.md`
(claude-9).  Ledger entry 45 (`injury/9c6220388033cbd1…`, ordinal 45,
`:injury-predecessor nil`, cause record
`tick-run-record-2026-10-26-8be8ff03…`, pin `e9a5eb35…`) was opened at click
1's terminal by the classifier's default branch on a `:grounded-progress`
close with no failure (`CloseOutcomeImage.click1_code_injury_law_nonInjury`).
The ordinary ledger transitions cannot retire an `:open` entry that was never
injured, so the medic path is the only honest one.  Until this revision
`ReplayResult` had one non-injury replay, `producerQualifiedNonInjury`, which
is a *failure* rescued by its producer (a9: `:already-satisfied` at
`:author-wait`).  Replaying the repaired classifier on click 1's record gives
`:non-injury-reason :successful-task-outcome`, not a producer-qualified
failure, so naming `producerQualifiedNonInjury` in entry 45's correction would
be a false statement in the ledger.

`successfulCloseNonInjury` is that fifth value: the repaired classifier replays
the record as a successful close.  `misclassificationQualified` admits either
non-injury replay; the other three values still refuse.  `replayFromClose`
connects the two modules: the replay value a record's close alone supplies is
`successfulCloseNonInjury` exactly when `CloseOutcomeImage.closeVerdict` says
`nonInjury` (`successfulClose_replay_iff_law_nonInjury`), it is never
`producerQualifiedNonInjury` (that value is about a failure kind, which the
close cannot see), and for click 1 it is the successful-close value
(`click1_replay_is_successfulClose`).  `entry45Payload.replay` is that value
by construction (`entry45_replay_from_click1_close`), so the medic cannot name
a successful-close replay for a record the law calls an injury.

This adds a constructor to a medic-model type.  Nothing Joe ruled names
`ReplayResult`'s four values (the module is codex/claude authored, 2026-10-24),
so this is read as an extension with a case, not a specification change.

**Clojure correspondence (conformance in a separate packet, not here).**
`futon2/src/futon2/aif/medic_disposition.clj` `replay-results` gains
`:successful-close-non-injury`, and `local-binding?` accepts it beside
`:producer-qualified-non-injury`; `meta_medic_authority.clj`
`required-findings` and the evaluation recipe's `check.clj` need the same
keyword.  Entry 45's numerals below are a transcription key, not identities.
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

/-- The replay of the repaired classifier on the original record.
`producerQualifiedNonInjury`: a failure of a kind its producer qualifies as a
non-injury (a9).  `successfulCloseNonInjury`: a successful close with no
failure, `:non-injury-reason :successful-task-outcome` (entry 45). -/
inductive ReplayResult where
  | producerQualifiedNonInjury
  | unsupportedAuthorRefusal
  | doneAtBaseRevision
  | injury
  | successfulCloseNonInjury
  deriving DecidableEq, Repr

/-- The two replay values that say the original record was not an injury. -/
def ReplayResult.nonInjury (r : ReplayResult) : Prop :=
  r = .producerQualifiedNonInjury ∨ r = .successfulCloseNonInjury

instance : DecidablePred ReplayResult.nonInjury := fun _ => inferInstanceAs (Decidable (_ ∨ _))

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
  decide payload.replay.nonInjury &&
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

/-! ## The successful-close replay value (R23) -/

/-- Only the two non-injury replays qualify; the other three refuse whatever
the binding and the admission say. -/
theorem qualified_replay_nonInjury (admit : MisclassificationAdmission)
    (current : InjuryEntry) (payload : MisclassificationPayload)
    (evidence : MisclassificationEvidence)
    (h : misclassificationQualified admit current payload evidence = true) :
    payload.replay.nonInjury := by
  simp only [misclassificationQualified, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem replay_nonInjury_iff (r : ReplayResult) :
    r.nonInjury ↔ r = .producerQualifiedNonInjury ∨ r = .successfulCloseNonInjury :=
  Iff.rfl

/-- Control: a9's payload with the new value is admitted only when its binding
holds.  Against the retained a9 evidence (replay `producerQualifiedNonInjury`)
the exact binding fails and the process refuses, even under an admission that
names the new payload; against evidence carrying the same value it appends. -/
def a9ClosePayload : MisclassificationPayload :=
  { a9Payload with replay := .successfulCloseNonInjury }
def a9CloseEvidence : MisclassificationEvidence :=
  { a9Evidence with replay := .successfulCloseNonInjury }
def admitA9Close : MisclassificationAdmission := fun current payload evidence =>
  decide (current = a9Entry ∧ payload = a9ClosePayload ∧ evidence = a9CloseEvidence)

theorem a9_new_value_qualifies_only_under_binding :
    let state : MedicState := ⟨[a9Entry, otherEntry], []⟩
    (medicProcess admitA9Close noGenuine (some a9Proof) state
      (.historicalMisclassification a9ClosePayload)).outcome = .refused ∧
    (medicProcess admitA9 noGenuine
      (some (.historicalMisclassification a9CloseEvidence)) state
      (.historicalMisclassification a9ClosePayload)).outcome = .refused ∧
    (medicProcess admitA9Close noGenuine
      (some (.historicalMisclassification a9CloseEvidence)) state
      (.historicalMisclassification a9ClosePayload)).outcome = .appended := by decide

/-- Control: a payload whose replay is `injury` still refuses, with a matching
binding and a permissive admission. -/
theorem injury_replay_refuses :
    let injured := { a9Payload with replay := .injury }
    let injuredEvidence := { a9Evidence with replay := .injury }
    let permissive : MisclassificationAdmission := fun _ _ _ => true
    let state : MedicState := ⟨[a9Entry, otherEntry], []⟩
    (medicProcess permissive noGenuine (some (.historicalMisclassification injuredEvidence))
      state (.historicalMisclassification injured)).outcome = .refused := by decide

/-- Ledger entry 45, transcribed.  Key (numerals are not the identities):
injury `injury/9c6220388033cbd1…` ↦ 9622; entry ordinal 45 ↦ 45;
`:injury-predecessor nil` ↦ 0 (the convention of `MedicLedgerBridge`);
cause record `tick-run-record-2026-10-26-8be8ff03…` ↦ 8603; cause pin
`e9a5eb35…` ↦ 9535; `:attempt 1`, `:state :open`. -/
def entry45 : InjuryEntry := ⟨9622, 45, 0, 8603, 9535, true⟩

/-- The replay value a record's close alone supplies, read off
`CloseOutcomeImage.closeVerdict`: `successfulCloseNonInjury` when the law says
the close is a non-injury; `injury` when it says injury (it never does,
`close_never_opens_injury`); `none` when the close does not decide. -/
def replayFromClose (c : CloseOutcomeImage.CloseOutcome) (failurePresent : Bool) :
    Option ReplayResult :=
  match CloseOutcomeImage.closeVerdict (CloseOutcomeImage.image c) failurePresent with
  | some .nonInjury => some .successfulCloseNonInjury
  | some .injury => some .injury
  | none => none

/-- The medic cannot name a successful-close replay for a record the law
calls an injury: the close supplies `successfulCloseNonInjury` exactly when
`closeVerdict` is `nonInjury`. -/
theorem successfulClose_replay_iff_law_nonInjury (c : CloseOutcomeImage.CloseOutcome)
    (b : Bool) :
    replayFromClose c b = some .successfulCloseNonInjury ↔
      CloseOutcomeImage.closeVerdict (CloseOutcomeImage.image c) b =
        some .nonInjury := by
  unfold replayFromClose
  cases CloseOutcomeImage.closeVerdict (CloseOutcomeImage.image c) b with
  | none => simp
  | some v => cases v <;> simp

/-- The close never supplies the producer-qualified value: that value is
about a failure kind, which the close cannot see.  The two non-injury replays
are distinct evidence kinds. -/
theorem close_never_producerQualified (c : CloseOutcomeImage.CloseOutcome) (b : Bool) :
    replayFromClose c b ≠ some .producerQualifiedNonInjury := by
  unfold replayFromClose
  cases CloseOutcomeImage.closeVerdict (CloseOutcomeImage.image c) b with
  | none => simp
  | some v => cases v <;> simp

/-- The close never supplies `injury` (`CloseOutcomeImage.close_never_opens_injury`). -/
theorem close_never_injury_replay (c : CloseOutcomeImage.CloseOutcome) (b : Bool) :
    replayFromClose c b ≠ some .injury := by
  unfold replayFromClose
  have h := CloseOutcomeImage.close_never_opens_injury (CloseOutcomeImage.image c) b
  cases hv : CloseOutcomeImage.closeVerdict (CloseOutcomeImage.image c) b with
  | none => simp
  | some v => cases v <;> simp_all

/-- Click 1's record (`:grounded-progress`, `:failure {:absent :no-failure}`)
replays as a successful close. -/
theorem click1_replay_is_successfulClose :
    replayFromClose .groundedProgress false = some .successfulCloseNonInjury :=
  (successfulClose_replay_iff_law_nonInjury _ _).mpr CloseOutcomeImage.click1_law_nonInjury

/-- Entry 45's correction.  Replay is taken from click 1's close, not chosen:
`entry45_replay_from_click1_close`.  Other numerals: classifier revision,
patch, reviewer, evaluator, evidence pin are placeholders for the correction
envelope that does not exist yet. -/
def entry45Payload : MisclassificationPayload :=
  ⟨entry45.occurrence, 0, 8603, 9535, 2310, .successfulCloseNonInjury, 2301, 9, 10, 4501⟩
def entry45Evidence : MisclassificationEvidence :=
  ⟨entry45.occurrence, 0, 8603, 9535, 2310, .successfulCloseNonInjury, 2301, 9, 10, 4501⟩
def admitEntry45 : MisclassificationAdmission := fun current payload evidence =>
  decide (current = entry45 ∧ payload = entry45Payload ∧ evidence = entry45Evidence)

/-- The premise of the new constructor's use: entry 45's replay value is the
one click 1's close supplies. -/
theorem entry45_replay_from_click1_close :
    some entry45Payload.replay = replayFromClose .groundedProgress false := rfl

/-- Entry 45's correction qualifies under the exact binding and removes
exactly that occurrence from the effective active set; the same payload with
the a9 value refuses under entry 45's admission (the binding names the
successful-close value), and a bare `.injury` replay refuses. -/
theorem entry45_correction_qualifies_with_successful_close_replay :
    let state : MedicState := ⟨[entry45, otherEntry], []⟩
    let result := medicProcess admitEntry45 noGenuine
      (some (.historicalMisclassification entry45Evidence)) state
      (.historicalMisclassification entry45Payload)
    result.outcome = .appended ∧ result.state.history = [entry45, otherEntry] ∧
      medicEffectiveActive result.state = [41] ∧
    (medicProcess admitEntry45 noGenuine
      (some (.historicalMisclassification entry45Evidence)) state
      (.historicalMisclassification
        { entry45Payload with replay := .producerQualifiedNonInjury })).outcome = .refused := by
  decide

/-- A reopening of entry 45's injury after the correction is active again:
the correction covers one exact occurrence. -/
theorem entry45_later_reopening_remains_active :
    let corrected := (medicProcess admitEntry45 noGenuine
      (some (.historicalMisclassification entry45Evidence))
      ⟨[entry45, otherEntry], []⟩ (.historicalMisclassification entry45Payload)).state
    let reopened := { entry45 with entry := 46, predecessor := 45 }
    medicEffectiveActive { corrected with history := corrected.history ++ [reopened] } =
      [41, 9622] := by decide

#print axioms qualified_replay_nonInjury
#print axioms a9_new_value_qualifies_only_under_binding
#print axioms injury_replay_refuses
#print axioms successfulClose_replay_iff_law_nonInjury
#print axioms close_never_producerQualified
#print axioms close_never_injury_replay
#print axioms click1_replay_is_successfulClose
#print axioms entry45_replay_from_click1_close
#print axioms entry45_correction_qualifies_with_successful_close_replay
#print axioms entry45_later_reopening_remains_active

/-- The proposal does not modify the established retry closing law. -/
theorem medic_preserves_success_only_retry_law (b : Bool)
    (o : SelfHealRoute.RetryClickOutcome) :
    o.closing b = SelfHealRoute.ClosingStatus.discharged ↔
      o = SelfHealRoute.RetryClickOutcome.successfulTaskOutcome :=
  SelfHealRoute.closing_dischargesOnlyOnSuccess b o

end DarkTower.WarMachine.HistoricalMisclassificationCorrection
