import DarkTower.WarMachine.SelfHealRoute

/-!
# Proposed historical misclassification correction

This is a candidate policy refinement for the single shape exemplified by the
historical `a9b900a4` false injury.  It is not an adopted runtime transition and
does not model repair of a real defect.  A qualified append-only correction
removes only its named false injury from the *effective* active set.  It does
not rewrite history, assert task success, create a retry, or create learning
credit.

Authority and pin authenticity are supplied predicates.  Thus this model does
not promote fields carried by a payload into proof of runtime authority.
-/

namespace DarkTower.WarMachine.HistoricalMisclassificationCorrection

abbrev InjuryId := Nat
abbrev EntryId := Nat
abbrev RecordId := Nat
abbrev Pin := Nat
abbrev Revision := Nat
abbrev PatchId := Nat
abbrev Principal := Nat

structure InjuryEntry where
  injury : InjuryId
  predecessor : EntryId
  originalRecord : RecordId
  originalPin : Pin
  active : Bool
  deriving DecidableEq, Repr

inductive ReplayResult where
  | producerQualifiedNonInjury
  | unsupportedAuthorRefusal
  | doneAtBaseRevision
  | injury
  deriving DecidableEq, Repr

structure CorrectionPayload where
  injury : InjuryId
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

structure Evidence where
  injury : InjuryId
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

abbrev AuthorityCheck := CorrectionPayload → Evidence → Bool
abbrev PinCheck := CorrectionPayload → Evidence → Bool

def exactBinding (c : CorrectionPayload) (e : Evidence) : Bool :=
  decide (c.injury = e.injury) &&
  decide (c.predecessor = e.predecessor) &&
  decide (c.originalRecord = e.originalRecord) &&
  decide (c.originalPin = e.originalPin) &&
  decide (c.classifierRevision = e.classifierRevision) &&
  decide (c.replay = e.replay) &&
  decide (c.patch = e.patch) &&
  decide (c.reviewer = e.reviewer) &&
  decide (c.evaluator = e.evaluator) &&
  decide (c.evidencePin = e.evidencePin)

def qualified (authority : AuthorityCheck) (pins : PinCheck)
    (current : InjuryEntry) (c : CorrectionPayload) (e : Evidence) : Bool :=
  current.active &&
  decide (current.injury = c.injury) &&
  decide (current.predecessor = c.predecessor) &&
  decide (current.originalRecord = c.originalRecord) &&
  decide (current.originalPin = c.originalPin) &&
  decide (c.replay = .producerQualifiedNonInjury) &&
  decide (c.reviewer ≠ c.evaluator) && exactBinding c e &&
  authority c e && pins c e

structure State where
  history : List InjuryEntry
  corrections : List CorrectionPayload
  deriving DecidableEq, Repr

inductive Outcome where
  | appended
  | duplicate
  | conflict
  | refused
  deriving DecidableEq, Repr

structure ProcessResult where
  outcome : Outcome
  state : State
  deriving DecidableEq, Repr

def process (authority : AuthorityCheck) (pins : PinCheck) (current : InjuryEntry)
    (evidence : Evidence) (state : State) (candidate : CorrectionPayload) : ProcessResult :=
  if ! qualified authority pins current candidate evidence then
    ⟨.refused, state⟩
  else if candidate ∈ state.corrections then
    ⟨.duplicate, state⟩
  else if state.corrections.any (fun old => old.injury = candidate.injury) then
    ⟨.conflict, state⟩
  else
    ⟨.appended, { state with corrections := state.corrections ++ [candidate] }⟩

def correctedIds (state : State) : List InjuryId :=
  state.corrections.map (·.injury)

def effectiveActive (state : State) : List InjuryId :=
  (state.history.filter (·.active)).map (·.injury) |>.filter
    (fun injury => injury ∉ correctedIds state)

theorem process_preserves_history :
    (process authority pins current evidence state candidate).state.history = state.history := by
  unfold process
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem appended_only_if_qualified
    (h : (process authority pins current evidence state candidate).outcome = .appended) :
    qualified authority pins current candidate evidence = true := by
  simp only [process] at h
  split at h <;> simp_all

theorem refused_unchanged
    (h : qualified authority pins current candidate evidence = false) :
    (process authority pins current evidence state candidate).state = state := by
  simp [process, h]

theorem duplicate_inert
    (hq : qualified authority pins current candidate evidence = true)
    (hmem : candidate ∈ state.corrections) :
    process authority pins current evidence state candidate = ⟨.duplicate, state⟩ := by
  simp [process, hq, hmem]

theorem conflicting_payload_refused_unchanged
    (hq : qualified authority pins current candidate evidence = true)
    (hnew : candidate ∉ state.corrections)
    (hold : ∃ old ∈ state.corrections, old.injury = candidate.injury) :
    process authority pins current evidence state candidate = ⟨.conflict, state⟩ := by
  simp only [process, hq, hnew, List.any_eq_true]
  simp_all

theorem appended_removes_exact_named_active
    (hq : qualified authority pins current candidate evidence = true)
    (hfresh : ∀ old ∈ state.corrections, old.injury ≠ candidate.injury) :
    (process authority pins current evidence state candidate).outcome = .appended ∧
    candidate.injury ∉ effectiveActive (process authority pins current evidence state candidate).state := by
  have hnotmem : candidate ∉ state.corrections := by
    intro h
    exact (hfresh candidate h) rfl
  have hany : state.corrections.any (fun old => old.injury = candidate.injury) = false := by
    rw [List.any_eq_false]
    intro old hold
    intro heq
    exact (hfresh old hold) (of_decide_eq_true heq)
  simp [process, hq, hnotmem, hany, effectiveActive, correctedIds]

theorem unrelated_active_preserved
    (hq : qualified authority pins current candidate evidence = true)
    (hfresh : ∀ old ∈ state.corrections, old.injury ≠ candidate.injury)
    (hentry : entry ∈ state.history) (hactive : entry.active = true)
    (hunrelated : entry.injury ≠ candidate.injury)
    (huncorrected : entry.injury ∉ correctedIds state) :
    entry.injury ∈ effectiveActive (process authority pins current evidence state candidate).state := by
  have hnotmem : candidate ∉ state.corrections := by
    intro h
    exact (hfresh candidate h) rfl
  have hany : state.corrections.any (fun old => old.injury = candidate.injury) = false := by
    rw [List.any_eq_false]
    intro old hold
    intro heq
    exact (hfresh old hold) (of_decide_eq_true heq)
  simp only [process, hq, Bool.not_true, ↓reduceIte, hnotmem, hany,
             effectiveActive, correctedIds, List.mem_filter, List.mem_map]
  constructor
  · exact ⟨entry, ⟨hentry, hactive⟩, rfl⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply decide_eq_true
    intro hex
    rcases hex with ⟨correction, hcorrection, heq⟩
    simp only [List.mem_append, List.mem_singleton] at hcorrection
    rcases hcorrection with hcorrection | hcandidate
    · apply huncorrected
      simp only [correctedIds, List.mem_map]
      exact ⟨correction, hcorrection, heq⟩
    · subst correction
      exact hunrelated heq.symm

/-! Synthetic a9-shaped model; these constants are examples, not live certification. -/

def a9Entry : InjuryEntry := ⟨9, 34, 60, 600, true⟩
def a9Correction : CorrectionPayload := ⟨9, 34, 60, 600, 36, .producerQualifiedNonInjury, 361, 11, 12, 700⟩
def a9Evidence : Evidence := ⟨9, 34, 60, 600, 36, .producerQualifiedNonInjury, 361, 11, 12, 700⟩
def otherEntry : InjuryEntry := ⟨41, 18, 70, 701, true⟩
def initial : State := ⟨[a9Entry, otherEntry], []⟩
def suppliedAuthority : AuthorityCheck := fun c e => decide (c = a9Correction ∧ e = a9Evidence)
def suppliedPins : PinCheck := fun c e => decide (c.evidencePin = 700 ∧ e.evidencePin = 700)

theorem a9_composed_correction_removes_only_a9 :
    let result := process suppliedAuthority suppliedPins a9Entry a9Evidence initial a9Correction
    result.outcome = .appended ∧ result.state.history = initial.history ∧
      effectiveActive result.state = [41] := by decide

theorem unsupported_refusal_cannot_remove :
    let bad := { a9Correction with replay := .unsupportedAuthorRefusal }
    (process suppliedAuthority suppliedPins a9Entry a9Evidence initial bad).outcome = .refused ∧
      effectiveActive (process suppliedAuthority suppliedPins a9Entry a9Evidence initial bad).state = [9, 41] := by decide

theorem done_at_base_cannot_remove :
    let bad := { a9Correction with replay := .doneAtBaseRevision }
    (process suppliedAuthority suppliedPins a9Entry a9Evidence initial bad).outcome = .refused ∧
      effectiveActive (process suppliedAuthority suppliedPins a9Entry a9Evidence initial bad).state = [9, 41] := by decide

theorem stale_predecessor_cannot_remove :
    let bad := { a9Correction with predecessor := 33 }
    (process suppliedAuthority suppliedPins a9Entry a9Evidence initial bad).outcome = .refused := by decide

theorem wrong_record_cannot_remove :
    let bad := { a9Correction with originalRecord := 61 }
    (process suppliedAuthority suppliedPins a9Entry a9Evidence initial bad).outcome = .refused := by decide

theorem replay_duplicate_is_inert :
    let once := (process suppliedAuthority suppliedPins a9Entry a9Evidence initial a9Correction).state
    process suppliedAuthority suppliedPins a9Entry a9Evidence once a9Correction = ⟨.duplicate, once⟩ := by decide

def conflictingCorrection := { a9Correction with patch := 362 }
def conflictingEvidence := { a9Evidence with patch := 362 }
def conflictAuthority : AuthorityCheck := fun c e => decide (c = conflictingCorrection ∧ e = conflictingEvidence)

theorem conflicting_replay_is_inert :
    let once := (process suppliedAuthority suppliedPins a9Entry a9Evidence initial a9Correction).state
    process conflictAuthority suppliedPins a9Entry conflictingEvidence once conflictingCorrection =
      ⟨.conflict, once⟩ := by decide

/-- The candidate overlay does not modify the established retry closing law. -/
theorem existing_retry_discharge_unchanged (b : Bool)
    (o : SelfHealRoute.RetryClickOutcome) :
    o.closing b = SelfHealRoute.ClosingStatus.discharged ↔
      o = SelfHealRoute.RetryClickOutcome.successfulTaskOutcome :=
  SelfHealRoute.closing_dischargesOnlyOnSuccess b o

/-!
## Proposed broader medic-repaired disposition

Joe's subsequent direction broadens the proposed disposition to genuine
externally repaired defects as well as proven historical misclassification.
The constructors remain distinct.  In particular, a genuine repair must carry
an independently admitted replay of its *original acceptance contract*; the
misclassification constructor cannot be used for it.
-/

structure GenuineRepairPayload where
  injury : InjuryId
  predecessor : EntryId
  causeRecord : RecordId
  causePin : Pin
  acceptanceContract : Pin
  patch : PatchId
  sourceRevision : Revision
  evaluator : Principal
  reviewer : Principal
  replayReceipt : Pin
  originalAcceptanceRepaired : Bool
  deriving DecidableEq, Repr

structure GenuineRepairEvidence where
  injury : InjuryId
  predecessor : EntryId
  causeRecord : RecordId
  causePin : Pin
  acceptanceContract : Pin
  patch : PatchId
  sourceRevision : Revision
  evaluator : Principal
  reviewer : Principal
  replayReceipt : Pin
  originalAcceptanceRepaired : Bool
  deriving DecidableEq, Repr

inductive MedicCorrection where
  | historicalMisclassification (payload : CorrectionPayload)
  | genuineDefect (payload : GenuineRepairPayload)
  deriving DecidableEq, Repr

inductive MedicEvidence where
  | historicalMisclassification (evidence : Evidence)
  | genuineDefect (evidence : GenuineRepairEvidence)
  deriving DecidableEq, Repr

def MedicCorrection.injury : MedicCorrection → InjuryId
  | .historicalMisclassification payload => payload.injury
  | .genuineDefect payload => payload.injury

abbrev MisclassificationAdmission := InjuryEntry → CorrectionPayload → Evidence → Bool
abbrev GenuineRepairAdmission := InjuryEntry → GenuineRepairPayload → GenuineRepairEvidence → Bool

def exactGenuineBinding (payload : GenuineRepairPayload)
    (evidence : GenuineRepairEvidence) : Bool :=
  decide (payload.injury = evidence.injury) &&
  decide (payload.predecessor = evidence.predecessor) &&
  decide (payload.causeRecord = evidence.causeRecord) &&
  decide (payload.causePin = evidence.causePin) &&
  decide (payload.acceptanceContract = evidence.acceptanceContract) &&
  decide (payload.patch = evidence.patch) &&
  decide (payload.sourceRevision = evidence.sourceRevision) &&
  decide (payload.evaluator = evidence.evaluator) &&
  decide (payload.reviewer = evidence.reviewer) &&
  decide (payload.replayReceipt = evidence.replayReceipt) &&
  decide (payload.originalAcceptanceRepaired = evidence.originalAcceptanceRepaired)

def genuineQualified (admit : GenuineRepairAdmission) (current : InjuryEntry)
    (payload : GenuineRepairPayload) (evidence : GenuineRepairEvidence) : Bool :=
  current.active &&
  decide (current.injury = payload.injury) &&
  decide (current.predecessor = payload.predecessor) &&
  payload.originalAcceptanceRepaired &&
  decide (payload.evaluator ≠ payload.reviewer) &&
  exactGenuineBinding payload evidence && admit current payload evidence

def medicQualified (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (current : InjuryEntry)
    (candidate : MedicCorrection) (evidence : MedicEvidence) : Bool :=
  match candidate, evidence with
  | .historicalMisclassification payload, .historicalMisclassification proof =>
      misclassification current payload proof
  | .genuineDefect payload, .genuineDefect proof =>
      genuineQualified genuine current payload proof
  | _, _ => false

structure MedicState where
  history : List InjuryEntry
  corrections : List MedicCorrection
  deriving DecidableEq, Repr

structure MedicResult where
  outcome : Outcome
  state : MedicState
  deriving DecidableEq, Repr

def medicProcess (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (current : InjuryEntry)
    (evidence : MedicEvidence) (state : MedicState)
    (candidate : MedicCorrection) : MedicResult :=
  if ! medicQualified misclassification genuine current candidate evidence then
    ⟨.refused, state⟩
  else if candidate ∈ state.corrections then
    ⟨.duplicate, state⟩
  else if state.corrections.any (fun old => old.injury = candidate.injury) then
    ⟨.conflict, state⟩
  else
    ⟨.appended, { state with corrections := state.corrections ++ [candidate] }⟩

def medicEffectiveActive (state : MedicState) : List InjuryId :=
  (state.history.filter (·.active)).map (·.injury) |>.filter
    (fun injury => injury ∉ state.corrections.map MedicCorrection.injury)

structure MedicRequest where
  current : InjuryEntry
  candidate : MedicCorrection
  evidence : MedicEvidence

def medicSweep (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) : MedicState → List MedicRequest → MedicState
  | state, [] => state
  | state, request :: rest =>
      medicSweep misclassification genuine
        (medicProcess misclassification genuine request.current request.evidence
          state request.candidate).state rest

theorem medicProcess_preserves_history :
    (medicProcess misclassification genuine current evidence state candidate).state.history =
      state.history := by
  unfold medicProcess
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem medic_appended_only_if_qualified
    (h : (medicProcess misclassification genuine current evidence state candidate).outcome =
      .appended) :
    medicQualified misclassification genuine current candidate evidence = true := by
  simp only [medicProcess] at h
  split at h <;> simp_all

theorem medic_duplicate_inert
    (hq : medicQualified misclassification genuine current candidate evidence = true)
    (hmem : candidate ∈ state.corrections) :
    medicProcess misclassification genuine current evidence state candidate =
      ⟨.duplicate, state⟩ := by
  simp [medicProcess, hq, hmem]

theorem medic_conflict_inert
    (hq : medicQualified misclassification genuine current candidate evidence = true)
    (hnew : candidate ∉ state.corrections)
    (hold : ∃ old ∈ state.corrections, old.injury = candidate.injury) :
    medicProcess misclassification genuine current evidence state candidate =
      ⟨.conflict, state⟩ := by
  simp only [medicProcess, hq, hnew, List.any_eq_true]
  simp_all

theorem medic_no_qualified_evidence_no_change
    (hq : medicQualified misclassification genuine current candidate evidence = false) :
    medicProcess misclassification genuine current evidence state candidate =
      ⟨.refused, state⟩ := by
  simp [medicProcess, hq]

theorem all_active_qualified_corrections_clear_effective_set
    (covered : ∀ entry ∈ state.history, entry.active = true →
      entry.injury ∈ state.corrections.map MedicCorrection.injury) :
    medicEffectiveActive state = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro injury hinjury
  simp only [medicEffectiveActive, List.mem_filter, List.mem_map] at hinjury
  rcases hinjury with ⟨⟨entry, ⟨hentry, hactive⟩, rfl⟩, hnotcorrected⟩
  have hcovered := covered entry hentry hactive
  rw [List.mem_map] at hcovered
  obtain ⟨correction, hcorrection, heq⟩ := hcovered
  exact (of_decide_eq_true hnotcorrected) ⟨correction, hcorrection, heq⟩

def realEntry : InjuryEntry := ⟨84, 37, 25, 846, true⟩
def realRepair : GenuineRepairPayload := ⟨84, 37, 25, 846, 900, 560, 561, 21, 22, 910, true⟩
def realEvidence : GenuineRepairEvidence := ⟨84, 37, 25, 846, 900, 560, 561, 21, 22, 910, true⟩

def admitA9 : MisclassificationAdmission := fun current payload evidence =>
  decide (current = a9Entry ∧ payload = a9Correction ∧ evidence = a9Evidence)

def admitReal : GenuineRepairAdmission := fun current payload evidence =>
  decide (current = realEntry ∧ payload = realRepair ∧ evidence = realEvidence)

def mixedInitial : MedicState := ⟨[a9Entry, realEntry, otherEntry], []⟩
def a9MedicRequest : MedicRequest :=
  ⟨a9Entry, .historicalMisclassification a9Correction,
    .historicalMisclassification a9Evidence⟩
def realMedicRequest : MedicRequest :=
  ⟨realEntry, .genuineDefect realRepair, .genuineDefect realEvidence⟩

theorem composed_medic_sweep_clears_only_qualified :
    medicEffectiveActive (medicSweep admitA9 admitReal mixedInitial
      [a9MedicRequest, realMedicRequest]) = [41] := by decide

theorem unresolved_injury_prevents_clear_all :
    medicEffectiveActive (medicSweep admitA9 admitReal mixedInitial
      [a9MedicRequest]) = [84, 41] := by decide

theorem unrelated_green_test_cannot_qualify_genuine_repair :
    let bad := { realRepair with originalAcceptanceRepaired := false }
    (medicProcess admitA9 admitReal realEntry (.genuineDefect realEvidence)
      mixedInitial (.genuineDefect bad)).outcome = .refused := by decide

theorem evidence_constructor_mismatch_refuses :
    (medicProcess admitA9 admitReal realEntry (.historicalMisclassification a9Evidence)
      mixedInitial (.genuineDefect realRepair)).outcome = .refused := by decide

/-- Medic repair is an effective-active overlay, not a new retry outcome. -/
theorem medic_preserves_success_only_retry_law (b : Bool)
    (o : SelfHealRoute.RetryClickOutcome) :
    o.closing b = SelfHealRoute.ClosingStatus.discharged ↔
      o = SelfHealRoute.RetryClickOutcome.successfulTaskOutcome :=
  SelfHealRoute.closing_dischargesOnlyOnSuccess b o

end DarkTower.WarMachine.HistoricalMisclassificationCorrection
