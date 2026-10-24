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

end DarkTower.WarMachine.HistoricalMisclassificationCorrection
