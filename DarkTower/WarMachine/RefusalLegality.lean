import DarkTower.WarMachine.R20Step

/-!
# Refusal legality: legal stops, not a Dark Room

Formal half of `futon2/holes/excursions/E-wm-construct-validity.md`
(Joe, 2026-11-05).  A War Machine click that does no work ends in one of three
dispositions:

* a **loop stop** (the machine does nothing further), legal only when the
  scored admissible field is empty (work exhausted, `R20FocusedSelection`
  `OuterSelectionConforms` over an empty field) or the operator overrides;
* a **click-legal terminal** (this click ends and the next click selects new
  work): already satisfied, a legitimate question left in the operator brief,
  or a harmful action declined.  Each must exclude its target from the next
  admissible field until new evidence arrives;
* a **debugger error**: anything else.  It is held and repaired, never a stop.

The booleans denote checks performed by the runtime refusal validator.  This
module does not attest that the validator exists or that an event occurred;
like `FileChangeHygieneDelivery`, it makes an admitted refusal imply that every
check succeeded, and it proves that legal terminals cannot form a Dark Room
cycle: with unchanged evidence, each removes its target, so at most
`field.length` of them can occur before the field is empty.
-/

namespace DarkTower.WarMachine.RefusalLegality
open R20Step

/-! ## Loop stops -/

inductive LoopStop where
  | workExhausted | operatorOverride
  deriving DecidableEq, Repr

structure LoopStopEvidence where
  kind : LoopStop
  /-- The scored admissible field after exclusions, as retained by the click. -/
  scoredField : List Candidate
  /-- The operator's stop control or cancel was observed. -/
  operatorSignal : Bool

def loopStopLegal (e : LoopStopEvidence) : Bool :=
  match e.kind with
  | .workExhausted => e.scoredField.isEmpty
  | .operatorOverride => e.operatorSignal

theorem workExhausted_legal_iff (field : List Candidate) (sig : Bool) :
    loopStopLegal ⟨.workExhausted, field, sig⟩ = true ↔ field = [] := by
  simp [loopStopLegal]

/-- "Nothing to do" with work still in the field is not a legal stop. -/
theorem nonempty_field_not_exhausted (c : Candidate) (rest : List Candidate) (sig : Bool) :
    loopStopLegal ⟨.workExhausted, c :: rest, sig⟩ = false := by
  simp [loopStopLegal]

theorem override_legal_iff (field : List Candidate) (sig : Bool) :
    loopStopLegal ⟨.operatorOverride, field, sig⟩ = true ↔ sig = true := by
  simp [loopStopLegal]

/-! ## Click-legal terminals -/

inductive ClickTerminal where
  | alreadySatisfied | legitimateQuestion | harmDeclined
  deriving DecidableEq, Repr

structure ClickEvidence where
  kind : ClickTerminal
  target : Target
  /-- C1: the selected want was measured as already satisfied. -/
  satisfactionMeasured : Bool
  /-- C2: the question cites a specific ambiguity in the mission text. -/
  ambiguityCited : Bool
  /-- C2: the question was written to the operator brief. -/
  questionInBrief : Bool
  /-- C3: the declined action matched a named harm rule. -/
  harmRuleMatched : Bool
  /-- The target's exclusion, keyed to the evidence digest, was recorded. -/
  exclusionRecorded : Bool
  deriving DecidableEq, Repr

def caseChecked (e : ClickEvidence) : Bool :=
  match e.kind with
  | .alreadySatisfied => e.satisfactionMeasured
  | .legitimateQuestion => e.ambiguityCited && e.questionInBrief
  | .harmDeclined => e.harmRuleMatched

def clickLegal (e : ClickEvidence) : Bool :=
  caseChecked e && e.exclusionRecorded

theorem clickLegal_iff (e : ClickEvidence) :
    clickLegal e = true ↔ caseChecked e = true ∧ e.exclusionRecorded = true := by
  simp [clickLegal]

/-- A terminal that leaves its target selectable is never legal: that is the
Dark Room move (stop, and be offered the same stop again). -/
theorem unexcluded_not_legal (e : ClickEvidence) (h : e.exclusionRecorded = false) :
    clickLegal e = false := by
  simp [clickLegal, h]

theorem question_needs_brief (e : ClickEvidence) (hk : e.kind = .legitimateQuestion)
    (h : e.questionInBrief = false) : clickLegal e = false := by
  simp [clickLegal, caseChecked, hk, h]

theorem question_needs_cited_ambiguity (e : ClickEvidence)
    (hk : e.kind = .legitimateQuestion) (h : e.ambiguityCited = false) :
    clickLegal e = false := by
  simp [clickLegal, caseChecked, hk, h]

/-! ## Disposition -/

inductive Disposition where
  | loopStop | clickTerminal | debuggerError
  deriving DecidableEq, Repr

/-- A refusal the click reports: a loop stop, a click terminal, or neither. -/
inductive Refusal where
  | stop (e : LoopStopEvidence)
  | terminal (e : ClickEvidence)
  | other

def disposition : Refusal → Disposition
  | .stop e => if loopStopLegal e then .loopStop else .debuggerError
  | .terminal e => if clickLegal e then .clickTerminal else .debuggerError
  | .other => .debuggerError

theorem disposition_loopStop_iff (r : Refusal) :
    disposition r = .loopStop ↔ ∃ e, r = .stop e ∧ loopStopLegal e = true := by
  cases r with
  | stop e => by_cases h : loopStopLegal e <;> simp [disposition, h]
  | terminal e => by_cases h : clickLegal e <;> simp [disposition, h]
  | other => simp [disposition]

theorem disposition_clickTerminal_iff (r : Refusal) :
    disposition r = .clickTerminal ↔ ∃ e, r = .terminal e ∧ clickLegal e = true := by
  cases r with
  | stop e => by_cases h : loopStopLegal e <;> simp [disposition, h]
  | terminal e => by_cases h : clickLegal e <;> simp [disposition, h]
  | other => simp [disposition]

/-- Every refusal outside the five legal cases is a debugger error. -/
theorem unlisted_is_debuggerError : disposition .other = .debuggerError := rfl

/-! ## No Dark Room cycle -/

/-- The next click's field after a terminal: a legal terminal on unchanged
evidence removes its target (cf. `ReadingRefusalReselection.reducedField`,
which does this within one click; here the exclusion persists across clicks
until the evidence digest changes). -/
def nextField (field : List Candidate) (e : ClickEvidence)
    (previousDigest currentDigest : String) : List Candidate :=
  if clickLegal e && previousDigest == currentDigest then
    field.filter (fun c => c.target != e.target)
  else field

theorem legal_terminal_excludes (field : List Candidate) (e : ClickEvidence)
    (digest : String) (h : clickLegal e = true) {c : Candidate}
    (hc : c ∈ nextField field e digest digest) : c ∈ field ∧ c.target ≠ e.target := by
  simp [nextField, h] at hc
  exact ⟨hc.1, hc.2⟩

theorem new_evidence_restores (field : List Candidate) (e : ClickEvidence)
    (old current : String) (h : old ≠ current) :
    nextField field e old current = field := by
  simp [nextField, h]

/-- A legal terminal on a target that was in the field strictly shrinks it. -/
theorem legal_terminal_shrinks (field : List Candidate) (e : ClickEvidence)
    (digest : String) (h : clickLegal e = true) {c : Candidate}
    (hc : c ∈ field) (ht : c.target = e.target) :
    (nextField field e digest digest).length < field.length := by
  simp only [nextField, h, beq_self_eq_true, Bool.and_self, if_true]
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨c, hc, by simp [ht]⟩

/-- A run of legal terminals on unchanged evidence, each on a target selected
from the field it was offered. -/
def runTerminals (digest : String) : List Candidate → List ClickEvidence → List Candidate
  | field, [] => field
  | field, e :: es => runTerminals digest (nextField field e digest digest) es

/-- Each step selected its target from the field it was offered and was legal. -/
def SelectedLegally (digest : String) : List Candidate → List ClickEvidence → Prop
  | _, [] => True
  | field, e :: es =>
      clickLegal e = true ∧ (∃ c ∈ field, c.target = e.target) ∧
        SelectedLegally digest (nextField field e digest digest) es

/-- **No Dark Room.** On unchanged evidence, `k` legal terminals each selected
from the field leave at most `field.length - k` candidates.  So at most
`field.length` of them can happen before the field is empty, and the only legal
stop left is `workExhausted`. -/
theorem legal_terminals_bounded (digest : String) :
    ∀ (es : List ClickEvidence) (field : List Candidate),
      SelectedLegally digest field es →
        (runTerminals digest field es).length + es.length ≤ field.length
  | [], field, _ => by simp [runTerminals]
  | e :: es, field, ⟨hl, ⟨c, hc, ht⟩, hrest⟩ => by
      have ih := legal_terminals_bounded digest es _ hrest
      have hs := legal_terminal_shrinks field e digest hl hc ht
      simp only [runTerminals, List.length_cons]
      omega

theorem legal_terminal_count_le_field (digest : String) (es : List ClickEvidence)
    (field : List Candidate) (h : SelectedLegally digest field es) :
    es.length ≤ field.length := by
  have := legal_terminals_bounded digest es field h
  omega

end DarkTower.WarMachine.RefusalLegality
