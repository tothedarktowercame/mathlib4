import DarkTower.WarMachine.OrdinaryClickRoute
import Lean.Elab.Tactic.Omega

/-!
# Guarded author-response correction at ordinary row 24

This is a local orchestration refinement for the author-result boundary before
the fresh-artifact/build path.  It models one narrow case: a completed,
provenance-verified `DONE` whose claimed artifact is exactly the immutable base
of that same request.  That reply remains refused; the detour merely permits
one later response to be evaluated by the unchanged abstract author gate.

The binding fields mirror the runtime request/result boundary in
`futon2/aif/full_loop_runner.clj`: target, author, repository, observed base,
and acceptance-contract identity.  `requestId` and `resultId` retain the
actual original request/result identities.  A runtime adapter must supply the
provenance, card, existing-artifact, and fresh-binding facts.  This file proves
no transport authentication, LLM reply, execution success, liveness, learning,
or Clojure conformance.

The modeled correction request is a new bounded prompt about the retained
original; it is not a claim that the original dispatch is replayed or that its
result changes.
-/

namespace DarkTower.WarMachine.AuthorResponseCorrectionRoute

abbrev OrdinaryBudget := OrdinaryClickRoute.Budget

structure Binding where
  target : String
  author : String
  repository : String
  baseRevision : String
  contractDigest : String
  deriving DecidableEq, Repr

inductive ReplyForm where
  | done
  | refuseAlreadySatisfied
  | absent
  deriving DecidableEq, Repr

/-- Immutable result observed for the original request. -/
structure OriginalResult where
  requestId : String
  resultId : String
  binding : Binding
  completed : Bool
  cancelled : Bool
  mechanicalFalsifier : Bool
  provenanceVerified : Bool
  form : ReplyForm
  claimedArtifact : String
  deriving DecidableEq, Repr

/-- Immutable identity allocated for one bounded correction request. -/
structure CorrectionRequest where
  correctionId : String
  originalRequestId : String
  originalResultId : String
  binding : Binding
  deriving DecidableEq, Repr

def CorrectionRequest.matchesOriginal (c : CorrectionRequest) (o : OriginalResult) : Bool :=
  c.originalRequestId == o.requestId &&
  c.originalResultId == o.resultId &&
  c.binding == o.binding

/-- A later response must name the correction request as well as the retained
original request/result. Completion and return provenance are supplied facts
from a future adapter, not self-authentication claims. -/
structure CorrectedReply where
  correctionId : String
  requestId : String
  originalResultId : String
  binding : Binding
  cancelled : Bool
  completed : Bool
  returnProvenanceVerified : Bool
  form : ReplyForm
  artifact : String
  validAlreadySatisfiedCard : Bool
  existingArtifactVerified : Bool
  freshArtifactBindingVerified : Bool
  deriving DecidableEq, Repr

/-- The only entry condition.  This is deliberately not a generic
`:artifact-binding-mismatch`: it is an explicit completed `DONE` at this
request's own base, with verified provenance and no cancellation/falsifier. -/
def OriginalResult.correctableDoneAtBase (o : OriginalResult) : Prop :=
  o.completed = true ∧
  o.cancelled = false ∧
  o.mechanicalFalsifier = false ∧
  o.provenanceVerified = true ∧
  o.form = .done ∧
  o.claimedArtifact = o.binding.baseRevision

def CorrectedReply.matches (r : CorrectedReply) (o : OriginalResult) : Bool :=
  r.requestId == o.requestId &&
  r.originalResultId == o.resultId &&
  r.binding == o.binding &&
  r.cancelled == false

def CorrectedReply.qualifiedFor (r : CorrectedReply)
    (o : OriginalResult) (c : CorrectionRequest) : Bool :=
  c.matchesOriginal o &&
  r.correctionId == c.correctionId &&
  r.matches o &&
  r.completed == true &&
  r.returnProvenanceVerified == true

inductive GateResult where
  | alreadySatisfied
  | freshDone
  | refused
  deriving DecidableEq, Repr

/-- Abstracts the existing, unchanged runtime gate.  A valid refusal needs a
valid card and an independently verified existing artifact.  A `DONE` needs a
fresh binding and cannot name the base.  Nothing here calls either result a
successful repair or a learning event. -/
def authorGate (o : OriginalResult) (r : CorrectedReply) : GateResult :=
  if r.matches o = false then .refused
  else match r.form with
    | .refuseAlreadySatisfied =>
        if r.validAlreadySatisfiedCard = true ∧ r.existingArtifactVerified = true
        then .alreadySatisfied else .refused
    | .done =>
        if r.freshArtifactBindingVerified = true ∧ r.artifact ≠ o.binding.baseRevision
        then .freshDone else .refused
    | .absent => .refused

inductive Refusal where
  | invalidOrChangedReply
  deriving DecidableEq, Repr

/-- The original result and correction request are present in every detour
state. A reply appears only after its own immutable correction wait. -/
inductive Node where
  | gate (original : OriginalResult) (ordinaryBudget : OrdinaryBudget) (allowance : Nat)
  | correctionPrompt (original : OriginalResult) (request : CorrectionRequest)
      (ordinaryBudget : OrdinaryBudget) (allowance : Nat)
  | correctionWait (original : OriginalResult) (request : CorrectionRequest)
      (ordinaryBudget : OrdinaryBudget) (allowance : Nat)
  | response (original : OriginalResult) (request : CorrectionRequest) (reply : CorrectedReply)
      (ordinaryBudget : OrdinaryBudget) (allowance : Nat)
  | validated (original : OriginalResult) (request : CorrectionRequest) (reply : CorrectedReply)
      (qualified : reply.qualifiedFor original request = true)
      (ordinaryBudget : OrdinaryBudget) (allowance : Nat)
  | alreadySatisfied (original : OriginalResult) (request : CorrectionRequest) (reply : CorrectedReply)
      (qualified : reply.qualifiedFor original request = true)
      (ordinaryBudget : OrdinaryBudget)
  | continuedToBuild (original : OriginalResult) (request : CorrectionRequest) (reply : CorrectedReply)
      (qualified : reply.qualifiedFor original request = true)
      (ordinary : OrdinaryClickRoute.Node)
  | refused (original : OriginalResult) (request : CorrectionRequest) (reply : CorrectedReply)
      (reason : Refusal) (ordinaryBudget : OrdinaryBudget)
  deriving Repr

/-- The allowance is consumed on entry; the reply is retained and evaluated
only after wait.  A valid refusal terminates as an explicit no-fresh-artifact
outcome; a valid fresh `DONE` merely resumes the existing row-24 build path. -/
inductive Step : Node → Node → Prop where
  | beginCorrection (h : original.correctableDoneAtBase)
      (hrequest : request.matchesOriginal original = true) :
      Step (.gate original b (n + 1)) (.correctionPrompt original request b n)
  | prompted :
      Step (.correctionPrompt original request b n) (.correctionWait original request b n)
  | replied (reply : CorrectedReply) :
      Step (.correctionWait original request b n) (.response original request reply b n)
  | qualified (h : reply.qualifiedFor original request = true) :
      Step (.response original request reply b n) (.validated original request reply h b n)
  | unqualified (h : reply.qualifiedFor original request = false) :
      Step (.response original request reply b n)
        (.refused original request reply .invalidOrChangedReply b)
  | validRefusal (h : authorGate original reply = .alreadySatisfied) :
      Step (.validated original request reply qualified b n)
        (.alreadySatisfied original request reply qualified b)
  | validFreshDone (h : authorGate original reply = .freshDone) :
      Step (.validated original request reply qualified b n)
        (.continuedToBuild original request reply qualified (.running OrdinaryClickRoute.Phase.p24 b))
  | invalidGateReply (h : authorGate original reply = .refused) :
      Step (.validated original request reply qualified b n)
        (.refused original request reply .invalidOrChangedReply b)

def measure : Node → Nat
  | .gate _ _ n => 4 * n + 1
  | .correctionPrompt _ _ _ n => 4 * n + 4
  | .correctionWait _ _ _ n => 4 * n + 3
  | .response _ _ _ _ n => 4 * n + 2
  | .validated _ _ _ _ _ n => 4 * n + 1
  | .alreadySatisfied _ _ _ _ _ | .continuedToBuild _ _ _ _ _ | .refused _ _ _ _ _ => 0

theorem step_decreases (h : Step s t) : measure t < measure s := by
  cases h
  case beginCorrection => simp [measure]; omega
  case prompted => simp [measure]
  case replied => simp [measure]
  case qualified => simp [measure]
  case unqualified => simp [measure]
  case validRefusal => simp [measure]
  case validFreshDone => simp [measure]
  case invalidGateReply => simp [measure]

theorem step_wellFounded : WellFounded (fun t s => Step s t) :=
  Subrelation.wf (fun h => step_decreases h) (InvImage.wf measure Nat.lt_wfRel.wf)

theorem noInfiniteCorrection (run : Nat → Node)
    (edges : ∀ n, Step (run n) (run (n + 1))) : False := by
  have bound : ∀ n, n + measure (run n) ≤ measure (run 0) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have := step_decreases (edges n)
      omega
  have := bound (measure (run 0) + 1)
  omega

def exampleBinding : Binding where
  target := "M-war-machine-wiring"
  author := "zai-2"
  repository := "/home/joe/code/futon5a"
  baseRevision := "68120423443eab3243c400563cc9c66f45fea6e7"
  contractDigest := "cc5cbb7fe7ecd93ed9af5efb608fd1b87b5bb84a2f2aa4bf89dbe21dc437321f"

/-- Synthetic shape of the retained c52 result, without claiming its omitted
card/reply facts: completed `DONE` at the observed base. -/
def exampleOriginal : OriginalResult where
  requestId := "invoke-1792869943375-3025-243e90fa"
  resultId := "c52d61b9-d268-438c-a204-b944e507a724"
  binding := exampleBinding
  completed := true
  cancelled := false
  mechanicalFalsifier := false
  provenanceVerified := true
  form := .done
  claimedArtifact := exampleBinding.baseRevision

def exampleCorrectionRequest : CorrectionRequest where
  correctionId := "correction-example"
  originalRequestId := exampleOriginal.requestId
  originalResultId := exampleOriginal.resultId
  binding := exampleBinding

/-- Synthetic later refusal; its card/artifact booleans are supplied adapter
facts, not assertions about c52's historical reply. -/
def correctedRefusal : CorrectedReply where
  correctionId := "correction-example"
  requestId := exampleOriginal.requestId
  originalResultId := exampleOriginal.resultId
  binding := exampleBinding
  cancelled := false
  form := .refuseAlreadySatisfied
  artifact := "249ce8a6685edbbb23b019d2661d5dc2c2198e90"
  validAlreadySatisfiedCard := true
  existingArtifactVerified := true
  freshArtifactBindingVerified := false
  completed := true
  returnProvenanceVerified := true

def baseDoneReply : CorrectedReply where
  correctionId := "wrong-base-done"
  requestId := exampleOriginal.requestId
  originalResultId := exampleOriginal.resultId
  binding := exampleBinding
  cancelled := false
  form := .done
  artifact := exampleBinding.baseRevision
  validAlreadySatisfiedCard := false
  existingArtifactVerified := false
  freshArtifactBindingVerified := false
  completed := true
  returnProvenanceVerified := true

def unrelatedCorrectionReply : CorrectedReply :=
  { correctedRefusal with correctionId := "unrelated-correction" }

def incompleteReply : CorrectedReply :=
  { correctedRefusal with completed := false }

def unprovenReply : CorrectedReply :=
  { correctedRefusal with returnProvenanceVerified := false }

def cancelledReply : CorrectedReply :=
  { correctedRefusal with cancelled := true }

theorem exampleOriginal_is_precisely_correctable :
    exampleOriginal.correctableDoneAtBase := by
  simp [OriginalResult.correctableDoneAtBase, exampleOriginal, exampleBinding]

/-- Positive control: the later refusal returns through the author gate, not
directly to build/grounding. -/
theorem corrected_refusal_reaches_only_alreadySatisfied (b : OrdinaryBudget) :
    ∃ n, Step (.gate exampleOriginal b (n + 1))
        (.correctionPrompt exampleOriginal exampleCorrectionRequest b n) ∧
      Step (.correctionPrompt exampleOriginal exampleCorrectionRequest b n)
        (.correctionWait exampleOriginal exampleCorrectionRequest b n) ∧
      Step (.correctionWait exampleOriginal exampleCorrectionRequest b n)
        (.response exampleOriginal exampleCorrectionRequest correctedRefusal b n) ∧
      (∃ hqualified,
        Step (.response exampleOriginal exampleCorrectionRequest correctedRefusal b n)
          (.validated exampleOriginal exampleCorrectionRequest correctedRefusal hqualified b n) ∧
        Step (.validated exampleOriginal exampleCorrectionRequest correctedRefusal hqualified b n)
          (.alreadySatisfied exampleOriginal exampleCorrectionRequest correctedRefusal hqualified b)) := by
  refine ⟨0, .beginCorrection exampleOriginal_is_precisely_correctable (by decide), .prompted,
    .replied correctedRefusal, ?_⟩
  refine ⟨by decide, .qualified (by decide), ?_⟩
  apply Step.validRefusal
  decide

/-- The original `DONE <base>` remains refused even after a correction chance. -/
theorem done_at_base_remains_refused :
    authorGate exampleOriginal baseDoneReply = .refused := by
  simp [authorGate, CorrectedReply.matches, baseDoneReply, exampleOriginal, exampleBinding]

theorem unrelated_example_is_unqualified :
    unrelatedCorrectionReply.qualifiedFor exampleOriginal exampleCorrectionRequest = false := by
  decide

theorem incomplete_example_is_unqualified :
    incompleteReply.qualifiedFor exampleOriginal exampleCorrectionRequest = false := by
  decide

theorem unproven_example_is_unqualified :
    unprovenReply.qualifiedFor exampleOriginal exampleCorrectionRequest = false := by
  decide

theorem cancelled_example_is_unqualified :
    cancelledReply.qualifiedFor exampleOriginal exampleCorrectionRequest = false := by
  decide

theorem zero_allowance_cannot_begin (original : OriginalResult) (b : OrdinaryBudget) :
    ¬ ∃ next, Step (.gate original b 0) next := by
  rintro ⟨next, h⟩
  cases h

theorem cancelled_original_cannot_begin (original : OriginalResult)
    (hcancelled : original.cancelled = true) :
    ¬ ∃ next, Step (.gate original b (n + 1)) next := by
  rintro ⟨next, h⟩
  cases h with
  | beginCorrection trigger => exact Bool.noConfusion (hcancelled.symm.trans trigger.2.1)

theorem mechanical_falsifier_cannot_begin (original : OriginalResult)
    (hfalsifier : original.mechanicalFalsifier = true) :
    ¬ ∃ next, Step (.gate original b (n + 1)) next := by
  rintro ⟨next, h⟩
  cases h with
  | beginCorrection trigger => exact Bool.noConfusion (hfalsifier.symm.trans trigger.2.2.1)

theorem mismatched_reply_is_refused
    (h : reply.matches original = false) :
    authorGate original reply = .refused := by
  simp [authorGate, h]

theorem absent_reply_is_refused (reply : CorrectedReply)
    (hmatch : reply.matches original = true) (habsent : reply.form = .absent) :
    authorGate original reply = .refused := by
  simp [authorGate, hmatch, habsent]

theorem unrelated_correction_is_unqualified
    (reply : CorrectedReply) (request : CorrectionRequest) (original : OriginalResult)
    (h : reply.correctionId ≠ request.correctionId) :
    reply.qualifiedFor original request = false := by
  simp [CorrectedReply.qualifiedFor, h]

theorem incomplete_reply_is_unqualified
    (reply : CorrectedReply) (request : CorrectionRequest) (original : OriginalResult)
    (hincomplete : reply.completed = false) :
    reply.qualifiedFor original request = false := by
  simp [CorrectedReply.qualifiedFor, hincomplete]

theorem unproven_return_is_unqualified
    (reply : CorrectedReply) (request : CorrectionRequest) (original : OriginalResult)
    (hunproven : reply.returnProvenanceVerified = false) :
    reply.qualifiedFor original request = false := by
  simp [CorrectedReply.qualifiedFor, hunproven]

theorem cancelled_reply_is_unqualified
    (reply : CorrectedReply) (request : CorrectionRequest) (original : OriginalResult)
    (hcancelled : reply.cancelled = true) :
    reply.qualifiedFor original request = false := by
  simp [CorrectedReply.qualifiedFor, CorrectedReply.matches, hcancelled]

/-- Any transition to the qualified no-fresh-artifact result carries an
explicit completed, provenance-verified reply bound to the same correction
request and retained original. -/
theorem alreadySatisfied_step_only_if_qualified
    (h : Step s (.alreadySatisfied original request reply qualified b)) :
    reply.qualifiedFor original request = true ∧
      authorGate original reply = .alreadySatisfied := by
  cases h with
  | validRefusal gate => exact ⟨qualified, gate⟩

/-- A fresh `DONE` only reaches the existing build control point after the
separate supplied fresh-binding fact; it is not declared a successful repair. -/
theorem fresh_done_continues_only_at_row24
    (h : Step (.validated original request reply qualified b n)
      (.continuedToBuild original request reply qualified ordinary)) :
    reply.qualifiedFor original request = true ∧
      ordinary = .running OrdinaryClickRoute.Phase.p24 b := by
  cases h
  exact ⟨qualified, rfl⟩

#print axioms step_wellFounded
#print axioms noInfiniteCorrection
#print axioms corrected_refusal_reaches_only_alreadySatisfied
#print axioms done_at_base_remains_refused
#print axioms unrelated_example_is_unqualified
#print axioms incomplete_example_is_unqualified
#print axioms unproven_example_is_unqualified
#print axioms cancelled_example_is_unqualified
#print axioms zero_allowance_cannot_begin
#print axioms cancelled_original_cannot_begin
#print axioms mechanical_falsifier_cannot_begin
#print axioms mismatched_reply_is_refused
#print axioms absent_reply_is_refused
#print axioms unrelated_correction_is_unqualified
#print axioms incomplete_reply_is_unqualified
#print axioms unproven_return_is_unqualified
#print axioms cancelled_reply_is_unqualified
#print axioms alreadySatisfied_step_only_if_qualified
#print axioms fresh_done_continues_only_at_row24

end DarkTower.WarMachine.AuthorResponseCorrectionRoute
