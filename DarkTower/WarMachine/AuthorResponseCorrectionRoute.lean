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

/-- A later response must name the original request and result exactly. -/
structure CorrectedReply where
  correctionId : String
  requestId : String
  originalResultId : String
  binding : Binding
  cancelled : Bool
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

/-- The original result is present in every detour state; a reply appears only
after the bounded correction prompt/wait states. -/
inductive Node where
  | gate (original : OriginalResult) (ordinaryBudget : OrdinaryBudget) (allowance : Nat)
  | correctionPrompt (original : OriginalResult) (ordinaryBudget : OrdinaryBudget) (allowance : Nat)
  | correctionWait (original : OriginalResult) (ordinaryBudget : OrdinaryBudget) (allowance : Nat)
  | response (original : OriginalResult) (reply : CorrectedReply)
      (ordinaryBudget : OrdinaryBudget) (allowance : Nat)
  | alreadySatisfied (original : OriginalResult) (reply : CorrectedReply)
      (ordinaryBudget : OrdinaryBudget)
  | continuedToBuild (ordinary : OrdinaryClickRoute.Node)
  | refused (original : OriginalResult) (reply : CorrectedReply)
      (reason : Refusal) (ordinaryBudget : OrdinaryBudget)
  deriving DecidableEq, Repr

/-- The allowance is consumed on entry; the reply is retained and evaluated
only after wait.  A valid refusal terminates as an explicit no-fresh-artifact
outcome; a valid fresh `DONE` merely resumes the existing row-24 build path. -/
inductive Step : Node → Node → Prop where
  | beginCorrection (h : original.correctableDoneAtBase) :
      Step (.gate original b (n + 1)) (.correctionPrompt original b n)
  | prompted :
      Step (.correctionPrompt original b n) (.correctionWait original b n)
  | replied (reply : CorrectedReply) :
      Step (.correctionWait original b n) (.response original reply b n)
  | validRefusal (h : authorGate original reply = .alreadySatisfied) :
      Step (.response original reply b n) (.alreadySatisfied original reply b)
  | validFreshDone (h : authorGate original reply = .freshDone) :
      Step (.response original reply b n)
        (.continuedToBuild (.running OrdinaryClickRoute.Phase.p24 b))
  | invalidReply (h : authorGate original reply = .refused) :
      Step (.response original reply b n)
        (.refused original reply .invalidOrChangedReply b)

def measure : Node → Nat
  | .gate _ _ n => 3 * n + 1
  | .correctionPrompt _ _ n => 3 * n + 3
  | .correctionWait _ _ n => 3 * n + 2
  | .response _ _ _ n => 3 * n + 1
  | .alreadySatisfied _ _ _ | .continuedToBuild _ | .refused _ _ _ _ => 0

theorem step_decreases (h : Step s t) : measure t < measure s := by
  cases h
  case beginCorrection => simp [measure]; omega
  case prompted => simp [measure]
  case replied => simp [measure]
  case validRefusal => simp [measure]
  case validFreshDone => simp [measure]
  case invalidReply => simp [measure]

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

theorem exampleOriginal_is_precisely_correctable :
    exampleOriginal.correctableDoneAtBase := by
  simp [OriginalResult.correctableDoneAtBase, exampleOriginal, exampleBinding]

/-- Positive control: the later refusal returns through the author gate, not
directly to build/grounding. -/
theorem corrected_refusal_reaches_only_alreadySatisfied (b : OrdinaryBudget) :
    ∃ n, Step (.gate exampleOriginal b (n + 1)) (.correctionPrompt exampleOriginal b n) ∧
      Step (.correctionPrompt exampleOriginal b n) (.correctionWait exampleOriginal b n) ∧
      Step (.correctionWait exampleOriginal b n) (.response exampleOriginal correctedRefusal b n) ∧
      Step (.response exampleOriginal correctedRefusal b n)
        (.alreadySatisfied exampleOriginal correctedRefusal b) := by
  refine ⟨0, .beginCorrection exampleOriginal_is_precisely_correctable, .prompted,
    .replied correctedRefusal, ?_⟩
  apply Step.validRefusal
  decide

/-- The original `DONE <base>` remains refused even after a correction chance. -/
theorem done_at_base_remains_refused :
    authorGate exampleOriginal baseDoneReply = .refused := by
  simp [authorGate, CorrectedReply.matches, baseDoneReply, exampleOriginal, exampleBinding]

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

/-- A fresh `DONE` only reaches the existing build control point after the
separate supplied fresh-binding fact; it is not declared a successful repair. -/
theorem fresh_done_continues_only_at_row24
    (h : Step (.response original reply b n) (.continuedToBuild ordinary)) :
    ordinary = .running OrdinaryClickRoute.Phase.p24 b := by
  cases h
  rfl

#print axioms step_wellFounded
#print axioms noInfiniteCorrection
#print axioms corrected_refusal_reaches_only_alreadySatisfied
#print axioms done_at_base_remains_refused
#print axioms zero_allowance_cannot_begin
#print axioms cancelled_original_cannot_begin
#print axioms mechanical_falsifier_cannot_begin
#print axioms mismatched_reply_is_refused
#print axioms absent_reply_is_refused
#print axioms fresh_done_continues_only_at_row24

end DarkTower.WarMachine.AuthorResponseCorrectionRoute
