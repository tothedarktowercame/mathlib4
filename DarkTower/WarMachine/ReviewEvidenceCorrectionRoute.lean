import DarkTower.WarMachine.OrdinaryClickRoute
import Lean.Elab.Tactic.Omega

/-!
# State-indexed reviewer-evidence correction at ordinary row 27

This is a narrow refinement of `OrdinaryClickRoute`'s row-27 control point.
The actual completed review and immutable request binding occur in the source
state.  Dispatch depends only on that state's typed missing-execution-evidence
result.  A reply and its checker result first appear after the wait state.

All identity, checker, and evidence facts are supplied by a future runtime
adapter.  This module proves conditional orchestration properties, not Clojure
conformance, transport authentication, or the truth of supplied evidence.
-/

namespace DarkTower.WarMachine.ReviewEvidenceCorrectionRoute

abbrev OrdinaryBudget := OrdinaryClickRoute.Budget

inductive GateResult where
  | passed
  | requestChanges
  | missingExecutionEvidence
  | otherFailure
  deriving DecidableEq, Repr

/-- Pins that must survive request, wait, reply, and revalidation unchanged. -/
structure Binding where
  target : String
  author : String
  reviewer : String
  artifactRevision : String
  contractDigest : String
  deriving DecidableEq, Repr

/-- The actual row-27 review state, not an existential receipt argument. -/
structure ReviewState where
  binding : Binding
  checker : String
  completed : Bool
  result : GateResult
  deriving DecidableEq, Repr

def ReviewState.correctionTrigger (r : ReviewState) : Prop :=
  r.completed = true ∧
  r.result = .missingExecutionEvidence ∧
  r.binding.author ≠ r.binding.reviewer

/-- Returned payload.  It does not exist in dispatch or wait nodes. -/
structure Reply where
  binding : Binding
  checkedBy : String
  result : GateResult
  deriving DecidableEq, Repr

def Reply.matches (reply : Reply) (original : ReviewState) : Prop :=
  reply.binding = original.binding ∧ reply.checkedBy = original.checker

def Reply.acceptable (reply : Reply) (original : ReviewState) : Prop :=
  reply.matches original ∧
    (reply.result = .passed ∨ reply.result = .requestChanges)

inductive Refusal where
  | responseInvalidOrChanged
  deriving DecidableEq, Repr

/-- The original review and binding are state indices throughout the detour. -/
inductive Node where
  | gate (actual : ReviewState) (ordinaryBudget : OrdinaryBudget) (corrections : Nat)
  | dispatch (original : ReviewState) (ordinaryBudget : OrdinaryBudget) (corrections : Nat)
  | wait (original : ReviewState) (ordinaryBudget : OrdinaryBudget) (corrections : Nat)
  | response (original : ReviewState) (reply : Reply)
      (ordinaryBudget : OrdinaryBudget) (corrections : Nat)
  | continued (ordinary : OrdinaryClickRoute.Node)
  | refused (reason : Refusal) (ordinaryBudget : OrdinaryBudget)
  | mechanicalFalsifierFailure (ordinaryBudget : OrdinaryBudget)
  deriving DecidableEq, Repr

/-- The correction consumes one allowance on entry.  A reply is checked only
after it arrives.  Success returns to this same gate with the checked result;
request-changes still uses the existing revision destination. -/
inductive Step : Node → Node → Prop where
  | correction (h : actual.correctionTrigger) :
      Step (.gate actual b (n + 1)) (.dispatch actual b n)
  | dispatched : Step (.dispatch original b n) (.wait original b n)
  | replied (reply : Reply) :
      Step (.wait original b n) (.response original reply b n)
  | responsePassed (hmatch : reply.matches original)
      (hresult : reply.result = .passed) :
      Step (.response original reply b n)
        (.gate { original with result := .passed } b n)
  | responseRequestsChanges (hmatch : reply.matches original)
      (hresult : reply.result = .requestChanges) :
      Step (.response original reply b n)
        (.gate { original with result := .requestChanges } b n)
  | responseRefused (h : ¬ reply.acceptable original) :
      Step (.response original reply b n) (.refused .responseInvalidOrChanged b)
  | gatePassed (h : actual.completed = true ∧ actual.result = .passed) :
      Step (.gate actual b n)
        (.continued (.running OrdinaryClickRoute.Phase.p28 b))
  | gateRequestsChanges
      (h : actual.completed = true ∧ actual.result = .requestChanges) :
      Step (.gate actual {b with revision := b.revision + 1} n)
        (.continued (.running OrdinaryClickRoute.Phase.revisionDispatch b))

/-- Local termination measure.  Continued/refused/mechanical states are terminal. -/
def measure : Node → Nat
  | .gate _ _ n => 4 * n + 1
  | .dispatch _ _ n => 4 * n + 4
  | .wait _ _ n => 4 * n + 3
  | .response _ _ _ n => 4 * n + 2
  | .continued _ | .refused _ _ | .mechanicalFalsifierFailure _ => 0

theorem step_decreases (h : Step s t) : measure t < measure s := by
  cases h <;> simp only [measure] <;> omega

theorem step_wellFounded : WellFounded (fun t s => Step s t) :=
  Subrelation.wf (fun h => step_decreases h) (InvImage.wf measure Nat.lt_wfRel.wf)

theorem noInfiniteDetour (run : Nat → Node)
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

/-- Erase the refinement to the existing ordinary control point.  Detour
steps stutter at p27; successful gate/revision exits are existing base edges. -/
def project : Node → OrdinaryClickRoute.Node
  | .gate _ b _ | .dispatch _ b _ | .wait _ b _ | .response _ _ b _ =>
      .running OrdinaryClickRoute.Phase.p27 b
  | .continued ordinary => ordinary
  | .refused _ b => .running OrdinaryClickRoute.Phase.p27 b
  | .mechanicalFalsifierFailure _ =>
      .stopped (.buildFailed OrdinaryClickRoute.BuildReason.reviewerFalsifierFailed)

theorem step_projects_to_stutter_or_ordinary (h : Step s t) :
    project s = project t ∨ OrdinaryClickRoute.Step (project s) (project t) := by
  cases h with
  | correction _ => exact .inl rfl
  | dispatched => exact .inl rfl
  | replied _ => exact .inl rfl
  | responsePassed _ _ => exact .inl rfl
  | responseRequestsChanges _ _ => exact .inl rfl
  | responseRefused _ => exact .inl rfl
  | gatePassed _ => exact .inr .gate27
  | gateRequestsChanges _ => exact .inr .revise27

def exampleBinding : Binding where
  target := "M-example"
  author := "author"
  reviewer := "reviewer"
  artifactRevision := "0123456789abcdef"
  contractDigest := "contract-v1"

def missingReview : ReviewState where
  binding := exampleBinding
  checker := "review-execution-gate-v1"
  completed := true
  result := .missingExecutionEvidence

def passingReply : Reply where
  binding := exampleBinding
  checkedBy := "review-execution-gate-v1"
  result := .passed

theorem missingReview_triggered : missingReview.correctionTrigger := by
  simp [ReviewState.correctionTrigger, missingReview, exampleBinding]

inductive Path : Node → List Node → Node → Prop where
  | single (s) : Path s [s] s
  | cons : Step s t → Path t xs u → Path s (s :: xs) u

/-- Positive control: the actual missing review authorizes dispatch; only after
the matching reply arrives is it checked and returned to the same gate. -/
theorem matching_reply_revalidates_at_same_gate (b : OrdinaryBudget) :
    Path (.gate missingReview b 1)
      [.gate missingReview b 1,
       .dispatch missingReview b 0,
       .wait missingReview b 0,
       .response missingReview passingReply b 0,
       .gate {missingReview with result := .passed} b 0,
       .continued (.running OrdinaryClickRoute.Phase.p28 b)]
      (.continued (.running OrdinaryClickRoute.Phase.p28 b)) := by
  refine .cons (.correction missingReview_triggered) ?_
  refine .cons .dispatched ?_
  refine .cons (.replied passingReply) ?_
  refine .cons (.responsePassed ?_ rfl) ?_
  · simp [Reply.matches, passingReply, missingReview]
  exact .cons (.gatePassed ⟨rfl, rfl⟩) (.single _)

/-- An actual nonmissing review cannot enter correction; an unrelated valid
reply is irrelevant because no reply is consulted at entry. -/
theorem nonmissing_actual_cannot_dispatch (actual : ReviewState)
    (hresult : actual.result ≠ .missingExecutionEvidence) :
    ¬ Step (.gate actual b (n + 1)) (.dispatch actual b n) := by
  intro h
  cases h with
  | correction trigger => exact hresult trigger.2.1

/-- Zero allowance has no correction transition. -/
theorem zero_allowance_cannot_dispatch (actual : ReviewState) :
    ¬ ∃ next, Step (.gate actual b 0) next ∧
      next = .dispatch actual b n := by
  rintro ⟨next, h, rfl⟩
  cases h

/-- A wrong binding/checker reply cannot be consumed into a corrected gate. -/
theorem wrong_reply_cannot_return_to_gate (hwrong : ¬ reply.matches original) :
    ¬ ∃ actual, Step (.response original reply b n) (.gate actual b n) := by
  rintro ⟨actual, h⟩
  cases h with
  | responsePassed hmatch _ => exact hwrong hmatch
  | responseRequestsChanges hmatch _ => exact hwrong hmatch

/-- The original immutable binding is preserved on every successful return. -/
theorem successful_return_preserves_binding
    (h : Step (.response original reply b n) (.gate actual b n)) :
    actual.binding = original.binding := by
  cases h <;> simp

/-- Evidence validity cannot be checked before a reply exists: dispatch can
only advance to wait, never to a corrected gate. -/
theorem dispatch_cannot_return_before_reply :
    ¬ Step (.dispatch original b n) (.gate actual b n') := by
  intro h
  cases h

/-- Row-29 mechanical falsifier failure is terminal in this refinement. -/
theorem mechanical_falsifier_has_no_correction (b : OrdinaryBudget) :
    ¬ ∃ next, Step (.mechanicalFalsifierFailure b) next := by
  rintro ⟨next, h⟩
  cases h

/-- Any successful continuation to row 28 comes only from the same gate with
a completed, rechecked passing result; there is no correction-to-approval edge. -/
theorem row28_only_after_same_gate
    (h : Step s (.continued (.running OrdinaryClickRoute.Phase.p28 b))) :
    ∃ actual n, s = .gate actual b n ∧
      actual.completed = true ∧ actual.result = .passed := by
  cases h with
  | gatePassed hgate => exact ⟨_, _, rfl, hgate.1, hgate.2⟩

#print axioms step_wellFounded
#print axioms noInfiniteDetour
#print axioms step_projects_to_stutter_or_ordinary
#print axioms matching_reply_revalidates_at_same_gate
#print axioms nonmissing_actual_cannot_dispatch
#print axioms zero_allowance_cannot_dispatch
#print axioms wrong_reply_cannot_return_to_gate
#print axioms successful_return_preserves_binding
#print axioms dispatch_cannot_return_before_reply
#print axioms mechanical_falsifier_has_no_correction
#print axioms row28_only_after_same_gate

end DarkTower.WarMachine.ReviewEvidenceCorrectionRoute
