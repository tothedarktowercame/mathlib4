import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Ordinary click: phases 16–30 (LL1)

Source: futon2 `holes/labs/wm-contract/logic-model/phases.md`, rows 16–30,
including 24.1. Anchors use R = `full_loop_runner.clj`; IJ =
`interpretation_job.clj`. This is a table model, not a proof of Clojure conformance.
No payload, transport response, or approval is manufactured by these edges.

Conditional phases 16 and 19 have pass-through success edges when their work is
disabled. Row 21 branches out and terminates; it is not on the grounding path.
The success path visits 24.1 even with a zero cure budget (validation succeeds).

The table leaves author/reviewer/re-review retry, revision, and standing-completion
bounds unspecified: they are finite parameters. Cure defaults to zero as stated.
A staged reviewer-evidence correction allowance also defaults to zero.  Its
payload predicates are supplied by a future runtime adapter: this file proves
control and binding consequences, not transport authentication or Clojure
conformance.
A detour consumes its own allowance on entry, never replenishes another allowance,
and returns to the same main-line phase. This bounds control transitions, not the
wall-clock duration of a poll or debugger wait. Unbounded debugger restarts in the
table's separate “Branches” section are outside this 16–30 model.

Row 22's unbound D-task exit retains its dynamic kind as a String. Rows 23 and 26
mention cancellation/refusal without naming an exit, and 24.1 says “validation
failure after retries” without a keyword: these are phase-attributed exceptions.
Row 29 is buildFailed, optionally qualified by the two named evidence failures;
there is no separate reviewNotApproved keyword in the table.
-/

namespace DarkTower.WarMachine.OrdinaryClickRoute

/-- Row identities plus the explicitly listed dispatch/wait detours. -/
inductive Phase where
  | p16 | p17 | p18 | p19 | p20 | p21 | p22 | p23 | p24 | p24_1
  | p25 | p26 | p27 | p28 | p29 | p30
  | authorRetryDispatch | authorRetryWait
  | buildCureDispatch | buildCureWait
  | reviewerRetryDispatch | reviewerRetryWait
  | reviewEvidenceCorrectionDispatch | reviewEvidenceCorrectionWait
  | revisionDispatch | revisionWait | revisionBuild
  | reReviewDispatch | reReviewWait | reReviewRetryDispatch | reReviewRetryWait
  | standingCompletionDispatch | standingCompletionWait
  deriving DecidableEq, Repr

/-- Row 29 names these as reasons under :build-failed, not separate outcomes. -/
inductive BuildReason where
  | unspecified | reviewExecutionEvidenceMissing | reviewerFalsifierFailed
  deriving DecidableEq, Repr

/-- Exactly the named exits in the scoped table, with opaque unnamed exceptions. -/
inductive Exit where
  | agentUnavailable | policyNondiscrimination | constructionFailed
  | unboundDTask (kind : String)
  | buildFailed (reason : BuildReason)
  | artifactBindingMismatch
  | reviewEvidenceCorrectionRefused
  | exception (phase : Phase)
  | historicalAwaitingValidation
  | grounded
  deriving DecidableEq, Repr

/-- Remaining allowances; none of the unspecified bounds is silently fixed to one. -/
structure Budget where
  author : Nat
  reviewer : Nat
  cure : Nat := 0
  revision : Nat
  reReview : Nat
  standing : Nat
  reviewEvidenceCorrection : Nat := 0
  deriving DecidableEq, Repr

/-- Immutable identity carried by the proposed reviewer-evidence correction.
These strings are opaque pins supplied by the runtime adapter. -/
structure ReviewBinding where
  target : String
  author : String
  reviewer : String
  artifactRevision : String
  contractDigest : String
  deriving DecidableEq, Repr

/-- Supplied facts for the narrow correction admission.  `correctedBinding`
is kept separate so changed reviewer/artifact/contract payloads can be refused
rather than silently replacing the original pins. -/
structure ReviewEvidenceCorrection where
  originalBinding : ReviewBinding
  correctedBinding : ReviewBinding
  completedReview : Bool
  reason : BuildReason
  correctedEvidenceValid : Bool
  deriving DecidableEq, Repr

def ReviewEvidenceCorrection.triggered (c : ReviewEvidenceCorrection) : Prop :=
  c.completedReview = true ∧ c.reason = .reviewExecutionEvidenceMissing

def ReviewEvidenceCorrection.admissible (c : ReviewEvidenceCorrection) : Prop :=
  c.triggered ∧
  c.originalBinding.author ≠ c.originalBinding.reviewer ∧
  c.correctedBinding = c.originalBinding ∧
  c.correctedEvidenceValid = true

/-- Terminal nodes have no outgoing edges. -/
inductive Node where
  | running (phase : Phase) (budget : Budget)
  | stopped (exit : Exit)
  deriving DecidableEq, Repr

def start (b : Budget) : Node := .running .p16 b

/-- The table's unnamed exception sites, including the named retry subphases. -/
def exceptionAt (p : Phase) : Prop :=
  p ∈ [Phase.p18, .p19, .p22, .p23, .p25, .p26, .p30,
       .authorRetryDispatch, .authorRetryWait,
       .buildCureDispatch, .buildCureWait,
       .reviewerRetryDispatch, .reviewerRetryWait]

/-- Edges transcribed from the table. Success edges assert only control flow. -/
inductive Step : Node → Node → Prop where
  /-- Row 16, (R wake-restored-agent!): reviewer available, or no wake needed. -/
  | ready16 : Step (.running .p16 b) (.running .p17 b)
  /-- Row 16, (R run-opportunity-core! :agent-unavailable): uncast/busy/self-review. -/
  | unavailable16 : Step (.running .p16 b) (.stopped .agentUnavailable)
  /-- Row 17, (R run-opportunity-core! :policy-nondiscrimination): guard passes. -/
  | discriminate17 : Step (.running .p17 b) (.running .p18 b)
  /-- Row 17, (R run-opportunity-core! :policy-nondiscrimination): guard refuses. -/
  | nondiscrimination17 : Step (.running .p17 b) (.stopped .policyNondiscrimination)
  /-- Row 18, (R mint-action-occurrence-once!): occurrence minted. -/
  | occurrence18 : Step (.running .p18 b) (.running .p19 b)
  /-- Row 19, (IJ run!): interpretation completes, or receipt mode is disabled. -/
  | interpret19 : Step (.running .p19 b) (.running .p20 b)
  /-- Row 20, (R construct-for-decision): ordinary construction succeeds. -/
  | construct20 : Step (.running .p20 b) (.running .p22 b)
  /-- Rows 20–21, (R run-opportunity-core! :revalidate-historical-repair): branch out. -/
  | historical20 : Step (.running .p20 b) (.running .p21 b)
  /-- Row 20, (R construction-wiring-result): absent, invalid, or refused construction. -/
  | constructionFailed20 : Step (.running .p20 b) (.stopped .constructionFailed)
  /-- Row 21, (R run-opportunity-core! :historical-verification-awaiting-validation). -/
  | historical21 : Step (.running .p21 b) (.stopped .historicalAwaitingValidation)
  /-- Row 22, (R dispatch! :author-dispatch): dispatched or deferred job retained. -/
  | author22 : Step (.running .p22 b) (.running .p23 b)
  /-- Row 22, (R run-opportunity-core! :d-task-dispatch): retain the dynamic kind. -/
  | unbound22 (kind : String) : Step (.running .p22 b) (.stopped (.unboundDTask kind))
  /-- Row 23, (R poll-job! :author-wait): completed author job. -/
  | authorDone23 : Step (.running .p23 b) (.running .p24 b)
  /-- Row 23, (R run-opportunity-core! :build-failed): author did not finish. -/
  | authorFailed23 : Step (.running .p23 b) (.stopped (.buildFailed .unspecified))
  /-- Row 23, (R dispatch! :author-retry-dispatch): spend one retry allowance. -/
  | authorRetry23 :
      Step (.running .p23 {b with author := b.author + 1})
           (.running .authorRetryDispatch b)
  /-- Row 23, (R poll-job! :author-retry-wait): retry dispatch returns a job. -/
  | authorRetryDispatched : Step (.running .authorRetryDispatch b) (.running .authorRetryWait b)
  /-- Row 23, (R poll-job! :author-retry-wait): retry returns to the author result check. -/
  | authorRetryWaited : Step (.running .authorRetryWait b) (.running .p23 b)
  /-- Row 24, (R resolve-target-build): commit resolves to the target repository. -/
  | build24 : Step (.running .p24 b) (.running .p24_1 b)
  /-- Row 24, (R run-opportunity-core! :artifact-binding-mismatch): wrong repository binding. -/
  | mismatch24 : Step (.running .p24 b) (.stopped .artifactBindingMismatch)
  /-- Row 24, (R resolve-target-build): no verifiable commit. -/
  | noCommit24 : Step (.running .p24 b) (.stopped (.buildFailed .unspecified))
  /-- Row 24.1, (R build-cure-loop): validation passes without another cure. -/
  | cureDone : Step (.running .p24_1 b) (.running .p25 b)
  /-- Row 24.1, (R build-cure-loop :build-cure-retries): exhausted validation failure. -/
  | cureFailed (b : Budget) : Step (.running .p24_1 {b with cure := 0}) (.stopped (.exception .p24_1))
  /-- Row 24.1, (R build-cure-loop :build-cure-dispatch): spend a cure retry. -/
  | cureRetry :
      Step (.running .p24_1 {b with cure := b.cure + 1}) (.running .buildCureDispatch b)
  /-- Row 24.1, (R build-cure-loop :build-cure-wait): cure job dispatched. -/
  | cureDispatched : Step (.running .buildCureDispatch b) (.running .buildCureWait b)
  /-- Row 24.1, (R build-cure-loop): recheck the cured build. -/
  | cureWaited : Step (.running .buildCureWait b) (.running .p24_1 b)
  /-- Row 25, (R dispatch! :reviewer-dispatch): independent review job retained. -/
  | reviewer25 : Step (.running .p25 b) (.running .p26 b)
  /-- Row 26, (R poll-job! :reviewer-wait): review response proceeds to the gate. -/
  | reviewDone26 : Step (.running .p26 b) (.running .p27 b)
  /-- Row 26, (R dispatch! :reviewer-retry-dispatch): spend a review retry. -/
  | reviewerRetry26 :
      Step (.running .p26 {b with reviewer := b.reviewer + 1}) (.running .reviewerRetryDispatch b)
  /-- Row 26, (R poll-job! :reviewer-retry-wait): retry job dispatched. -/
  | reviewerRetryDispatched :
      Step (.running .reviewerRetryDispatch b) (.running .reviewerRetryWait b)
  /-- Row 26, (R poll-job! :reviewer-retry-wait): return to review response handling. -/
  | reviewerRetryWaited : Step (.running .reviewerRetryWait b) (.running .p26 b)
  /-- Row 27, (R review-execution-gate): retain the verdict for the later approval check. -/
  | gate27 : Step (.running .p27 b) (.running .p28 b)
  /-- Staged row-27 correction: only a completed review with the typed missing
  execution-evidence reason and exact immutable binding may spend this distinct
  allowance.  The validity/authentication facts are supplied premises. -/
  | reviewEvidenceCorrection27 (c : ReviewEvidenceCorrection)
      (_ : c.admissible) :
      Step (.running .p27 {b with reviewEvidenceCorrection := b.reviewEvidenceCorrection + 1})
           (.running .reviewEvidenceCorrectionDispatch b)
  | reviewEvidenceCorrectionDispatched :
      Step (.running .reviewEvidenceCorrectionDispatch b)
           (.running .reviewEvidenceCorrectionWait b)
  /-- Re-enter the same row-27 gate; correction never jumps to approval. -/
  | reviewEvidenceCorrectionWaited :
      Step (.running .reviewEvidenceCorrectionWait b) (.running .p27 b)
  /-- A triggered correction with altered reviewer/artifact/contract binding
  is an explicit refusal, never an accepted correction. -/
  | reviewEvidenceCorrectionBindingRefused (c : ReviewEvidenceCorrection)
      (_ : c.triggered) (_ : c.correctedBinding ≠ c.originalBinding) :
      Step (.running .p27 b) (.stopped .reviewEvidenceCorrectionRefused)
  /-- Row 27, (R run-revision-round :revision-dispatch): spend a revision allowance. -/
  | revise27 :
      Step (.running .p27 {b with revision := b.revision + 1}) (.running .revisionDispatch b)
  /-- Row 27, (R run-revision-round :revision-wait): revision dispatched. -/
  | revisionDispatched : Step (.running .revisionDispatch b) (.running .revisionWait b)
  /-- Row 27, (R run-revision-round :revision-build): revision answer received. -/
  | revisionWaited : Step (.running .revisionWait b) (.running .revisionBuild b)
  /-- Row 27, (R run-revision-round :re-review-dispatch): revision build proceeds to review. -/
  | revisionBuilt : Step (.running .revisionBuild b) (.running .reReviewDispatch b)
  /-- Row 27, (R run-revision-round :re-review-wait): re-review dispatched. -/
  | reReviewDispatched : Step (.running .reReviewDispatch b) (.running .reReviewWait b)
  /-- Row 27, (R run-revision-round): return the revision verdict to the gate. -/
  | reReviewWaited : Step (.running .reReviewWait b) (.running .p27 b)
  /-- Row 27, (R run-revision-round :re-review-retry-dispatch): spend a re-review retry. -/
  | reReviewRetry :
      Step (.running .reReviewWait {b with reReview := b.reReview + 1})
           (.running .reReviewRetryDispatch b)
  /-- Row 27, (R run-revision-round :re-review-retry-wait): retry dispatched. -/
  | reReviewRetryDispatched :
      Step (.running .reReviewRetryDispatch b) (.running .reReviewRetryWait b)
  /-- Row 27, (R run-revision-round): retry returns to re-review handling. -/
  | reReviewRetryWaited : Step (.running .reReviewRetryWait b) (.running .reReviewWait b)
  /-- Row 28, (R checkpoint! :build): retain the build before checking approval. -/
  | checkpoint28 : Step (.running .p28 b) (.running .p29 b)
  /-- Row 29, (R run-opportunity-core! :standing-completion-dispatch): bounded completion detour. -/
  | standing29 :
      Step (.running .p29 {b with standing := b.standing + 1})
           (.running .standingCompletionDispatch b)
  /-- Row 29, (R poll-job! :standing-completion-wait): completion dispatched. -/
  | standingDispatched :
      Step (.running .standingCompletionDispatch b) (.running .standingCompletionWait b)
  /-- Row 29, (R run-opportunity-core! :approved?): return to the approval check. -/
  | standingWaited : Step (.running .standingCompletionWait b) (.running .p29 b)
  /-- Row 29, (R run-opportunity-core! :approved?): approval permits grounding. -/
  | approved29 : Step (.running .p29 b) (.running .p30 b)
  /-- Row 29, (R run-opportunity-core! :build-failed): retain either named review reason. -/
  | notApproved29 (reason : BuildReason) :
      Step (.running .p29 b) (.stopped (.buildFailed reason))
  /-- Row 30, (R ground-commit!): grounding produces its terminal witness. -/
  | ground30 : Step (.running .p30 b) (.stopped .grounded)
  /-- Rows 18,19,22,23,24.1,25,26,30, (R run-phase!): unnamed exceptions at listed sites. -/
  | exception (h : exceptionAt p) : Step (.running p b) (.stopped (.exception p))

/-- Local order, including return edges inside detours. Entry spends budget. -/
def phaseRank : Phase → Nat
  | .p16 => 100 | .p17 => 95 | .p18 => 90 | .p19 => 85 | .p20 => 80
  | .p21 => 79 | .p22 => 75 | .p23 => 70 | .p24 => 65 | .p24_1 => 60
  | .p25 => 55 | .p26 => 50 | .p27 => 40 | .p28 => 20 | .p29 => 10 | .p30 => 0
  | .authorRetryDispatch => 72 | .authorRetryWait => 71
  | .buildCureDispatch => 62 | .buildCureWait => 61
  | .reviewerRetryDispatch => 52 | .reviewerRetryWait => 51
  | .reviewEvidenceCorrectionDispatch => 42 | .reviewEvidenceCorrectionWait => 41
  | .revisionDispatch => 47 | .revisionWait => 46 | .revisionBuild => 45
  | .reReviewDispatch => 44 | .reReviewWait => 43
  | .reReviewRetryDispatch => 45 | .reReviewRetryWait => 44
  | .standingCompletionDispatch => 12 | .standingCompletionWait => 11

def Budget.total (b : Budget) : Nat :=
  b.author + b.reviewer + b.cure + b.revision + b.reReview + b.standing +
    b.reviewEvidenceCorrection

/-- Every detour costs at least 128; every phase rank is below 128. -/
def measure : Node → Nat
  | .running p b => 128 * b.total + phaseRank p + 1
  | .stopped _ => 0

theorem step_decreases (h : Step s t) : measure t < measure s := by
  cases h <;> simp only [measure, Budget.total, phaseRank] <;> omega

/-- Explicit well-founded relation used to rule out infinite detour paths. -/
theorem step_wellFounded : WellFounded (fun t s => Step s t) :=
  Subrelation.wf (fun h => step_decreases h) (InvImage.wf measure Nat.lt_wfRel.wf)

/-- Paths include both endpoints, so phase visits are not implicit in an edge. -/
inductive Path : Node → List Node → Node → Prop where
  | single (s) : Path s [s] s
  | cons : Step s t → Path t xs u → Path s (s :: xs) u

def Maximal (s : Node) : Prop := ¬ ∃ t, Step s t

theorem progress (p : Phase) (b : Budget) : ∃ t, Step (.running p b) t := by
  cases p
  all_goals first
    | exact ⟨_, Step.ready16⟩
    | exact ⟨_, Step.discriminate17⟩
    | exact ⟨_, Step.occurrence18⟩
    | exact ⟨_, Step.interpret19⟩
    | exact ⟨_, Step.construct20⟩
    | exact ⟨_, Step.historical21⟩
    | exact ⟨_, Step.author22⟩
    | exact ⟨_, Step.authorDone23⟩
    | exact ⟨_, Step.build24⟩
    | exact ⟨_, Step.cureDone⟩
    | exact ⟨_, Step.reviewer25⟩
    | exact ⟨_, Step.reviewDone26⟩
    | exact ⟨_, Step.gate27⟩
    | exact ⟨_, Step.checkpoint28⟩
    | exact ⟨_, Step.approved29⟩
    | exact ⟨_, Step.ground30⟩
    | exact ⟨_, Step.authorRetryDispatched⟩
    | exact ⟨_, Step.authorRetryWaited⟩
    | exact ⟨_, Step.cureDispatched⟩
    | exact ⟨_, Step.cureWaited⟩
    | exact ⟨_, Step.reviewerRetryDispatched⟩
    | exact ⟨_, Step.reviewerRetryWaited⟩
    | exact ⟨_, Step.reviewEvidenceCorrectionDispatched⟩
    | exact ⟨_, Step.reviewEvidenceCorrectionWaited⟩
    | exact ⟨_, Step.revisionDispatched⟩
    | exact ⟨_, Step.revisionWaited⟩
    | exact ⟨_, Step.revisionBuilt⟩
    | exact ⟨_, Step.reReviewDispatched⟩
    | exact ⟨_, Step.reReviewWaited⟩
    | exact ⟨_, Step.reReviewRetryDispatched⟩
    | exact ⟨_, Step.reReviewRetryWaited⟩
    | exact ⟨_, Step.standingDispatched⟩
    | exact ⟨_, Step.standingWaited⟩

/-- No infinite sequence of edges, even from states other than the entry state. -/
theorem noInfinitePath (run : Nat → Node) (edges : ∀ n, Step (run n) (run (n + 1))) :
    False := by
  have bound : ∀ n, n + measure (run n) ≤ measure (run 0) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have := step_decreases (edges n)
      omega
  have := bound (measure (run 0) + 1)
  omega

/-- The exact main-line witness, including the zero-cure visit to row 24.1. -/
def mainPhases : List Phase :=
  [.p16, .p17, .p18, .p19, .p20, .p22, .p23, .p24, .p24_1,
   .p25, .p26, .p27, .p28, .p29, .p30]

def groundingTrace (b : Budget) : List Node :=
  mainPhases.map (fun p => .running p b) ++ [.stopped .grounded]

/-- Theorem 2: each consecutive pair in the displayed main line is an edge. -/
theorem grounding_reachable (b : Budget) :
    Path (start b) (groundingTrace b) (.stopped .grounded) := by
  unfold start groundingTrace mainPhases
  exact .cons .ready16 (.cons .discriminate17 (.cons .occurrence18
    (.cons .interpret19 (.cons .construct20 (.cons .author22
    (.cons .authorDone23 (.cons .build24 (.cons .cureDone
    (.cons .reviewer25 (.cons .reviewDone26 (.cons .gate27
    (.cons .checkpoint28 (.cons .approved29 (.cons .ground30 (.single _)))))))))))))))

/-- Theorem 1: every maximal path is finite and ends at a named terminal.
The first conjunct excludes the infinite alternative; the second classifies every
finite maximal path; the third supplies a maximal path (not merely a vacuous law). -/
theorem termination_totality (b : Budget) :
    (¬ ∃ run : Nat → Node, run 0 = start b ∧ ∀ n, Step (run n) (run (n + 1))) ∧
    (∀ xs last, Path (start b) xs last → Maximal last → ∃ e, last = .stopped e) ∧
    (∃ xs e, Path (start b) xs (.stopped e) ∧ Maximal (.stopped e)) := by
  constructor
  · rintro ⟨run, _, edges⟩
    exact noInfinitePath run edges
  constructor
  · intro xs last _ maximal
    cases last with
    | running p fuel => exact False.elim (maximal (progress p fuel))
    | stopped e => exact ⟨e, rfl⟩
  · refine ⟨groundingTrace b, .grounded, grounding_reachable b, ?_⟩
    rintro ⟨t, h⟩
    cases h

def atPhase (p : Phase) : Node → Prop
  | .running q _ => q = p
  | .stopped _ => False

def Visits (p : Phase) (xs : List Node) : Prop := ∃ n ∈ xs, atPhase p n

/-- A non-grounding exit stays on the pre-checkpoint side of either review cut. -/
def Before (p : Phase) : Node → Prop
  | .running q _ => phaseRank p ≤ phaseRank q
  | .stopped e => e ≠ .grounded

/-- Only the actual checkpoint can cross either review cut. -/
theorem preserves_review_cut (which : p = .p25 ∨ p = .p29)
    (edge : Step s t) (before : Before p s) (avoid : ¬ atPhase p s) :
    Before p t := by
  rcases which with rfl | rfl
  all_goals cases edge <;> simp_all [Before, atPhase, phaseRank]

theorem path_preserves_review_cut (which : p = .p25 ∨ p = .p29)
    (path : Path s xs t) (before : Before p s) (avoid : ¬ Visits p xs) :
    Before p t := by
  induction path with
  | single s => exact before
  | @cons s u xs t edge path ih =>
    have avoidHead : ¬ atPhase p s := by
      intro h
      exact avoid ⟨s, by simp, h⟩
    have avoidTail : ¬ Visits p xs := by
      rintro ⟨n, hn, hp⟩
      exact avoid ⟨n, by simp [hn], hp⟩
    exact ih (preserves_review_cut which edge before avoidHead) avoidTail

/-- Theorem 3: grounding cannot silently skip reviewer dispatch or approval. -/
theorem no_silent_skip (b : Budget) (path : Path (start b) xs (.stopped .grounded)) :
    Visits .p25 xs ∧ Visits .p29 xs := by
  have visit (p : Phase) (which : p = .p25 ∨ p = .p29) : Visits p xs := by
    by_contra avoid
    have initial : Before p (start b) := by
      rcases which with rfl | rfl <;> simp [Before, start, phaseRank]
    have h := path_preserves_review_cut which path initial avoid
    exact h rfl
  exact ⟨visit .p25 (Or.inl rfl), visit .p29 (Or.inr rfl)⟩

/-! ## Staged reviewer-evidence correction properties -/

def retainedBinding : ReviewBinding where
  target := "M-example"
  author := "author"
  reviewer := "reviewer"
  artifactRevision := "0123456789abcdef"
  contractDigest := "contract-v1"

def validCorrection : ReviewEvidenceCorrection where
  originalBinding := retainedBinding
  correctedBinding := retainedBinding
  completedReview := true
  reason := .reviewExecutionEvidenceMissing
  correctedEvidenceValid := true

theorem validCorrection_admissible : validCorrection.admissible := by
  simp [ReviewEvidenceCorrection.admissible,
    ReviewEvidenceCorrection.triggered, validCorrection, retainedBinding]

/-- Positive control: one allowance gives one correction, then re-enters the
same gate and only the ordinary gate edge proceeds. -/
theorem one_review_evidence_correction_revalidates_at_same_gate (b : Budget) :
    Path (.running .p27
        {b with reviewEvidenceCorrection := b.reviewEvidenceCorrection + 1})
      [.running .p27
          {b with reviewEvidenceCorrection := b.reviewEvidenceCorrection + 1},
       .running .reviewEvidenceCorrectionDispatch b,
       .running .reviewEvidenceCorrectionWait b,
       .running .p27 b,
       .running .p28 b]
      (.running .p28 b) := by
  exact .cons (.reviewEvidenceCorrection27 validCorrection validCorrection_admissible)
    (.cons .reviewEvidenceCorrectionDispatched
      (.cons .reviewEvidenceCorrectionWaited (.cons .gate27 (.single _))))

/-- A corrected response may still request changes: after returning to the
same gate it can take the pre-existing revision edge, never coerced approval. -/
theorem corrected_review_can_follow_existing_revision (b : Budget) :
    Path (.running .reviewEvidenceCorrectionWait
            {b with revision := b.revision + 1})
      [.running .reviewEvidenceCorrectionWait {b with revision := b.revision + 1},
       .running .p27 {b with revision := b.revision + 1},
       .running .revisionDispatch b]
      (.running .revisionDispatch b) := by
  exact .cons .reviewEvidenceCorrectionWaited (.cons .revise27 (.single _))

/-- Zero allowance cannot take a correction edge.  Hence a second correction
after the one-bounce witness is unavailable unless separately supplied. -/
theorem zero_allowance_cannot_correct (b : Budget)
    (h : b.reviewEvidenceCorrection = 0) :
    ¬ ∃ c next, Step (.running .p27 b) next ∧
      next = .running .reviewEvidenceCorrectionDispatch c := by
  rintro ⟨c, next, edge, rfl⟩
  cases edge <;> simp_all

/-- Any accepted correction edge exposes the exact typed trigger, reviewer
independence, immutable binding, and supplied evidence-validity premises. -/
theorem correction_edge_only_if_admissible
    (edge : Step (.running .p27 b)
      (.running .reviewEvidenceCorrectionDispatch b')) :
    ∃ c : ReviewEvidenceCorrection, c.triggered ∧
      c.originalBinding.author ≠ c.originalBinding.reviewer ∧
      c.correctedBinding = c.originalBinding ∧
      c.correctedEvidenceValid = true := by
  cases edge with
  | reviewEvidenceCorrection27 c hc =>
      exact ⟨c, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩

/-- The mechanical falsifier terminal is row 29 and has no correction edge.
This includes the retained selected-want/evidence-authority failure scope. -/
theorem reviewer_falsifier_cannot_enter_review_evidence_correction (b : Budget) :
    ¬ Step (.running .p29 b) (.running .reviewEvidenceCorrectionDispatch b') := by
  intro h
  cases h

/-- Correction cannot skip the same review gate and land at approval. -/
theorem correction_wait_cannot_skip_gate (b : Budget) :
    ¬ Step (.running .reviewEvidenceCorrectionWait b) (.running .p28 b') := by
  intro h
  cases h

#print axioms termination_totality
#print axioms grounding_reachable
#print axioms no_silent_skip
#print axioms one_review_evidence_correction_revalidates_at_same_gate
#print axioms corrected_review_can_follow_existing_revision
#print axioms zero_allowance_cannot_correct
#print axioms correction_edge_only_if_admissible
#print axioms reviewer_falsifier_cannot_enter_review_evidence_correction
#print axioms correction_wait_cannot_skip_gate

end DarkTower.WarMachine.OrdinaryClickRoute
