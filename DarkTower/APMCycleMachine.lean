/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.ExperimentalDesign

/-!
# APM cycle machine

This is the behavioural model for the live Clojure countdown controller.  It
models the protocol spine rather than a fabricated research trace: a campaign
registration is admissible only when it names the exact generated contract,
and phase advancement follows that contract.

The first bridge target is the F23 defect.  A registration which omits
`promoteSolver` after `verify` is rejected even though all of its individual
records may have valid shapes.
-/

namespace DarkTower.APMCycleMachine

inductive Phase
  | preflight
  | solve
  | verify
  | promoteSolver
  | studentAttempt1
  | guideIntervention1
  | studentAttempt2
  | guideIntervention2
  | studentAttempt3
  | scribeReduce
  | closeFrame
  deriving DecidableEq, Repr

def canonicalPhaseOrder : List Phase :=
  [.preflight, .solve, .verify, .promoteSolver,
   .studentAttempt1, .guideIntervention1,
   .studentAttempt2, .guideIntervention2,
   .studentAttempt3, .scribeReduce, .closeFrame]

structure Contract where
  id : String
  phases : List Phase
  deriving DecidableEq, Repr

def canonicalContract : Contract where
  id := "apm-complete-frame-cycle-v2"
  phases := canonicalPhaseOrder

structure Registration where
  campaignId : String
  manifestHash : String
  contractId : String
  phases : List Phase
  deriving DecidableEq, Repr

def Registration.matches (contract : Contract) (registration : Registration) : Prop :=
  registration.contractId = contract.id ∧ registration.phases = contract.phases

instance (contract : Contract) (registration : Registration) :
    Decidable (registration.matches contract) := by
  unfold Registration.matches
  infer_instance

def nextPhase? : Phase → Option Phase
  | .preflight => some .solve
  | .solve => some .verify
  | .verify => some .promoteSolver
  | .promoteSolver => some .studentAttempt1
  | .studentAttempt1 => some .guideIntervention1
  | .guideIntervention1 => some .studentAttempt2
  | .studentAttempt2 => some .guideIntervention2
  | .guideIntervention2 => some .studentAttempt3
  | .studentAttempt3 => some .scribeReduce
  | .scribeReduce => some .closeFrame
  | .closeFrame => none

structure MachineState where
  campaignId : String
  manifestHash : String
  phase : Phase
  ledgerVersion : Nat
  activeClaim : Option String
  deriving DecidableEq, Repr

structure Receipt where
  campaignId : String
  manifestHash : String
  fromPhase : Phase
  toPhase : Phase
  deriving DecidableEq, Repr

structure DispatchObservation where
  announcedJobId : String
  activatedJobId : String
  activationAccepted : Bool
  reactivatedJobId : String
  terminalJobId : String
  commandOwnExit : Option Nat
  claimPersisted : Bool
  receiptPersisted : Bool
  resumedJobId : String
  clientTimeoutObserved : Bool
  timeoutTreatedAsSuccess : Bool
  deriving DecidableEq, Repr

def validDispatch (observation : DispatchObservation) : Prop :=
  observation.announcedJobId ≠ "" ∧
  observation.activatedJobId = observation.announcedJobId ∧
  observation.activationAccepted = true ∧
  observation.reactivatedJobId = observation.announcedJobId ∧
  observation.terminalJobId = observation.announcedJobId ∧
  observation.commandOwnExit = some 0 ∧
  observation.claimPersisted = true ∧
  observation.receiptPersisted = true ∧
  observation.resumedJobId = observation.announcedJobId ∧
  observation.timeoutTreatedAsSuccess = false

theorem client_timeout_never_establishes_success
    (observation : DispatchObservation) (h : validDispatch observation)
    (_htimeout : observation.clientTimeoutObserved = true) :
    observation.timeoutTreatedAsSuccess = false := h.2.2.2.2.2.2.2.2.2

structure StudentBinding where
  ordinal : Nat
  sessionId : String
  snapshotDigest : String
  deriving DecidableEq, Repr

/-- JSON role submissions carry enum values as strings.  The deterministic
adapter canonicalizes the one accepted close result before policy validation;
the model does not require an LLM to synthesize an EDN keyword over JSON. -/
def canonicalCloseResult (wireValue : String) : Option String :=
  if wireValue = "closed" then some "closed"
  else if wireValue = "partial" then some "partial"
  else none

def validCloseWireResult (wireValue : String) : Prop :=
  canonicalCloseResult wireValue = some "closed" ∨
  canonicalCloseResult wireValue = some "partial"

theorem json_closed_result_is_accepted : validCloseWireResult "closed" := by
  simp [validCloseWireResult, canonicalCloseResult]

theorem partial_json_result_is_accepted : validCloseWireResult "partial" := by
  simp [validCloseWireResult, canonicalCloseResult]

theorem void_wire_result_is_refused : ¬ validCloseWireResult "void" := by
  simp [validCloseWireResult, canonicalCloseResult]

/-- Reset is a rotation, not merely clearing a registry cell.  The next
invocation must mint a nonempty id distinct from the previously inhabited id. -/
structure SessionRotation where
  previousId : String
  nextId : String
  deriving DecidableEq, Repr

def validSessionRotation (rotation : SessionRotation) : Prop :=
  rotation.previousId ≠ "" ∧ rotation.nextId ≠ "" ∧
  rotation.previousId ≠ rotation.nextId

def f25ReusedStudentSession : SessionRotation where
  previousId := "zai-5cb28d42"
  nextId := "zai-5cb28d42"

theorem f25_reused_student_session_refused :
    ¬ validSessionRotation f25ReusedStudentSession := by
  simp [validSessionRotation, f25ReusedStudentSession]

/-- Session freshness is a closure condition.  A historical violation remains
visible by making the frame partial; it must not erase a separately verified
solved problem or block banking that proof. -/
def validSessionEvidenceForFrame (frameResult : String)
    (rotation : SessionRotation) : Prop :=
  frameResult = "partial" ∨ validSessionRotation rotation

theorem f25_reused_session_requires_partial_frame :
    validSessionEvidenceForFrame "partial" f25ReusedStudentSession := by
  simp [validSessionEvidenceForFrame]

theorem f25_reused_session_cannot_support_closed_frame :
    ¬ validSessionEvidenceForFrame "closed" f25ReusedStudentSession := by
  simp [validSessionEvidenceForFrame, validSessionRotation,
        f25ReusedStudentSession]

/-- Fresh conversational sessions are not sufficient isolation: before the
next Student attempt, the prior worktree state must be durably preserved and
the active worktree returned to the registered base revision. -/
structure StudentAttemptWorkspaceTransition where
  priorHead : String
  baseRevision : String
  resultingHead : String
  preservationRef : String
  preservationDigest : String
  cleanAfter : Bool
  deriving DecidableEq, Repr

def validStudentAttemptWorkspaceTransition
    (t : StudentAttemptWorkspaceTransition) : Prop :=
  t.priorHead ≠ "" ∧ t.baseRevision ≠ "" ∧
  t.resultingHead = t.baseRevision ∧
  t.preservationRef ≠ "" ∧ t.preservationDigest ≠ "" ∧
  t.cleanAfter = true

def unpreservedStudentReset : StudentAttemptWorkspaceTransition where
  priorHead := "attempt-1-head"
  baseRevision := "registered-base"
  resultingHead := "registered-base"
  preservationRef := ""
  preservationDigest := ""
  cleanAfter := true

theorem unpreserved_student_reset_is_refused :
    ¬ validStudentAttemptWorkspaceTransition unpreservedStudentReset := by
  simp [validStudentAttemptWorkspaceTransition, unpreservedStudentReset]

/-! A Student terminal is evidential only when the controller preserves the
exact candidate before it certifies the phase receipt.  This applies equally
to a normal typed submission and to a controller-authored missing-observation
receipt: compilation without a durable receipt binding is not an observation. -/
structure StudentTerminalCandidate where
  attemptOrdinal : Nat
  candidateHead : String
  candidateRef : String
  candidateDigest : String
  problemBlob : String
  leanExit : Nat
  worktreeClean : Bool
  persistedBeforeReceipt : Bool
  receiptCandidateDigest : String
  deriving DecidableEq, Repr

def validStudentTerminalCandidate (candidate : StudentTerminalCandidate) : Prop :=
  candidate.attemptOrdinal ∈ [1, 2, 3] ∧
  candidate.candidateHead ≠ "" ∧ candidate.candidateRef ≠ "" ∧
  candidate.candidateDigest ≠ "" ∧ candidate.problemBlob ≠ "" ∧
  candidate.leanExit = 0 ∧ candidate.worktreeClean = true ∧
  candidate.persistedBeforeReceipt = true ∧
  candidate.receiptCandidateDigest = candidate.candidateDigest

def f30CompiledButUnrecordedCandidate : StudentTerminalCandidate where
  attemptOrdinal := 3
  candidateHead := "5865822658658226586582265865822658658226"
  candidateRef :=
    "refs/apm/preserved-student-attempts/f30/a01J06/58658226"
  candidateDigest := "f30-student-candidate"
  problemBlob := "f30-student-main-blob"
  leanExit := 0
  worktreeClean := true
  persistedBeforeReceipt := true
  receiptCandidateDigest := ""

theorem f30_compiling_candidate_without_receipt_binding_is_refused :
    ¬ validStudentTerminalCandidate f30CompiledButUnrecordedCandidate := by
  simp [validStudentTerminalCandidate, f30CompiledButUnrecordedCandidate]

def certifiedStudentCandidate : StudentTerminalCandidate where
  attemptOrdinal := 3
  candidateHead := "student-head"
  candidateRef := "refs/apm/student-candidates/f/p/attempt-3/student-head"
  candidateDigest := "candidate-digest"
  problemBlob := "problem-blob"
  leanExit := 0
  worktreeClean := true
  persistedBeforeReceipt := true
  receiptCandidateDigest := "candidate-digest"

theorem certified_student_candidate_is_valid :
    validStudentTerminalCandidate certifiedStudentCandidate := by
  simp [validStudentTerminalCandidate, certifiedStudentCandidate]

/-! Candidate validation and Student observation are separate controller
decisions. A rejected candidate remains durable evidence, but it cannot be
certified and does not prevent a typed-missing observation receipt. -/
inductive StudentCandidateDisposition
  | certified
  | rejectedEvidence
  deriving DecidableEq, Repr

def candidateMaySupplyCertifiedHead : StudentCandidateDisposition → Bool
  | .certified => true
  | .rejectedEvidence => false

def candidateMaySupplyCertifiedObservation : StudentCandidateDisposition → Bool
  | .certified => true
  | .rejectedEvidence => false

/-- Candidate certification and recovery of the Student's completed observation
are independent.  A rejected candidate may be retained as evidence only; a
controller may recover the observation from the durable job trace. -/
inductive StudentObservationDisposition
  | typedStudentReceipt
  | controllerRecovered
  | genuinelyMissing
  deriving DecidableEq, Repr

def observationSatisfied : StudentObservationDisposition → Bool
  | .typedStudentReceipt | .controllerRecovered => true
  | .genuinelyMissing => false

def observationForcesPartialLearning : StudentObservationDisposition → Bool
  | .genuinelyMissing => true
  | .typedStudentReceipt | .controllerRecovered => false

theorem rejected_candidate_is_evidence_but_not_certification :
    candidateMaySupplyCertifiedHead .rejectedEvidence = false ∧
    candidateMaySupplyCertifiedObservation .rejectedEvidence = false := by
  decide

theorem recovered_observation_is_observed_but_not_candidate_certification :
    observationSatisfied .controllerRecovered = true ∧
    observationForcesPartialLearning .controllerRecovered = false ∧
    candidateMaySupplyCertifiedHead .rejectedEvidence = false := by
  decide

/-! Promotion review distinguishes a judgement about a candidate from a
failure of the review apparatus to produce any judgement.  In particular,
`cannotJudge` is not a fourth candidate judgement. -/
inductive CandidateJudgement
  | approve
  | reassign
  | reject
  deriving DecidableEq, Repr

inductive ReviewVerdict
  | judged (judgement : CandidateJudgement)
  | cannotJudge
  deriving DecidableEq, Repr

/-! Pattern-set equality constrains only approval.  Reassignment replaces the
set, while rejection and challenge leave the proposed attachment unchanged. -/
inductive AttachmentReviewVerdict
  | approve
  | reassign
  | reject
  | challenge
  deriving DecidableEq, Repr

/-- Faithful model of the controller's `exact-patterns?`, which compares
`(count …)` and `(set …)` rather than the sequences themselves.  It therefore
accepts a reordering, and this definition must too: modelling the check as
list equality would state a constraint stronger than the one the machine
enforces. -/
def exactPatterns (expected actual : List String) : Prop :=
  expected.length = actual.length ∧ ∀ p, p ∈ expected ↔ p ∈ actual

def AttachmentReviewVerdict.patternSetValid
    (verdict : AttachmentReviewVerdict)
    (edgePatterns reviewPatterns : List String) : Prop :=
  match verdict with
  | .approve => exactPatterns edgePatterns reviewPatterns
  | .reassign | .reject | .challenge => True

theorem approval_requires_exact_pattern_set
    (edgePatterns reviewPatterns : List String) :
    AttachmentReviewVerdict.patternSetValid .approve edgePatterns reviewPatterns ↔
      exactPatterns edgePatterns reviewPatterns := by
  rfl

/-- The order-insensitivity is deliberate, not an oversight in the model. -/
theorem exactPatterns_of_perm {expected actual : List String}
    (perm : expected.Perm actual) : exactPatterns expected actual :=
  ⟨perm.length_eq, fun _ => perm.mem_iff⟩

theorem nonapproval_does_not_require_exact_pattern_set
    (verdict : AttachmentReviewVerdict) (notApprove : verdict ≠ .approve)
    (edgePatterns reviewPatterns : List String) :
    verdict.patternSetValid edgePatterns reviewPatterns := by
  cases verdict <;> simp_all [AttachmentReviewVerdict.patternSetValid]

/-! Promotion is allowed to leave review only with materialized artifacts and
one persisted disposition for every candidate.  These types model the
controller-owned boundary: an agent may report an identifier, but only the
identifier read back with the same content digest is usable by a successor. -/

structure MaterializedArtifact where
  artifactId : String
  contentDigest : String
  persistedContentDigest : String
  readBackContentDigest : String
  persistenceReceiptId : String
  deriving DecidableEq, Repr

def MaterializedArtifact.Valid (artifact : MaterializedArtifact) : Prop :=
  artifact.artifactId ≠ "" ∧
  artifact.contentDigest ≠ "" ∧
  artifact.persistenceReceiptId ≠ "" ∧
  artifact.persistedContentDigest = artifact.contentDigest ∧
  artifact.readBackContentDigest = artifact.contentDigest

inductive PromotionDispositionKind
  | approve
  | reassign
  | reject
  deriving DecidableEq, Repr

structure PromotionDisposition where
  candidate : MaterializedArtifact
  reviewEvidence : MaterializedArtifact
  kind : PromotionDispositionKind
  edgePatterns : List String
  reviewPatterns : List String
  attachmentStatus : String
  deriving DecidableEq, Repr

def PromotionDisposition.publishing (disposition : PromotionDisposition) : Bool :=
  match disposition.kind with
  | .approve | .reassign => true
  | .reject => false

def PromotionDisposition.Valid (disposition : PromotionDisposition) : Prop :=
  disposition.candidate.Valid ∧
  disposition.reviewEvidence.Valid ∧
  disposition.reviewPatterns ≠ [] ∧
  match disposition.kind with
  | .approve =>
      exactPatterns disposition.edgePatterns disposition.reviewPatterns ∧
      disposition.attachmentStatus = "reviewed"
  | .reassign =>
      disposition.attachmentStatus = "reviewed"
  | .reject =>
      disposition.attachmentStatus = "proposed"

/-! A failed attachment projection is not a disposition about the candidate.
It is an apparatus observation which prevents construction of a completed
review pass until the persisted judgement can be projected and read back. -/

structure PromotionProjectionFailure where
  candidateId : String
  reviewEvidenceId : String
  operation : String
  finding : String
  deriving DecidableEq, Repr

def PromotionProjectionFailure.Valid
    (failure : PromotionProjectionFailure) : Prop :=
  failure.candidateId ≠ "" ∧
  failure.reviewEvidenceId ≠ "" ∧
  failure.operation ≠ "" ∧
  failure.finding ≠ ""

inductive PromotionProjectionOutcome
  | materialized (disposition : PromotionDisposition)
  | apparatusFailure (failure : PromotionProjectionFailure)
  deriving DecidableEq, Repr

def PromotionProjectionOutcome.completed
    (outcome : PromotionProjectionOutcome) : Bool :=
  match outcome with
  | .materialized _ => true
  | .apparatusFailure _ => false

theorem projection_failure_is_not_a_completed_disposition
    (failure : PromotionProjectionFailure) :
    (PromotionProjectionOutcome.apparatusFailure failure).completed = false := by
  rfl

def ProjectionBatchCompleted
    (outcomes : List PromotionProjectionOutcome) : Prop :=
  ∀ outcome ∈ outcomes, outcome.completed = true

theorem projection_failure_prevents_completed_batch
    (outcomes : List PromotionProjectionOutcome)
    (failure : PromotionProjectionFailure)
    (member : PromotionProjectionOutcome.apparatusFailure failure ∈ outcomes) :
    ¬ ProjectionBatchCompleted outcomes := by
  intro completed
  have := completed _ member
  simp [PromotionProjectionOutcome.completed] at this

structure CompletedReviewPass where
  dispatchedCandidateIds : List String
  dispositions : List PromotionDisposition
  deriving DecidableEq, Repr

def CompletedReviewPass.Valid (pass : CompletedReviewPass) : Prop :=
  pass.dispatchedCandidateIds ≠ [] ∧
  pass.dispatchedCandidateIds.Nodup ∧
  (pass.dispositions.map (fun disposition =>
      disposition.candidate.artifactId)).Perm pass.dispatchedCandidateIds ∧
  ∀ disposition ∈ pass.dispositions, disposition.Valid

theorem completed_pass_accounts_for_every_candidate
    (pass : CompletedReviewPass) (valid : pass.Valid)
    (candidateId : String) (member : candidateId ∈ pass.dispatchedCandidateIds) :
    ∃ disposition ∈ pass.dispositions,
      disposition.candidate.artifactId = candidateId := by
  rcases valid with ⟨_, _, accounted, _⟩
  have mapped : candidateId ∈ pass.dispositions.map
      (fun disposition => disposition.candidate.artifactId) :=
    accounted.mem_iff.mpr member
  simpa using mapped

theorem invalid_disposition_prevents_completed_pass
    (pass : CompletedReviewPass) (disposition : PromotionDisposition)
    (member : disposition ∈ pass.dispositions)
    (invalid : ¬ disposition.Valid) : ¬ pass.Valid := by
  intro valid
  exact invalid (valid.2.2.2 disposition member)

theorem rejected_disposition_is_nonpublishing
    (disposition : PromotionDisposition)
    (kind : disposition.kind = .reject) : disposition.publishing = false := by
  simp [PromotionDisposition.publishing, kind]

theorem approved_disposition_is_publishing
    (disposition : PromotionDisposition)
    (kind : disposition.kind = .approve) : disposition.publishing = true := by
  simp [PromotionDisposition.publishing, kind]

structure CertifiedPromotionPass where
  reviewPass : CompletedReviewPass
  snapshot : MaterializedArtifact
  publishedCandidateIds : List String
  deriving DecidableEq, Repr

def CertifiedPromotionPass.Valid (pass : CertifiedPromotionPass) : Prop :=
  pass.reviewPass.Valid ∧ pass.snapshot.Valid ∧
  pass.publishedCandidateIds.Nodup ∧
  (pass.reviewPass.dispositions.filter
      (fun disposition => disposition.publishing)).map
      (fun disposition => disposition.candidate.artifactId) =
    pass.publishedCandidateIds

theorem valid_certification_publishes_exactly_the_merit_dispositions
    (pass : CertifiedPromotionPass) (valid : pass.Valid) :
    (pass.reviewPass.dispositions.filter
        (fun disposition => disposition.publishing)).map
        (fun disposition => disposition.candidate.artifactId) =
      pass.publishedCandidateIds := by
  exact valid.2.2.2

/-! A review request is constructed only after the controller has resolved
the material that the reviewer will inspect.  `ReviewDispatch` is the raw
construction record; `ValidReviewDispatch` is the proof-carrying value that
may actually be sent.

DECLARED RESIDUAL — `hole-review-dispatch-resolution-witness-v1.edn`, open.
The resolution fields below are self-reported BOOLEANS: nothing here ties
`candidatePersisted = true` to the candidate actually being persisted.  So
`valid_dispatch_excludes_apparatus_failure` proves *if the controller says
everything resolves, the enumerated failures do not occur* — sound up to this
hole, and no further.  That is deliberately the same shape this model was
written to remove (`TN-fable-F32-model` §2: Lean verifying that Clojure
reports its own schema as satisfied), so it is named rather than left to be
found.  Intended closure: content-addressed witnesses, as
`TraceReviewSnapshot` already does by requiring `snapshotDigest =
contentDigest`; a controller then cannot assert a resolution it did not
perform.  Closes with the Clojure enforcement packet, which is where the
resolution record acquires a producer.

DECIDED, NOT YET DONE — `ReviewVerdict.cannotJudge` is to be retired.  Once
dispatch validity holds, every documented cause of it is excluded by
construction, and a reviewer holding resolved evidence can only approve,
reassign or reject.  A reviewer-runtime failure remains possible but is an
apparatus transition, not a verdict about a candidate, and belongs outside
`ReviewVerdict` (codex-10's finding on this packet, concurred). -/
structure ReviewCandidateResolution where
  candidateId : String
  candidatePersisted : Bool
  candidateFetchable : Bool
  parentPatternId : String
  parentPatternFetchable : Bool
  deriving DecidableEq, Repr

structure ReviewJobTraceResolution where
  traceId : String
  fetchable : Bool
  deriving DecidableEq, Repr

structure ReviewerInputResolution where
  baseProblemBlob : String
  baseProblemBlobFetchable : Bool
  solverFinalHead : String
  solverFinalHeadFetchable : Bool
  jobTraces : List ReviewJobTraceResolution
  deriving DecidableEq, Repr

structure ReviewDispatch where
  candidates : List ReviewCandidateResolution
  reviewerInputs : ReviewerInputResolution
  deriving DecidableEq, Repr

def ReviewCandidateResolution.resolves
    (candidate : ReviewCandidateResolution) : Prop :=
  candidate.candidateId ≠ "" ∧
  candidate.candidatePersisted = true ∧
  candidate.candidateFetchable = true ∧
  candidate.parentPatternId ≠ "" ∧
  candidate.parentPatternFetchable = true

def ReviewJobTraceResolution.resolves
    (trace : ReviewJobTraceResolution) : Prop :=
  trace.traceId ≠ "" ∧ trace.fetchable = true

def ReviewerInputResolution.resolves
    (inputs : ReviewerInputResolution) : Prop :=
  inputs.baseProblemBlob ≠ "" ∧
  inputs.baseProblemBlobFetchable = true ∧
  inputs.solverFinalHead ≠ "" ∧
  inputs.solverFinalHeadFetchable = true ∧
  ∀ trace ∈ inputs.jobTraces, trace.resolves

def ReviewDispatch.Valid (dispatch : ReviewDispatch) : Prop :=
  dispatch.candidates ≠ [] ∧
  (∀ candidate ∈ dispatch.candidates, candidate.resolves) ∧
  dispatch.reviewerInputs.resolves

/-- This is the only review-dispatch value the transition machine may send. -/
structure ValidReviewDispatch extends ReviewDispatch where
  valid : toReviewDispatch.Valid

inductive ReviewApparatusFailureCause
  | candidateNotPersisted
  | candidateNotFetchable
  | parentPatternNotFetchable
  | baseProblemBlobNotFetchable
  | solverFinalHeadNotFetchable
  | jobTraceNotFetchable
  deriving DecidableEq, Repr

def ReviewApparatusFailureCause.occurs
    (cause : ReviewApparatusFailureCause) (dispatch : ReviewDispatch) : Prop :=
  match cause with
  | .candidateNotPersisted =>
      ∃ candidate ∈ dispatch.candidates,
        candidate.candidatePersisted = false
  | .candidateNotFetchable =>
      ∃ candidate ∈ dispatch.candidates,
        candidate.candidateFetchable = false
  | .parentPatternNotFetchable =>
      ∃ candidate ∈ dispatch.candidates,
        candidate.parentPatternFetchable = false
  | .baseProblemBlobNotFetchable =>
      dispatch.reviewerInputs.baseProblemBlobFetchable = false
  | .solverFinalHeadNotFetchable =>
      dispatch.reviewerInputs.solverFinalHeadFetchable = false
  | .jobTraceNotFetchable =>
      ∃ trace ∈ dispatch.reviewerInputs.jobTraces, trace.fetchable = false

theorem dispatch_with_unresolvable_candidate_is_invalid
    (dispatch : ReviewDispatch) (candidate : ReviewCandidateResolution)
    (member : candidate ∈ dispatch.candidates)
    (unresolvable : ¬ candidate.resolves) : ¬ dispatch.Valid := by
  intro valid
  exact unresolvable (valid.2.1 candidate member)

theorem dispatch_with_unresolved_reviewer_inputs_is_invalid
    (dispatch : ReviewDispatch)
    (unresolved : ¬ dispatch.reviewerInputs.resolves) : ¬ dispatch.Valid := by
  intro valid
  exact unresolved valid.2.2

theorem valid_dispatch_excludes_apparatus_failure
    (dispatch : ValidReviewDispatch) (cause : ReviewApparatusFailureCause) :
    ¬ cause.occurs dispatch.toReviewDispatch := by
  rcases dispatch.valid with ⟨_, candidatesResolve, inputsResolve⟩
  rcases inputsResolve with ⟨_, baseFetchable, _, headFetchable, tracesResolve⟩
  cases cause with
  | candidateNotPersisted =>
      rintro ⟨candidate, member, missing⟩
      have := (candidatesResolve candidate member).2.1
      simp_all
  | candidateNotFetchable =>
      rintro ⟨candidate, member, missing⟩
      have := (candidatesResolve candidate member).2.2.1
      simp_all
  | parentPatternNotFetchable =>
      rintro ⟨candidate, member, missing⟩
      have := (candidatesResolve candidate member).2.2.2.2
      simp_all
  | baseProblemBlobNotFetchable => simp_all [ReviewApparatusFailureCause.occurs]
  | solverFinalHeadNotFetchable => simp_all [ReviewApparatusFailureCause.occurs]
  | jobTraceNotFetchable =>
      rintro ⟨trace, member, missing⟩
      have := (tracesResolve trace member).2
      simp_all

abbrev ReviewPass := List ReviewVerdict

def isJudgement : ReviewVerdict → Bool
  | .judged _ => true
  | .cannotJudge => false

/-- A promotion pass is resolved exactly when every candidate received a
candidate judgement.  The number of approvals is deliberately irrelevant. -/
def resolved (pass : ReviewPass) : Bool := pass.all isJudgement

inductive ApparatusRepairCause
  | terminalRepairExhausted
  | promotionPassUnresolved
  | promotionProjectionFailed
  deriving DecidableEq, Repr

structure AwaitingApparatusRepair where
  cause : ApparatusRepairCause
  lastValidReceipt : String
  contractBlob : String
  persistedReview : ReviewPass
  projectionFailure : Option PromotionProjectionFailure := none
  deriving DecidableEq, Repr

inductive PromotionPassSuccessor
  | advance
  | awaitingApparatusRepair (hold : AwaitingApparatusRepair)
  deriving DecidableEq, Repr

def promotionPassSuccessor (lastValidReceipt contractBlob : String)
    (pass : ReviewPass) : PromotionPassSuccessor :=
  if resolved pass then .advance
  else .awaitingApparatusRepair
    { cause := .promotionPassUnresolved
      lastValidReceipt := lastValidReceipt
      contractBlob := contractBlob
      persistedReview := pass
      projectionFailure := none }

def projectionFailureSuccessor (lastValidReceipt contractBlob : String)
    (pass : ReviewPass) (failure : PromotionProjectionFailure) :
    PromotionPassSuccessor :=
  .awaitingApparatusRepair
    { cause := .promotionProjectionFailed
      lastValidReceipt := lastValidReceipt
      contractBlob := contractBlob
      persistedReview := pass
      projectionFailure := some failure }

structure ProjectionRepair where
  persistedReview : ReviewPass
  reviewerRedispatched : Bool
  projectionReadBack : Bool
  deriving DecidableEq, Repr

structure ProjectionRepairPolicy where
  maxAttempts : Nat
  deriving DecidableEq, Repr

def ProjectionRepairPolicy.Valid (policy : ProjectionRepairPolicy) : Prop :=
  0 < policy.maxAttempts

def projectionRepairExhausted (policy : ProjectionRepairPolicy)
    (attempts : Nat) : Bool :=
  0 < policy.maxAttempts && policy.maxAttempts ≤ attempts

inductive ApparatusDecisionOwner
  | claudeSupervisor
  deriving DecidableEq, Repr

structure ApparatusRepairPark where
  cause : ApparatusRepairCause
  attempts : Nat
  maxAttempts : Nat
  decisionOwner : ApparatusDecisionOwner
  decisionBellRequired : Bool
  deriving DecidableEq, Repr

inductive ProjectionRepairExhaustionSuccessor
  | parkedFrameQueueContinues (park : ApparatusRepairPark)
  deriving DecidableEq, Repr

def projectionRepairExhaustionSuccessor (policy : ProjectionRepairPolicy)
    (attempts : Nat) : Option ProjectionRepairExhaustionSuccessor :=
  if projectionRepairExhausted policy attempts then
    some (.parkedFrameQueueContinues
      { cause := .promotionProjectionFailed
        attempts := attempts
        maxAttempts := policy.maxAttempts
        decisionOwner := .claudeSupervisor
        decisionBellRequired := true })
  else
    none

theorem projection_repair_before_bound_cannot_park
    (policy : ProjectionRepairPolicy) (attempts : Nat)
    (h : attempts < policy.maxAttempts) :
    projectionRepairExhaustionSuccessor policy attempts = none := by
  simp [projectionRepairExhaustionSuccessor, projectionRepairExhausted,
    Nat.not_le.mpr h]

theorem exhausted_projection_repair_parks_for_claude_and_continues_queue
    (policy : ProjectionRepairPolicy) (attempts : Nat)
    (valid : policy.Valid) (exhausted : policy.maxAttempts ≤ attempts) :
    projectionRepairExhaustionSuccessor policy attempts =
      some (.parkedFrameQueueContinues
        { cause := .promotionProjectionFailed
          attempts := attempts
          maxAttempts := policy.maxAttempts
          decisionOwner := .claudeSupervisor
          decisionBellRequired := true }) := by
  have nonzero : policy.maxAttempts ≠ 0 := Nat.ne_of_gt valid
  simp [projectionRepairExhaustionSuccessor, projectionRepairExhausted,
    nonzero, exhausted]

/-- On repair, verdicts already made on the merits are immutable.  Only an
apparatus-failure position may acquire a judgement. -/
def preservesJudgements : ReviewPass → ReviewPass → Bool
  | [], [] => true
  | .judged old :: olds, new :: news =>
      (new == .judged old) && preservesJudgements olds news
  | .cannotJudge :: olds, _ :: news => preservesJudgements olds news
  | _, _ => false

def validProjectionRepair (hold : AwaitingApparatusRepair)
    (repair : ProjectionRepair) : Prop :=
  hold.cause = .promotionProjectionFailed ∧
  repair.persistedReview = hold.persistedReview ∧
  repair.reviewerRedispatched = false ∧
  repair.projectionReadBack = true

theorem valid_projection_repair_preserves_persisted_judgement
    (hold : AwaitingApparatusRepair) (repair : ProjectionRepair)
    (valid : validProjectionRepair hold repair) :
    repair.persistedReview = hold.persistedReview ∧
    repair.reviewerRedispatched = false := by
  exact ⟨valid.2.1, valid.2.2.1⟩

inductive ReviewResumeMode
  | revalidatePersisted
  | appendOnlyRedispatch
  deriving DecidableEq, Repr

structure ReviewResume where
  newContractBlob : String
  successorReview : ReviewPass
  mode : ReviewResumeMode
  deriving DecidableEq, Repr

def validReviewResume (hold : AwaitingApparatusRepair)
    (resume : ReviewResume) : Prop :=
  resume.newContractBlob ≠ "" ∧
  resume.newContractBlob ≠ hold.contractBlob ∧
  preservesJudgements hold.persistedReview resume.successorReview = true

def mixedUnresolvedReview : ReviewPass :=
  [.judged .approve, .cannotJudge, .judged .reject]

def allRejectReview : ReviewPass :=
  [.judged .reject, .judged .reject, .judged .reject]

theorem unresolved_promotion_pass_does_not_advance :
    promotionPassSuccessor "last-valid-receipt" "contract-v1"
      mixedUnresolvedReview =
      .awaitingApparatusRepair
        { cause := .promotionPassUnresolved
          lastValidReceipt := "last-valid-receipt"
          contractBlob := "contract-v1"
          persistedReview := mixedUnresolvedReview
          projectionFailure := none } := by
  rfl

theorem all_reject_promotion_pass_advances :
    promotionPassSuccessor "last-valid-receipt" "contract-v1"
      allRejectReview = .advance := by
  rfl

/-! The three theorems below are the general properties.  The two example
theorems above compute on fixed literals, which shows the definitions reduce
but would still hold if `promotionPassSuccessor` ignored its argument in every
other case.  A predicate proved only against a literal the model invents is
what let the earlier guide-snapshot obligation sit inert; state the quantified
form as well. -/
theorem unresolved_pass_never_advances
    (receipt blob : String) (pass : ReviewPass) (h : resolved pass = false) :
    promotionPassSuccessor receipt blob pass =
      .awaitingApparatusRepair
        { cause := .promotionPassUnresolved
          lastValidReceipt := receipt
          contractBlob := blob
          persistedReview := pass
          projectionFailure := none } := by
  simp [promotionPassSuccessor, h]

theorem projection_failure_never_advances
    (receipt blob : String) (pass : ReviewPass)
    (failure : PromotionProjectionFailure) :
    projectionFailureSuccessor receipt blob pass failure =
      .awaitingApparatusRepair
        { cause := .promotionProjectionFailed
          lastValidReceipt := receipt
          contractBlob := blob
          persistedReview := pass
          projectionFailure := some failure } := by
  rfl

theorem resolved_pass_always_advances
    (receipt blob : String) (pass : ReviewPass) (h : resolved pass = true) :
    promotionPassSuccessor receipt blob pass = .advance := by
  simp [promotionPassSuccessor, h]

/-- Zero approvals is a legitimate result: a pass of rejections advances at any
length.  This is the property the campaign's role cards require and the one a
resolution rule could most easily break. -/
theorem rejections_only_pass_advances (receipt blob : String) (n : Nat) :
    promotionPassSuccessor receipt blob
      (List.replicate n (.judged .reject)) = .advance := by
  apply resolved_pass_always_advances
  induction n with
  | zero => rfl
  | succ k ih => simp [resolved, List.replicate, isJudgement] at ih ⊢

theorem unchanged_contract_cannot_resume_review
    (hold : AwaitingApparatusRepair) (pass : ReviewPass)
    (mode : ReviewResumeMode) :
    ¬ validReviewResume hold
      { newContractBlob := hold.contractBlob
        successorReview := pass
        mode := mode } := by
  simp [validReviewResume]

structure ControllerMemoryUse where
  receiptId : String
  snapshotId : String
  snapshotDigest : String
  accessibleIds : List String
  surfacedIds : List String
  searchReceiptIds : List String
  deriving DecidableEq, Repr

def validControllerMemoryUse (m : ControllerMemoryUse) : Prop :=
  m.receiptId ≠ "" ∧ m.snapshotId ≠ "" ∧ m.snapshotDigest ≠ "" ∧
  m.surfacedIds.all (fun id => id ∈ m.accessibleIds ∨ id ∈ m.searchReceiptIds)

structure ScribeStudentInput where
  jobId : String
  memoryUse : ControllerMemoryUse
  deriving DecidableEq, Repr

def validScribeStudentInput (input : ScribeStudentInput) : Prop :=
  input.jobId ≠ "" ∧ validControllerMemoryUse input.memoryUse

theorem controller_memory_use_makes_missing_observation_scribe_compatible
    (jobId : String) (memoryUse : ControllerMemoryUse)
    (hJob : jobId ≠ "") (hMemory : validControllerMemoryUse memoryUse) :
    validScribeStudentInput { jobId := jobId, memoryUse := memoryUse } := by
  exact ⟨hJob, hMemory⟩

/-- A Guide can extend the Student shelf only through independent review. The
next Student binds to the exact content-addressed union snapshot, never to the
Guide's conversational report or unreviewed candidates. -/
structure GuideSnapshotTransition where
  depositor : String
  reviewer : String
  priorSnapshotDigest : String
  unionSnapshotDigest : String
  nextStudentSnapshotDigest : String
  candidatePatternsNonempty : Bool
  deriving DecidableEq, Repr

def validGuideSnapshotTransition (t : GuideSnapshotTransition) : Prop :=
  t.depositor ≠ "" ∧ t.reviewer ≠ "" ∧ t.depositor ≠ t.reviewer ∧
  t.priorSnapshotDigest ≠ "" ∧ t.unionSnapshotDigest ≠ "" ∧
  t.nextStudentSnapshotDigest = t.unionSnapshotDigest ∧
  t.candidatePatternsNonempty = true

def unreviewedGuideSnapshot : GuideSnapshotTransition where
  depositor := "f27-guide"
  reviewer := "f27-guide"
  priorSnapshotDigest := "solver-snapshot"
  unionSnapshotDigest := "guide-union"
  nextStudentSnapshotDigest := "solver-snapshot"
  candidatePatternsNonempty := false

theorem unreviewed_guide_snapshot_is_refused :
    ¬ validGuideSnapshotTransition unreviewedGuideSnapshot := by
  simp [validGuideSnapshotTransition, unreviewedGuideSnapshot]

def analystWakeEligibleFrameResult (frameResult : String) : Prop :=
  frameResult = "closed" ∨ frameResult = "partial"

theorem partial_terminal_frame_wakes_analyst :
    analystWakeEligibleFrameResult "partial" := by
  simp [analystWakeEligibleFrameResult]

/-- A role job is not successful merely because Agency reached `done`: its
terminal value must carry the authority-bound typed report. -/
structure RoleTerminalOutput where
  commandOwnExit : Option Nat
  frameId : String
  problemId : String
  expectedFrameId : String
  expectedProblemId : String
  typedReport : Bool
  deriving DecidableEq, Repr

def validRoleTerminalOutput (output : RoleTerminalOutput) : Prop :=
  output.commandOwnExit = some 0 ∧ output.typedReport = true ∧
  output.frameId = output.expectedFrameId ∧
  output.problemId = output.expectedProblemId

/-- One invalid terminal may create one new, pre-announced canonical repair
job.  The rejected findings are durable input, not conversational context. -/
structure TerminalOutputRepair where
  originalJobId : String
  repairJobId : String
  attempt : Nat
  findings : List String
  repairedOutput : RoleTerminalOutput
  deriving DecidableEq, Repr

def validTerminalOutputRepair (repair : TerminalOutputRepair) : Prop :=
  repair.originalJobId ≠ "" ∧ repair.repairJobId ≠ "" ∧
  repair.repairJobId ≠ repair.originalJobId ∧ repair.attempt = 1 ∧
  repair.findings ≠ [] ∧ validRoleTerminalOutput repair.repairedOutput

def f25UntypedStudentOutput : RoleTerminalOutput where
  commandOwnExit := none
  frameId := ""
  problemId := ""
  expectedFrameId := "f25"
  expectedProblemId := "m94A02"
  typedReport := false

theorem f25_untyped_student_terminal_refused :
    ¬ validRoleTerminalOutput f25UntypedStudentOutput := by
  simp [validRoleTerminalOutput, f25UntypedStudentOutput]

/-! The deterministic boundary supersedes interpreting an LLM's conversational
terminal value.  Every live role uses the same envelope; only the observational
evidence schema varies by role and phase. -/

inductive LiveRole
  | solver | student | guide | scribe | zaiScribe | proctor
  | promotionProctor | analyst
  deriving DecidableEq, Repr

def allLiveRoles : List LiveRole :=
  [.solver, .student, .guide, .scribe, .zaiScribe, .proctor,
   .promotionProctor, .analyst]

/-! Terminal submission authority is modeled at field granularity.  Content
and semantic references may be authored by a role.  Controller accounting --
job, dispatch, snapshot, search receipt, and surfaced-result identity -- may
only be derived from persisted controller records. -/

inductive SubmissionFieldKind
  | content | semanticReference | controllerAccounting
  deriving DecidableEq, Repr

inductive SubmissionFieldSource
  | role | controller
  deriving DecidableEq, Repr

structure SubmissionFieldRule where
  name : String
  kind : SubmissionFieldKind
  source : SubmissionFieldSource
  deriving DecidableEq, Repr

def validSubmissionField (field : SubmissionFieldRule) : Bool :=
  !(field.kind = .controllerAccounting && field.source = .role)

def studentUsedIdsField : SubmissionFieldRule where
  name := "evidence.memory-use.used-ids"
  kind := .semanticReference
  source := .role

def studentSurfacedIdsField : SubmissionFieldRule where
  name := "evidence.memory-use.surfaced-ids"
  kind := .controllerAccounting
  source := .controller

def invalidRoleAuthoredSurfacedIds : SubmissionFieldRule where
  name := "evidence.memory-use.surfaced-ids"
  kind := .controllerAccounting
  source := .role

theorem student_used_ids_is_a_valid_semantic_claim :
    validSubmissionField studentUsedIdsField = true := by rfl

theorem role_authored_surfaced_ids_is_refused :
    validSubmissionField invalidRoleAuthoredSurfacedIds = false := by
  rfl

def controllerDerivedSubmissionFields : List String :=
  ["job-id", "dispatch-id", "agent-id", "frame-id", "problem-id", "phase",
   "role", "attempt-ordinal", "submission-attempt", "fresh-session-nonce",
   "memory-snapshot", "memory-cascade",
   "evidence.memory-cascade.used-via-cascade",
   "evidence.memory-use.receipt-id",
   "evidence.memory-use.snapshot-id", "evidence.memory-use.snapshot-digest",
   "evidence.memory-use.accessible-memory-ids",
   "evidence.memory-use.surfaced-ids", "evidence.memory-use.queries",
   "evidence.memory-search-receipt-ids"]

def roleAuthoredSubmissionFields : LiveRole → List String
  | .solver => ["command-own-exit", "outcome", "failure-account", "evidence"]
  | .student => ["command-own-exit", "outcome", "failure-account",
                  "evidence.memory-use.used-ids"]
  | .guide => ["command-own-exit", "outcome", "failure-account", "evidence"]
  | .scribe => ["command-own-exit", "outcome", "failure-account", "evidence"]
  | .zaiScribe =>
      ["command-own-exit", "outcome", "failure-account", "evidence"]
  | .proctor => ["command-own-exit", "outcome", "failure-account", "evidence"]
  | .promotionProctor =>
      ["command-own-exit", "outcome", "failure-account", "evidence"]
  | .analyst => ["command-own-exit", "outcome", "failure-account", "evidence"]

def phaseRequires : Phase → List String
  | .preflight => []
  | .solve => ["preflight-receipt"]
  | .verify => ["solve-receipt", "committed-proof"]
  | .promoteSolver => ["solve-receipt", "verify-receipt"]
  | .studentAttempt1 => ["preflight-receipt", "solver-memory-snapshot"]
  | .guideIntervention1 => ["student-attempt-1-receipt", "memory-use-1-receipt"]
  | .studentAttempt2 => ["guide-intervention-1-receipt", "solver-memory-snapshot"]
  | .guideIntervention2 => ["student-attempt-2-receipt", "memory-use-2-receipt"]
  | .studentAttempt3 => ["guide-intervention-2-receipt", "solver-memory-snapshot"]
  | .scribeReduce =>
      ["solve-receipt", "verify-receipt", "solver-promotion-receipt",
       "student-attempt-1-receipt", "memory-use-1-receipt",
       "student-attempt-2-receipt", "memory-use-2-receipt",
       "student-attempt-3-receipt", "memory-use-3-receipt",
       "guide-intervention-1-receipt", "guide-intervention-2-receipt"]
  | .closeFrame =>
      ["solve-receipt", "verify-receipt", "solver-promotion-receipt",
       "student-attempt-1-receipt", "memory-use-1-receipt",
       "student-attempt-2-receipt", "memory-use-2-receipt",
       "student-attempt-3-receipt", "memory-use-3-receipt",
       "guide-intervention-1-receipt", "guide-intervention-2-receipt",
       "scribe-lane-receipt", "memory-disposition-receipt",
       "promotion-review-receipt"]

def phaseProduces : Phase → List String
  | .preflight => ["preflight-receipt"]
  | .solve => ["solve-receipt", "committed-proof"]
  | .verify => ["verify-receipt"]
  | .promoteSolver => ["solver-promotion-receipt", "solver-memory-snapshot"]
  | .studentAttempt1 => ["student-attempt-1-receipt", "memory-use-1-receipt"]
  | .guideIntervention1 => ["guide-intervention-1-receipt"]
  | .studentAttempt2 => ["student-attempt-2-receipt", "memory-use-2-receipt"]
  | .guideIntervention2 => ["guide-intervention-2-receipt"]
  | .studentAttempt3 => ["student-attempt-3-receipt", "memory-use-3-receipt"]
  | .scribeReduce =>
      ["scribe-lane-receipt", "memory-disposition-receipt",
       "promotion-review-receipt"]
  | .closeFrame => ["frame-close-receipt", "frame-trace"]

def receiptRequiredFields : String → List String
  | "frame-preflight" => ["receipt/id", "receipt/type", "receipt/frame-id",
      "receipt/problem-id", "receipt/result"]
  | "frame-solve" => ["receipt/id", "receipt/type", "receipt/frame-id",
      "receipt/problem-id", "receipt/final-head", "receipt/lean"]
  | "frame-verify" => ["receipt/id", "receipt/type", "receipt/frame-id",
      "receipt/problem-id", "receipt/solve-receipt-id",
      "receipt/mathematical-sound?"]
  | "solver-promotion" => ["receipt/id", "receipt/type", "receipt/frame-id",
      "receipt/problem-id", "receipt/job-id", "receipt/input-receipt-ids", "receipt/lanes",
      "receipt/dispositions", "receipt/promotion-reviews", "receipt/snapshot-id",
      "receipt/snapshot-digest", "receipt/snapshot-path",
      "receipt/reviewed-memory-ids", "receipt/independent-review?",
      "receipt/promotion-pass-witness"]
  | "student-attempt" => ["receipt/id", "receipt/type", "receipt/frame-id",
      "receipt/problem-id", "receipt/attempt-ordinal", "receipt/fresh-session-id",
      "receipt/job-id", "receipt/outcome", "receipt/failure-account",
      "receipt/memory-use", "receipt/memory-snapshot"]
  | "student-observation-missing" =>
      ["receipt/id", "receipt/type", "receipt/frame-id", "receipt/problem-id",
       "receipt/attempt-ordinal", "receipt/job-id", "receipt/author",
       "receipt/reason", "receipt/repair-attempts", "receipt/memory-snapshot",
       "receipt/harness-observed", "receipt/memory-use"]
  | "student-observation-recovered" =>
      ["receipt/id", "receipt/type", "receipt/frame-id", "receipt/problem-id",
       "receipt/attempt-ordinal", "receipt/job-id", "receipt/author",
       "receipt/reason", "receipt/repair-attempts", "receipt/memory-snapshot",
       "receipt/harness-observed", "receipt/memory-use",
       "receipt/candidate-disposition"]
  | "guide-intervention" => ["receipt/id", "receipt/type", "receipt/frame-id",
      "receipt/problem-id", "receipt/intervention-ordinal", "receipt/mode",
      "receipt/input-attempt-id", "receipt/effect", "receipt/channel-audit"]
  | "scribe-reduce" => ["receipt/id", "receipt/type", "receipt/frame-id",
      "receipt/problem-id", "receipt/job-id", "receipt/input-receipt-ids", "receipt/lanes",
      "receipt/dispositions", "receipt/promotion-reviews",
      "receipt/promotion-pass-witness"]
  | "frame-close" => ["receipt/id", "receipt/type", "receipt/frame-id",
      "receipt/problem-id", "receipt/input-receipt-ids", "receipt/trace-id",
      "receipt/result", "receipt/learning-outcome"]
  | _ => []

def receiptTypes : List String :=
  ["frame-preflight", "frame-solve", "frame-verify", "solver-promotion",
   "student-attempt", "student-observation-missing",
   "student-observation-recovered", "guide-intervention",
   "scribe-reduce", "frame-close"]

/-! APM memory search is an explicit, recorded capability.  Snapshot binding
still records which promoted memories were proactively supplied, while open
search ranges over the independently reviewed mathematics corpus. -/

structure RoleSearchEvidence where
  role : LiveRole
  jobId : String
  query : String
  traceId : String
  corpusScope : String
  resultIds : List String
  persisted : Bool
  deriving DecidableEq, Repr

def searchCapableRole : LiveRole → Bool
  | .student | .scribe | .zaiScribe | .promotionProctor => true
  | _ => false

def validRoleSearch (evidence : RoleSearchEvidence) : Prop :=
  searchCapableRole evidence.role = true ∧
  evidence.jobId ≠ "" ∧ evidence.query ≠ "" ∧ evidence.traceId ≠ "" ∧
  evidence.corpusScope = "reviewed-mathematics" ∧ evidence.persisted = true

def f29NarratedButUnexecutedSearch : RoleSearchEvidence where
  role := .student
  jobId := "f29-student"
  query := "Gauss-Lucas"
  traceId := ""
  corpusScope := "reviewed-mathematics"
  resultIds := []
  persisted := false

theorem f29_narrated_search_is_not_execution_evidence :
    ¬ validRoleSearch f29NarratedButUnexecutedSearch := by
  simp [validRoleSearch, searchCapableRole, f29NarratedButUnexecutedSearch]

def recordedOpenStudentSearch : RoleSearchEvidence where
  role := .student
  jobId := "student-job"
  query := "cast normalization"
  traceId := "search-trace"
  corpusScope := "reviewed-mathematics"
  resultIds := ["memory-outside-proactive-snapshot"]
  persisted := true

theorem recorded_open_student_search_is_valid :
    validRoleSearch recordedOpenStudentSearch := by
  simp [validRoleSearch, searchCapableRole, recordedOpenStudentSearch]

def terminalLifecycleActions : List String := ["close-block", "close-campaign"]

theorem terminal_lifecycle_actions_nonvacuous :
    terminalLifecycleActions.length = 2 := by decide

structure WorkspaceRetirementBinding where
  recordedTerminalHead : String
  observedHead : String
  worktreeClean : Bool
  branchRetained : Bool
  deriving DecidableEq, Repr

def validWorkspaceRetirementBinding (binding : WorkspaceRetirementBinding) : Prop :=
  binding.recordedTerminalHead ≠ "" ∧
  binding.observedHead = binding.recordedTerminalHead ∧
  binding.worktreeClean = true ∧ binding.branchRetained = true

def staleBaseRetirementMutant : WorkspaceRetirementBinding where
  recordedTerminalHead := "solved-head"
  observedHead := "base-head"
  worktreeClean := true
  branchRetained := true

theorem stale_base_cannot_substitute_for_terminal_head :
    ¬ validWorkspaceRetirementBinding staleBaseRetirementMutant := by
  simp [validWorkspaceRetirementBinding, staleBaseRetirementMutant]

/-! Retirement is replayed from the persisted terminal certificate, not by
re-observing a workspace that successful retirement is supposed to remove. -/
structure FrameRetirementOrder where
  terminalValidated : Bool
  terminalPersisted : Bool
  workspaceRemoved : Bool
  replayUsesPersistedTerminal : Bool
  deriving DecidableEq, Repr

def validFrameRetirementOrder (order : FrameRetirementOrder) : Prop :=
  order.workspaceRemoved = true →
    order.terminalValidated = true ∧ order.terminalPersisted = true ∧
    order.replayUsesPersistedTerminal = true

def f34RemovalBeforeTerminalPersistence : FrameRetirementOrder where
  terminalValidated := true
  terminalPersisted := false
  workspaceRemoved := true
  replayUsesPersistedTerminal := false

theorem removal_before_terminal_persistence_is_refused :
    ¬ validFrameRetirementOrder f34RemovalBeforeTerminalPersistence := by
  simp [validFrameRetirementOrder, f34RemovalBeforeTerminalPersistence]

def persistedTerminalRetirementReplay : FrameRetirementOrder where
  terminalValidated := true
  terminalPersisted := true
  workspaceRemoved := true
  replayUsesPersistedTerminal := true

theorem persisted_terminal_authorizes_retirement_replay :
    validFrameRetirementOrder persistedTerminalRetirementReplay := by
  simp [validFrameRetirementOrder, persistedTerminalRetirementReplay]

inductive SupervisorDriveStatus where
  | awaitingTerminal
  | terminalCollected
  | certified
  deriving DecidableEq, Repr

def supervisorMayAdvance : SupervisorDriveStatus → Bool
  | .certified => true
  | _ => false

theorem terminal_collection_is_progress_but_not_certification :
    supervisorMayAdvance .terminalCollected = false := by decide

structure PreflightAuthorityObservation where
  authorityRevision : String
  authorityBlob : String
  commandOwnExit : Nat
  cleanBefore : Bool
  cleanAfter : Bool
  deriving DecidableEq, Repr

def validPreflightAuthorityObservation (x : PreflightAuthorityObservation) : Prop :=
  x.authorityRevision ≠ "" ∧ x.authorityBlob ≠ "" ∧
  x.commandOwnExit = 0 ∧ x.cleanBefore = true ∧ x.cleanAfter = true

theorem artifact_identity_is_not_an_agent_observation
    (x : PreflightAuthorityObservation)
    (h : validPreflightAuthorityObservation x) :
    x.authorityRevision ≠ "" ∧ x.authorityBlob ≠ "" := by
  exact ⟨h.1, h.2.1⟩

def validPreflightSorryBaseline
    (errors sorryWarnings blockingWarnings : Nat) : Prop :=
  errors = 0 ∧ 0 < sorryWarnings ∧ blockingWarnings = 0

theorem three_sorries_are_a_valid_nonvacuous_preflight_baseline :
    validPreflightSorryBaseline 0 3 0 := by
  unfold validPreflightSorryBaseline
  exact ⟨rfl, by omega, rfl⟩

theorem zero_sorries_are_not_an_unresolved_preflight_baseline :
    ¬ validPreflightSorryBaseline 0 0 0 := by
  norm_num [validPreflightSorryBaseline]

theorem blocking_warnings_refuse_preflight :
    ¬ validPreflightSorryBaseline 0 1 1 := by
  norm_num [validPreflightSorryBaseline]

structure SubmissionAuthority where
  jobId : String
  dispatchId : String
  frameId : String
  problemId : String
  agentId : String
  role : LiveRole
  deriving DecidableEq, Repr

structure TypedRoleSubmission where
  registeredAuthority : SubmissionAuthority
  persistedAuthority : SubmissionAuthority
  submittedJobId : String
  schemaValid : Bool
  persisted : Bool
  conversationalTerminalUsed : Bool
  deriving DecidableEq, Repr

def validTypedRoleSubmission (submission : TypedRoleSubmission) : Prop :=
  submission.registeredAuthority.jobId ≠ "" ∧
  submission.registeredAuthority.dispatchId ≠ "" ∧
  submission.registeredAuthority.frameId ≠ "" ∧
  submission.registeredAuthority.problemId ≠ "" ∧
  submission.registeredAuthority.agentId ≠ "" ∧
  submission.persistedAuthority = submission.registeredAuthority ∧
  submission.submittedJobId = submission.registeredAuthority.jobId ∧
  submission.schemaValid = true ∧ submission.persisted = true ∧
  submission.conversationalTerminalUsed = false

theorem typed_submission_prevents_authority_forgery
    (submission : TypedRoleSubmission) (h : validTypedRoleSubmission submission) :
    submission.persistedAuthority.frameId =
      submission.registeredAuthority.frameId ∧
    submission.submittedJobId = submission.registeredAuthority.jobId := by
  exact ⟨congrArg SubmissionAuthority.frameId h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem conversation_cannot_advance_a_valid_submission
    (submission : TypedRoleSubmission) (h : validTypedRoleSubmission submission) :
    submission.conversationalTerminalUsed = false := h.2.2.2.2.2.2.2.2.2

theorem every_live_role_has_one_submission_schema : allLiveRoles.length = 8 := by
  rfl

/-- Controller collection is a bounded persisted observation after the role's
terminal turn.  It is performed before repair or a missing-observation ruling;
conversation is never consulted as a fallback. -/
structure RoleCollectionBudget where
  collectionAttempts : Nat
  repairAttempts : Nat
  deriving DecidableEq, Repr

def roleCollectionBudget (_ : LiveRole) : RoleCollectionBudget where
  collectionAttempts := 1
  repairAttempts := 1

structure TerminalCollectionEvidence where
  role : LiveRole
  terminalObserved : Bool
  collectionAttempts : Nat
  repairAttempts : Nat
  submissionAvailable : Bool
  submissionCollected : Bool
  collectionPersisted : Bool
  missingObservationIssued : Bool
  deriving DecidableEq, Repr

def validTerminalCollection (e : TerminalCollectionEvidence) : Prop :=
  let budget := roleCollectionBudget e.role
  e.terminalObserved = true ∧ e.collectionPersisted = true ∧
  e.collectionAttempts ≤ budget.collectionAttempts ∧
  e.repairAttempts ≤ budget.repairAttempts ∧
  (e.submissionAvailable = true → e.submissionCollected = true) ∧
  (e.missingObservationIssued = true →
    e.role = .student ∧ e.submissionAvailable = false ∧
    e.collectionAttempts = budget.collectionAttempts ∧
    e.repairAttempts = budget.repairAttempts)

theorem available_submission_is_collected
    (e : TerminalCollectionEvidence) (h : validTerminalCollection e)
    (available : e.submissionAvailable = true) :
    e.submissionCollected = true := h.2.2.2.2.1 available

def prematureF25MissingObservation : TerminalCollectionEvidence where
  role := .student
  terminalObserved := true
  collectionAttempts := 0
  repairAttempts := 0
  submissionAvailable := false
  submissionCollected := false
  collectionPersisted := true
  missingObservationIssued := true

theorem premature_f25_missing_observation_refused :
    ¬ validTerminalCollection prematureF25MissingObservation := by
  simp [validTerminalCollection, roleCollectionBudget,
    prematureF25MissingObservation]

def nonStudentSubstitution : TerminalCollectionEvidence where
  role := .guide
  terminalObserved := true
  collectionAttempts := 1
  repairAttempts := 1
  submissionAvailable := false
  submissionCollected := false
  collectionPersisted := true
  missingObservationIssued := true

theorem non_student_missing_observation_refused :
    ¬ validTerminalCollection nonStudentSubstitution := by
  simp [validTerminalCollection, roleCollectionBudget, nonStudentSubstitution]

def uncollectedValidSubmission : TerminalCollectionEvidence where
  role := .student
  terminalObserved := true
  collectionAttempts := 1
  repairAttempts := 0
  submissionAvailable := true
  submissionCollected := false
  collectionPersisted := true
  missingObservationIssued := false

theorem available_but_uncollected_submission_refused :
    ¬ validTerminalCollection uncollectedValidSubmission := by
  simp [validTerminalCollection, roleCollectionBudget, uncollectedValidSubmission]

/-- A terminal produced before typed submissions existed may be superseded
exactly once.  This is a new job, not reinterpretation of the legacy terminal:
it preserves the frozen evidence snapshot and starts a fresh role session. -/
structure TypedSubmissionMigration where
  legacyJobId : String
  replacementJobId : String
  legacySnapshotId : String
  replacementSnapshotId : String
  freshSession : Bool
  registeredBeforeActivation : Bool
  migrationOrdinal : Nat
  deriving DecidableEq, Repr

def validTypedSubmissionMigration (migration : TypedSubmissionMigration) : Prop :=
  migration.legacyJobId ≠ "" ∧ migration.replacementJobId ≠ "" ∧
  migration.legacyJobId ≠ migration.replacementJobId ∧
  migration.legacySnapshotId ≠ "" ∧
  migration.replacementSnapshotId = migration.legacySnapshotId ∧
  migration.freshSession = true ∧
  migration.registeredBeforeActivation = true ∧
  migration.migrationOrdinal = 1

theorem typed_submission_migration_is_bounded_and_snapshot_preserving
    (migration : TypedSubmissionMigration)
    (h : validTypedSubmissionMigration migration) :
    migration.migrationOrdinal = 1 ∧
    migration.replacementSnapshotId = migration.legacySnapshotId ∧
    migration.freshSession = true := by
  exact ⟨h.2.2.2.2.2.2.2, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- Recovery from a job which was announced but never accepted for activation.
The old job is terminally cancelled before a distinct replacement authority is
registered; this recovery is independent of terminal-proof repair. -/
structure UnacceptedJobSupersession where
  oldJobId : String
  replacementJobId : String
  cancellationPersisted : Bool
  replacementRegistered : Bool
  replacementAccepted : Bool
  supersessionOrdinal : Nat
  deriving DecidableEq, Repr

def validUnacceptedJobSupersession (s : UnacceptedJobSupersession) : Prop :=
  s.oldJobId ≠ "" ∧ s.replacementJobId ≠ "" ∧
  s.oldJobId ≠ s.replacementJobId ∧
  s.cancellationPersisted = true ∧ s.replacementRegistered = true ∧
  s.replacementAccepted = true ∧ s.supersessionOrdinal = 1

theorem unaccepted_job_supersession_is_distinct_cancelled_and_bounded
    (s : UnacceptedJobSupersession) (h : validUnacceptedJobSupersession s) :
    s.oldJobId ≠ s.replacementJobId ∧ s.cancellationPersisted = true ∧
    s.supersessionOrdinal = 1 := by
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Immutable authority shared by the deterministic announce, activation,
typed-submission, and restart-reconciliation adapter boundaries. -/
structure PreannouncedJobAuthority where
  derivedJobId : String
  announcedJobId : String
  activatedJobId : String
  submittedJobId : String
  announcedRequestDigest : String
  activatedRequestDigest : String
  queuedSurvivedRestart : Bool
  conflictingReplayRejected : Bool
  deriving DecidableEq, Repr

def validPreannouncedJobAuthority (a : PreannouncedJobAuthority) : Prop :=
  a.derivedJobId ≠ "" ∧
  a.derivedJobId = a.announcedJobId ∧
  a.announcedJobId = a.activatedJobId ∧
  a.activatedJobId = a.submittedJobId ∧
  a.announcedRequestDigest ≠ "" ∧
  a.announcedRequestDigest = a.activatedRequestDigest ∧
  a.queuedSurvivedRestart = true ∧
  a.conflictingReplayRejected = true

theorem valid_preannouncement_preserves_exact_authority
    (a : PreannouncedJobAuthority) (h : validPreannouncedJobAuthority a) :
    a.derivedJobId = a.submittedJobId ∧
    a.announcedRequestDigest = a.activatedRequestDigest ∧
    a.queuedSurvivedRestart = true ∧
    a.conflictingReplayRejected = true := by
  rcases h with ⟨_, hda, haa, has, _, hd, hr, hc⟩
  exact ⟨hda.trans (haa.trans has), hd, hr, hc⟩

def conflictingPreannouncement : PreannouncedJobAuthority where
  derivedJobId := "invoke-derived"
  announcedJobId := "invoke-derived"
  activatedJobId := "invoke-derived"
  submittedJobId := "invoke-derived"
  announcedRequestDigest := "request-a"
  activatedRequestDigest := "request-b"
  queuedSurvivedRestart := true
  conflictingReplayRejected := false

theorem conflicting_preannouncement_refused :
    ¬ validPreannouncedJobAuthority conflictingPreannouncement := by
  simp [validPreannouncedJobAuthority, conflictingPreannouncement]

/-- Evidence that must exist before a Student job may be dispatched.  This is
stronger than observing a correct binding in the eventual campaign trace: it
rules out launching an unbound Student and attempting to repair the receipt
afterward. -/
structure StudentDispatchWitness where
  ordinal : Nat
  promotionReceiptId : String
  snapshotId : String
  snapshotDigest : String
  accessibleMemoryIds : List String
  deriving DecidableEq, Repr

def validStudentDispatchWitness (expectedOrdinal : Nat)
    (witness : StudentDispatchWitness) : Prop :=
  witness.ordinal = expectedOrdinal ∧
  witness.promotionReceiptId ≠ "" ∧
  witness.snapshotId ≠ "" ∧
  witness.snapshotDigest ≠ ""

def f24MissingSnapshotWitness : StudentDispatchWitness where
  ordinal := 0
  promotionReceiptId := ""
  snapshotId := ""
  snapshotDigest := ""
  accessibleMemoryIds := []

theorem f24_missing_snapshot_dispatch_refused :
    ¬ validStudentDispatchWitness 1 f24MissingSnapshotWitness := by
  simp [validStudentDispatchWitness, f24MissingSnapshotWitness]

def validStudentBindings (snapshotDigest : String)
    (attempts : List StudentBinding) : Prop :=
  attempts.map (·.ordinal) = [1, 2, 3] ∧
  (attempts.map (·.sessionId)).Nodup ∧
  ∀ attempt ∈ attempts, attempt.snapshotDigest = snapshotDigest

/-- The promotion boundary is useful only when a distinct reviewer inspects
the Student-visible base residuals, rather than merely approving provenance. -/
structure PromotionEvidence where
  scribeSeat : String
  measurementProctorSeat : String
  promotionProctorSeat : String
  baseProblemBlob : String
  problemPath : String
  solverFinalHead : String
  laneCount : Nat
  reviewReason : String
  reviewResidual : String
  deriving DecidableEq, Repr

def validPromotionEvidence (evidence : PromotionEvidence) : Prop :=
  evidence.promotionProctorSeat ≠ evidence.scribeSeat ∧
  evidence.promotionProctorSeat ≠ evidence.measurementProctorSeat ∧
  evidence.baseProblemBlob ≠ "" ∧ evidence.problemPath ≠ "" ∧
  evidence.solverFinalHead ≠ "" ∧ evidence.laneCount = 4 ∧
  evidence.reviewReason ≠ "" ∧ evidence.reviewResidual ≠ ""

def f24PromotionEvidence : PromotionEvidence where
  scribeSeat := "f24-scribe"
  measurementProctorSeat := "f24-proctor"
  promotionProctorSeat := "f24-proctor"
  baseProblemBlob := "ba00d348a51e63214064c534a6e29f1b1517e405"
  problemPath := "problems/m93A02/lean/Main.lean"
  solverFinalHead := "7d26e872f89040284c58c2f4b516f50a6a42fef2"
  laneCount := 0
  reviewReason := ""
  reviewResidual := ""

theorem f24_promotion_procedure_refused :
    ¬ validPromotionEvidence f24PromotionEvidence := by
  simp [validPromotionEvidence, f24PromotionEvidence]

/-- Promotion publication must account for every reviewed candidate. Approved
IDs are exactly the IDs attached to the Student-visible snapshot; rejected IDs
remain explicit rather than disappearing through a wire-format filter. -/
structure PromotionPublicationEvidence where
  reviewedMemoryIds : List String
  approvedMemoryIds : List String
  rejectedMemoryIds : List String
  attachedMemoryIds : List String
  deriving DecidableEq, Repr

def validPromotionPublication (evidence : PromotionPublicationEvidence) : Prop :=
  evidence.reviewedMemoryIds =
      evidence.approvedMemoryIds ++ evidence.rejectedMemoryIds ∧
  evidence.attachedMemoryIds = evidence.approvedMemoryIds ∧
  evidence.reviewedMemoryIds.Nodup

def f28DroppedSolverPromotion : PromotionPublicationEvidence where
  reviewedMemoryIds := ["e-14c2c205", "e-4b95d2fd", "e-56018477", "e-925c0ab3"]
  approvedMemoryIds := ["e-14c2c205", "e-4b95d2fd", "e-56018477", "e-925c0ab3"]
  rejectedMemoryIds := []
  attachedMemoryIds := []

theorem f28_approved_but_unattached_promotion_refused :
    ¬ validPromotionPublication f28DroppedSolverPromotion := by
  simp [validPromotionPublication, f28DroppedSolverPromotion]

def accountedSolverPromotion : PromotionPublicationEvidence where
  reviewedMemoryIds := ["memory-1", "memory-2"]
  approvedMemoryIds := ["memory-1"]
  rejectedMemoryIds := ["memory-2"]
  attachedMemoryIds := ["memory-1"]

theorem accounted_solver_promotion_accepted :
    validPromotionPublication accountedSolverPromotion := by
  simp [validPromotionPublication, accountedSolverPromotion]

structure CampaignLane where
  campaignId : String
  regulatorId : String
  problemBuffer : String
  continuationSession : String
  analystSession : String
  ledgerDigest : String
  projectionLedgerDigest : String
  deriving DecidableEq, Repr

def validCampaignIsolation (lanes : List CampaignLane) : Prop :=
  2 ≤ lanes.length ∧
  (lanes.map (·.campaignId)).Nodup ∧
  (lanes.map (·.regulatorId)).Nodup ∧
  (lanes.map (·.problemBuffer)).Nodup ∧
  (lanes.map (·.continuationSession)).Nodup ∧
  (lanes.map (·.analystSession)).Nodup ∧
  ∀ lane ∈ lanes, lane.projectionLedgerDigest = lane.ledgerDigest

inductive ProblemOutcome
  | solved
  | unsolved
  deriving DecidableEq, Repr

inductive FrameResult
  | frameClosed
  | framePartial
  | frameVoid
  deriving DecidableEq, Repr

inductive LearningOutcome
  | observed
  | partiallyObserved
  | unobserved
  | skipped
  deriving DecidableEq, Repr

def validOutcome : ProblemOutcome → FrameResult → Prop
  | .solved, .frameClosed => True
  | .solved, .framePartial => True
  | .unsolved, .framePartial => True
  | .unsolved, .frameVoid => True
  | _, _ => False

/-- Problem truth, frame completion, and learning measurement are orthogonal.
A solved proof remains bankable when the learning trailer is incomplete. -/
structure TerminalOutcome where
  problem : ProblemOutcome
  frame : FrameResult
  learning : LearningOutcome
  deriving DecidableEq, Repr

def validTerminalOutcome (o : TerminalOutcome) : Prop :=
  validOutcome o.problem o.frame ∧
  (o.frame = .frameClosed → o.learning = .observed ∨ o.learning = .skipped)

def bankableSolved (o : TerminalOutcome) : Prop :=
  validTerminalOutcome o ∧ o.problem = .solved

def successorEligible (o : TerminalOutcome) : Prop := bankableSolved o

/-- An unsolved partial frame may be retried only as the same problem from its
exact retained Solver head.  This is distinct from ordinary queue succession:
it neither banks a solved problem nor advances to the next problem. -/
def retryEligible (o : TerminalOutcome) : Prop :=
  validTerminalOutcome o ∧ o.problem = .unsolved ∧ o.frame = .framePartial

inductive ObservationAuthor
  | student
  | controller
  deriving DecidableEq, Repr

/-- A missing subjective measurement is controller evidence, never a forged
Student receipt. It may fill the observation dependency while retaining its
own distinct type and authorship. -/
structure MissingObservationReceipt where
  receiptType : String
  author : ObservationAuthor
  phase : Phase
  jobId : String
  reason : String
  repairAttempts : Nat
  contentDigest : String
  deriving DecidableEq, Repr

def validMissingObservationReceipt (r : MissingObservationReceipt) : Prop :=
  r.receiptType = "student-observation-missing" ∧
  r.author = .controller ∧
  r.jobId ≠ "" ∧ r.reason = "typed-submission-missing" ∧
  r.contentDigest ≠ ""

/-- A controller-authored recovery says that the Student completed an
observable attempt even though typed-submission collection failed.  Candidate
certification remains a separate field and may be false. -/
structure RecoveredObservationReceipt where
  receiptType : String
  author : ObservationAuthor
  phase : Phase
  jobId : String
  reason : String
  durableObservation : Bool
  candidateCertified : Bool
  contentDigest : String
  deriving DecidableEq, Repr

def validRecoveredObservationReceipt (r : RecoveredObservationReceipt) : Prop :=
  r.receiptType = "student-observation-recovered" ∧
  r.author = .controller ∧ r.jobId ≠ "" ∧
  r.reason = "typed-submission-collection-failed-but-observation-recovered" ∧
  r.durableObservation = true ∧ r.contentDigest ≠ ""

def rejectedF34Observation : RecoveredObservationReceipt where
  receiptType := "student-observation-recovered"
  author := .controller
  phase := .studentAttempt3
  jobId := "apm-role-239d06d913686c0d46d50e1fe86b9fe8c258eaaebde7cc1119fa6a33befad814"
  reason := "typed-submission-collection-failed-but-observation-recovered"
  durableObservation := true
  candidateCertified := false
  contentDigest := "f34-durable-observation"

theorem f34_observation_recovered_without_certifying_candidate :
    validRecoveredObservationReceipt rejectedF34Observation ∧
    rejectedF34Observation.candidateCertified = false := by
  simp [validRecoveredObservationReceipt, rejectedF34Observation]

def f25ReferenceOutcome : TerminalOutcome where
  problem := .solved
  frame := .framePartial
  learning := .partiallyObserved

theorem f25_reference_is_bankable_and_successor_eligible :
    bankableSolved f25ReferenceOutcome ∧ successorEligible f25ReferenceOutcome := by
  simp [bankableSolved, successorEligible, validTerminalOutcome, validOutcome,
    f25ReferenceOutcome]

def forgedStudentObservation : MissingObservationReceipt where
  receiptType := "student-attempt"
  author := .student
  phase := .studentAttempt1
  jobId := "f25-job"
  reason := "typed-submission-missing"
  repairAttempts := 1
  contentDigest := "digest"

theorem forged_student_observation_refused :
    ¬ validMissingObservationReceipt forgedStudentObservation := by
  simp [validMissingObservationReceipt, forgedStudentObservation]

def conflatedF25Outcome : TerminalOutcome where
  problem := .unsolved
  frame := .framePartial
  learning := .partiallyObserved

theorem conflated_f25_outcome_not_bankable :
    ¬ bankableSolved conflatedF25Outcome := by
  simp [bankableSolved, validTerminalOutcome, validOutcome, conflatedF25Outcome]

def f26ProgressOutcome : TerminalOutcome where
  problem := .unsolved
  frame := .framePartial
  learning := .skipped

theorem f26_progress_is_retryable_but_not_solved_or_successor_eligible :
    retryEligible f26ProgressOutcome ∧
    ¬ bankableSolved f26ProgressOutcome ∧
    ¬ successorEligible f26ProgressOutcome := by
  simp [retryEligible, bankableSolved, successorEligible, validTerminalOutcome,
    validOutcome, f26ProgressOutcome]

structure AnalystWake where
  frameId : String
  terminal : Bool
  ordinal : Nat
  seriesInputVersion : Nat
  appendOnly : Bool
  proposalType : Option String
  proposalDigest : Option String
  successorHandoff : Bool
  mutatesInFlight : Bool
  deriving DecidableEq, Repr

def validAnalystTenure (wakes : List AnalystWake) : Prop :=
  wakes.length = 2 ∧ (wakes.map (·.frameId)).Nodup ∧
  wakes.map (·.ordinal) = [1, 2] ∧
  wakes.map (·.seriesInputVersion) = [1, 2] ∧
  (∀ wake ∈ wakes, wake.terminal = true ∧ wake.appendOnly = true ∧
    wake.mutatesInFlight = false) ∧
  match wakes.getLast? with
  | some wake => wake.proposalType = some "regime-proposal" ∧
      ∃ digest, wake.proposalDigest = some digest ∧ digest ≠ "" ∧
        wake.successorHandoff = true
  | none => False

def validAdvance (state : MachineState) (receipt : Receipt) : Prop :=
  state.activeClaim = none ∧
  receipt.campaignId = state.campaignId ∧
  receipt.manifestHash = state.manifestHash ∧
  receipt.fromPhase = state.phase ∧
  nextPhase? state.phase = some receipt.toPhase

theorem verify_advances_only_to_promotion
    (state : MachineState) (receipt : Receipt)
    (hphase : state.phase = .verify)
    (hvalid : validAdvance state receipt) :
    receipt.toPhase = .promoteSolver := by
  simp [validAdvance, hphase, nextPhase?] at hvalid
  exact hvalid.2.2.2.2.symm

def f23MalformedRegistration : Registration where
  campaignId := "apm-f23-one-off-v1"
  manifestHash := "0b272803df2088dc4af604ef59265839a475fbe5d82f3cdc09913448be096ef6"
  contractId := "apm-complete-frame-cycle-v2"
  phases :=
    [.preflight, .solve, .verify,
     .studentAttempt1, .guideIntervention1,
     .studentAttempt2, .guideIntervention2,
     .studentAttempt3, .scribeReduce, .closeFrame]

theorem f23_registration_refused :
    ¬ f23MalformedRegistration.matches canonicalContract := by decide

def positiveRegistration : Registration where
  campaignId := "synthetic-qualified-cycle"
  manifestHash := "synthetic-manifest"
  contractId := canonicalContract.id
  phases := canonicalContract.phases

theorem positive_registration_accepted :
    positiveRegistration.matches canonicalContract := by decide

structure DurableCoordinatorIntent where
  coordinatorId : String
  stateDigest : String
  dispatchId : String
  jobId : String
  intentPersisted : Bool
  activationAccepted : Bool
  completionPersisted : Bool
  restartReconciledSameJob : Bool
  deriving DecidableEq, Repr

def validDurableCoordinatorIntent (intent : DurableCoordinatorIntent) : Prop :=
  intent.coordinatorId ≠ "" ∧ intent.stateDigest ≠ "" ∧
  intent.dispatchId ≠ "" ∧ intent.jobId ≠ "" ∧
  intent.intentPersisted = true ∧
  (intent.activationAccepted = true → intent.intentPersisted = true) ∧
  (intent.completionPersisted = true → intent.activationAccepted = true) ∧
  (intent.restartReconciledSameJob = true → intent.intentPersisted = true)

def activationBeforeIntentMutant : DurableCoordinatorIntent where
  coordinatorId := "jit-f26"
  stateDigest := "state-digest"
  dispatchId := "dispatch-id"
  jobId := "job-id"
  intentPersisted := false
  activationAccepted := true
  completionPersisted := false
  restartReconciledSameJob := false

theorem activation_before_persisted_intent_is_refused :
    ¬ validDurableCoordinatorIntent activationBeforeIntentMutant := by
  simp [validDurableCoordinatorIntent, activationBeforeIntentMutant]

structure CoordinatorRegistryEntry where
  coordinatorId : String
  problemId : String
  coordinatorType : String
  configPath : String
  statePath : String
  entryDigest : String
  retryCount : Nat
  retryMax : Nat
  deriving DecidableEq, Repr

def validCoordinatorRegistryEntry (entry : CoordinatorRegistryEntry) : Prop :=
  entry.coordinatorId ≠ "" ∧ entry.problemId ≠ "" ∧
  entry.coordinatorType ≠ "" ∧
  entry.configPath ≠ "" ∧ entry.statePath ≠ "" ∧
  entry.entryDigest ≠ "" ∧ entry.retryCount ≤ entry.retryMax

def directoryHeuristicRegistryMutant : CoordinatorRegistryEntry where
  coordinatorId := "jit-f26"
  problemId := "m94A03"
  coordinatorType := "jit-queue"
  configPath := ""
  statePath := "data/apm-campaigns"
  entryDigest := "digest"
  retryCount := 0
  retryMax := 2

theorem directory_heuristic_is_not_canonical_registration :
    ¬ validCoordinatorRegistryEntry directoryHeuristicRegistryMutant := by
  simp [validCoordinatorRegistryEntry, directoryHeuristicRegistryMutant]

def freshCoordinatorRetryMutant : CoordinatorRegistryEntry where
  coordinatorId := "jit-m94A03-retry-v3"
  problemId := "m94A03"
  coordinatorType := "jit-queue"
  configPath := "data/apm-campaigns/m94A03.edn"
  statePath := "data/apm-campaigns/m94A03/state.edn"
  entryDigest := "digest"
  retryCount := 3
  retryMax := 2

theorem retry_beyond_bound_is_refused :
    ¬ validCoordinatorRegistryEntry freshCoordinatorRetryMutant := by
  simp [validCoordinatorRegistryEntry, freshCoordinatorRetryMutant]

end DarkTower.APMCycleMachine
