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
  | solver | student | guide | scribe | proctor | promotionProctor | analyst
  deriving DecidableEq, Repr

def allLiveRoles : List LiveRole :=
  [.solver, .student, .guide, .scribe, .proctor, .promotionProctor, .analyst]

def terminalLifecycleActions : List String := ["close-block", "close-campaign"]

theorem terminal_lifecycle_actions_nonvacuous :
    terminalLifecycleActions.length = 2 := by decide

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

theorem every_live_role_has_one_submission_schema : allLiveRoles.length = 7 := by
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

end DarkTower.APMCycleMachine
