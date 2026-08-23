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

def validOutcome : ProblemOutcome → FrameResult → Prop
  | .solved, .frameClosed => True
  | .solved, .framePartial => True
  | .unsolved, .framePartial => True
  | .unsolved, .frameVoid => True
  | _, _ => False

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
