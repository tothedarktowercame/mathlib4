/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.APMCycleMachine
import Lean

/-!
# Executable refinement checker for Clojure campaign traces

The Clojure side emits observations, not verdicts. This checker parses that
artifact and accepts exactly a complete refinement of the Lean-owned phase
order with continuous ledger and receipt references.
-/

namespace DarkTower.APMCampaignTraceChecker

open Lean DarkTower.APMCycleMachine

structure TraceStep where
  fromPhase : String
  toPhase : String
  ledgerBefore : String
  ledgerAfter : String
  receiptId : String
  priorReceiptId : Option String
  jobId : String
  activatedJobId : String
  activationStatus : Nat
  reactivatedJobId : String
  terminalJobId : String
  commandOwnExit : Option Nat
  claimPersisted : Bool
  receiptPersisted : Bool
  resumedJobId : String
  clientTimeoutObserved : Bool
  timeoutTreatedAsSuccess : Bool
  submissionRegistered : Bool
  submissionPersisted : Bool
  submissionSchemaValid : Bool
  submissionAuthorityDerived : Bool
  conversationUsedAsReceipt : Bool
  submissionJobId : String
  deriving FromJson, Repr

structure TraceStudentBinding where
  ordinal : Nat
  sessionId : String
  snapshotDigest : String
  deriving FromJson, Repr

/-- The controller recomputes `contentDigest` from the published union body.
Equality here is the trace-level witness that a named review snapshot is
content-addressed rather than merely a nonempty identifier. -/
structure TraceReviewSnapshot where
  ordinal : Nat
  snapshotDigest : String
  contentDigest : String
  deriving FromJson, Repr

/-- Persisted review verdicts, grouped by the completed pass that produced
them.  The wire strings are decoded into the cycle model's deliberately
nested `ReviewVerdict` type below. -/
structure TraceReviewPass where
  phase : String
  ordinal : Nat
  verdicts : List String
  deriving FromJson, Repr

structure TraceCampaignLane where
  campaignId : String
  regulatorId : String
  problemBuffer : String
  continuationSession : String
  analystSession : String
  ledgerDigest : String
  projectionLedgerDigest : String
  deriving FromJson, Repr

structure TraceAnalystWake where
  frameId : String
  terminal : Bool
  ordinal : Nat
  seriesInputVersion : Nat
  appendOnly : Bool
  proposalType : Option String
  proposalDigest : Option String
  successorHandoff : Bool
  mutatesInFlight : Bool
  deriving FromJson, Repr

structure CampaignTrace where
  schemaVersion : Nat
  campaignId : String
  manifestHash : String
  contractId : String
  phaseOrder : List String
  steps : List TraceStep
  closed : Bool
  terminalLedgerDigest : String
  solverSnapshotDigest : String
  solverSnapshotContentDigest : String
  snapshotAdmittedAfterSolveVerify : Bool
  snapshotDepositor : String
  snapshotReviewer : String
  studentBindings : List TraceStudentBinding
  reviewSnapshots : List TraceReviewSnapshot
  reviewPasses : List TraceReviewPass
  campaignLanes : List TraceCampaignLane
  phaseReceiptIds : List String
  problemOutcome : String
  frameResult : String
  analystWakes : List TraceAnalystWake
  deriving FromJson, Repr

def phaseName : Phase → String
  | .preflight => "preflight"
  | .solve => "solve"
  | .verify => "verify"
  | .promoteSolver => "promote-solver"
  | .studentAttempt1 => "student-attempt-1"
  | .guideIntervention1 => "guide-intervention-1"
  | .studentAttempt2 => "student-attempt-2"
  | .guideIntervention2 => "guide-intervention-2"
  | .studentAttempt3 => "student-attempt-3"
  | .scribeReduce => "scribe-reduce"
  | .closeFrame => "close-frame"

def canonicalNames : List String := canonicalPhaseOrder.map phaseName

def expectedEdges : List (String × String) :=
  ("registered" :: canonicalNames).zip canonicalNames

def stepEdges (trace : CampaignTrace) : List (String × String) :=
  trace.steps.map fun step => (step.fromPhase, step.toPhase)

def ledgerContinuous : List TraceStep → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      first.ledgerAfter == second.ledgerBefore &&
      ledgerContinuous (second :: rest)

def receiptContinuous : List TraceStep → Bool
  | [] => true
  | first :: rest =>
      first.priorReceiptId.isNone && go first.receiptId rest
  where
    go : String → List TraceStep → Bool
      | _, [] => true
      | prior, step :: rest =>
          step.priorReceiptId == some prior && go step.receiptId rest

def terminalDigestMatches (trace : CampaignTrace) : Bool :=
  match trace.steps.getLast? with
  | none => false
  | some step => trace.terminalLedgerDigest == step.ledgerAfter

def validDispatchStep (step : TraceStep) : Bool :=
  !step.jobId.isEmpty &&
  step.activatedJobId == step.jobId &&
  step.activationStatus == 202 &&
  step.reactivatedJobId == step.jobId &&
  step.terminalJobId == step.jobId &&
  step.commandOwnExit == some 0 &&
  step.claimPersisted && step.receiptPersisted &&
  step.resumedJobId == step.jobId &&
  !step.timeoutTreatedAsSuccess &&
  step.submissionRegistered && step.submissionPersisted &&
  step.submissionSchemaValid && step.submissionAuthorityDerived &&
  !step.conversationUsedAsReceipt && step.submissionJobId == step.jobId

def dispatchLifecycleValid (steps : List TraceStep) : Bool :=
  steps.all validDispatchStep &&
  (steps.map (·.jobId)).Nodup

def validReviewSnapshot (snapshot : TraceReviewSnapshot) : Bool :=
  !snapshot.snapshotDigest.isEmpty &&
  snapshot.snapshotDigest == snapshot.contentDigest

/-- After attempt one, the later bindings and completed guide reviews are
zipped in protocol order.  A Student may keep its predecessor when a review
publishes no change, or bind the newly published union. -/
def snapshotBindingTail : String → List TraceStudentBinding →
    List TraceReviewSnapshot → Bool
  | _, [], [] => true
  | _previous, binding :: bindings, review :: reviews =>
      !binding.snapshotDigest.isEmpty && validReviewSnapshot review &&
      binding.snapshotDigest == review.snapshotDigest &&
      snapshotBindingTail binding.snapshotDigest bindings reviews
  | _, _, _ => false

def snapshotBindingChain (solverDigest : String)
    (bindings : List TraceStudentBinding)
    (reviews : List TraceReviewSnapshot) : Bool :=
  !solverDigest.isEmpty &&
  match bindings with
  | [] => false
  | first :: rest =>
      first.snapshotDigest == solverDigest &&
      snapshotBindingTail first.snapshotDigest rest reviews

def memoryValid (trace : CampaignTrace) : Bool :=
  !trace.solverSnapshotDigest.isEmpty &&
  trace.solverSnapshotDigest == trace.solverSnapshotContentDigest &&
  trace.snapshotAdmittedAfterSolveVerify &&
  !trace.snapshotDepositor.isEmpty &&
  !trace.snapshotReviewer.isEmpty &&
  trace.snapshotDepositor != trace.snapshotReviewer &&
  trace.studentBindings.map (·.ordinal) == [1, 2, 3] &&
  trace.reviewSnapshots.map (·.ordinal) == [1, 2] &&
  (trace.studentBindings.map (·.sessionId)).Nodup &&
  snapshotBindingChain trace.solverSnapshotDigest trace.studentBindings
    trace.reviewSnapshots

def decodeReviewVerdict : String → Option ReviewVerdict
  | "approve" => some (.judged .approve)
  | "reassign" => some (.judged .reassign)
  | "reject" => some (.judged .reject)
  | "cannot-judge" => some .cannotJudge
  | _ => none

def traceReviewPassResolved (pass : TraceReviewPass) : Bool :=
  match pass.verdicts.mapM decodeReviewVerdict with
  | some verdicts => resolved verdicts
  | none => false

def reviewResolutionValid (trace : CampaignTrace) : Bool :=
  !trace.reviewPasses.isEmpty && trace.reviewPasses.all traceReviewPassResolved

theorem snapshot_chain_first_attempt_binds_solver
    (solver : String) (first : TraceStudentBinding)
    (rest : List TraceStudentBinding) (reviews : List TraceReviewSnapshot)
    (h : snapshotBindingChain solver (first :: rest) reviews = true) :
    first.snapshotDigest = solver := by
  simp [snapshotBindingChain] at h
  exact h.2.1

/-- The unchanged case, stated honestly: a Student may keep its predecessor
digest exactly when the intervening review PUBLISHED that same digest, i.e.
the review added nothing.  Keeping a predecessor that the review has moved past
is not this case and is rejected below. -/
theorem unchanged_review_publication_step_is_valid
    (previous : String) (binding : TraceStudentBinding)
    (review : TraceReviewSnapshot)
    (hpub : review.snapshotDigest = previous)
    (hb : binding.snapshotDigest = previous)
    (hne : previous ≠ "") (hr : validReviewSnapshot review = true) :
    snapshotBindingTail previous [binding] [review] = true := by
  simp [snapshotBindingTail, hb, hpub, hne, hr]

/-- The frozen-snapshot defect, refused by construction.  When a review
publishes a NEW union and the Student keeps its predecessor anyway, the chain
is invalid -- this is the guide-to-Student circuit that the F27 review found
severed, and the reason a predecessor escape hatch cannot be permitted. -/
theorem stale_binding_after_moved_review_is_rejected
    (previous : String) (binding : TraceStudentBinding)
    (review : TraceReviewSnapshot)
    (hb : binding.snapshotDigest = previous)
    (hmoved : review.snapshotDigest ≠ previous) :
    snapshotBindingTail previous [binding] [review] = false := by
  simp [snapshotBindingTail, hb, Ne.symm hmoved]

theorem latest_review_snapshot_step_is_valid
    (previous : String) (binding : TraceStudentBinding)
    (review : TraceReviewSnapshot)
    (hb : binding.snapshotDigest = review.snapshotDigest)
    (hne : review.snapshotDigest ≠ "")
    (hr : validReviewSnapshot review = true) :
    snapshotBindingTail previous [binding] [review] = true := by
  simp [snapshotBindingTail, hb, hne, hr]

theorem out_of_chain_snapshot_step_is_rejected
    (previous : String) (binding : TraceStudentBinding)
    (review : TraceReviewSnapshot)
    (hr : binding.snapshotDigest ≠ review.snapshotDigest) :
    snapshotBindingTail previous [binding] [review] = false := by
  simp [snapshotBindingTail, hr]

theorem empty_solver_digest_rejects_snapshot_chain
    (bindings : List TraceStudentBinding)
    (reviews : List TraceReviewSnapshot) :
    snapshotBindingChain "" bindings reviews = false := by
  simp [snapshotBindingChain]

theorem empty_first_binding_rejects_snapshot_chain
    (solver session : String) (ordinal : Nat)
    (rest : List TraceStudentBinding) (reviews : List TraceReviewSnapshot) :
    snapshotBindingChain solver
      ({ ordinal := ordinal, sessionId := session, snapshotDigest := "" } :: rest)
      reviews = false := by
  by_cases h : solver = ""
  · simp [snapshotBindingChain, h]
  · simp [snapshotBindingChain, h]

theorem empty_later_binding_rejects_snapshot_step
    (previous session : String) (ordinal : Nat)
    (review : TraceReviewSnapshot) :
    snapshotBindingTail previous
      [{ ordinal := ordinal, sessionId := session, snapshotDigest := "" }]
      [review] = false := by
  simp [snapshotBindingTail]

theorem empty_review_digest_rejects_snapshot_step
    (previous : String) (binding : TraceStudentBinding)
    (ordinal : Nat) :
    snapshotBindingTail previous [binding]
      [{ ordinal := ordinal, snapshotDigest := "", contentDigest := "" }] =
      false := by
  simp [snapshotBindingTail, validReviewSnapshot]

theorem non_content_addressed_review_rejects_snapshot_step
    (previous : String) (binding : TraceStudentBinding)
    (ordinal : Nat) (published recomputed : String)
    (h : published ≠ recomputed) :
    snapshotBindingTail previous [binding]
      [{ ordinal := ordinal, snapshotDigest := published,
         contentDigest := recomputed }] = false := by
  simp [snapshotBindingTail, validReviewSnapshot, h]

def observedBindings (first second third : String) : List TraceStudentBinding :=
  [{ ordinal := 1, sessionId := "session-1", snapshotDigest := first },
   { ordinal := 2, sessionId := "session-2", snapshotDigest := second },
   { ordinal := 3, sessionId := "session-3", snapshotDigest := third }]

def observedReviews (first second : String) : List TraceReviewSnapshot :=
  [{ ordinal := 1, snapshotDigest := first, contentDigest := first },
   { ordinal := 2, snapshotDigest := second, contentDigest := second }]

theorem f32_observed_snapshot_chain_is_valid :
    snapshotBindingChain "597f2854"
      (observedBindings "597f2854" "4a906871" "84b46007")
      (observedReviews "4a906871" "84b46007") = true := by
  rfl

theorem f33_unchanged_guide_union_snapshot_chain_is_valid :
    snapshotBindingChain "cb974c26"
      (observedBindings "cb974c26" "cb974c26" "38647e2e")
      (observedReviews "cb974c26" "38647e2e") = true := by
  rfl

theorem f34_observed_snapshot_chain_is_valid :
    snapshotBindingChain "22872e59"
      (observedBindings "22872e59" "4b80e3cb" "7747c992")
      (observedReviews "4b80e3cb" "7747c992") = true := by
  rfl

theorem fabricated_out_of_chain_snapshot_is_rejected :
    snapshotBindingChain "solver"
      (observedBindings "solver" "unpublished" "review-2")
      (observedReviews "review-1" "review-2") = false := by
  rfl

def campaignIsolationValid (trace : CampaignTrace) : Bool :=
  2 ≤ trace.campaignLanes.length &&
  (trace.campaignLanes.map (·.campaignId)).Nodup &&
  (trace.campaignLanes.map (·.regulatorId)).Nodup &&
  (trace.campaignLanes.map (·.problemBuffer)).Nodup &&
  (trace.campaignLanes.map (·.continuationSession)).Nodup &&
  (trace.campaignLanes.map (·.analystSession)).Nodup &&
  trace.campaignLanes.all
    fun lane => lane.projectionLedgerDigest == lane.ledgerDigest

def terminalFrameValid (trace : CampaignTrace) : Bool :=
  trace.phaseReceiptIds == trace.steps.map (·.receiptId) &&
  trace.phaseReceiptIds.length == canonicalNames.length &&
  trace.phaseReceiptIds.Nodup &&
  ((trace.problemOutcome == "solved" &&
      (trace.frameResult == "closed" || trace.frameResult == "partial")) ||
   (trace.problemOutcome == "unsolved" &&
      (trace.frameResult == "partial" || trace.frameResult == "void")))

def analystValid (trace : CampaignTrace) : Bool :=
  trace.analystWakes.length == 2 &&
  (trace.analystWakes.map (·.frameId)).Nodup &&
  trace.analystWakes.map (·.ordinal) == [1, 2] &&
  trace.analystWakes.map (·.seriesInputVersion) == [1, 2] &&
  trace.analystWakes.all
    (fun wake => wake.terminal && wake.appendOnly && !wake.mutatesInFlight) &&
  match trace.analystWakes.getLast? with
  | some wake => wake.proposalType == some "regime-proposal" &&
      wake.proposalDigest.any (fun digest => !digest.isEmpty) &&
      wake.successorHandoff
  | none => false

def accepts (trace : CampaignTrace) : Bool :=
  trace.schemaVersion == 1 &&
  !trace.campaignId.isEmpty &&
  !trace.manifestHash.isEmpty &&
  trace.contractId == canonicalContract.id &&
  trace.phaseOrder == canonicalNames &&
  stepEdges trace == expectedEdges &&
  ledgerContinuous trace.steps &&
  receiptContinuous trace.steps &&
  dispatchLifecycleValid trace.steps &&
  memoryValid trace &&
  reviewResolutionValid trace &&
  campaignIsolationValid trace &&
  terminalFrameValid trace &&
  analystValid trace &&
  trace.closed && terminalDigestMatches trace

theorem acceptance_implies_canonical_order (trace : CampaignTrace)
    (h : accepts trace = true) : trace.phaseOrder = canonicalNames := by
  simp [accepts] at h
  aesop

theorem acceptance_implies_registration_identity (trace : CampaignTrace)
    (h : accepts trace = true) :
    trace.contractId = canonicalContract.id ∧
    trace.campaignId ≠ "" ∧ trace.manifestHash ≠ "" := by
  simp [accepts] at h
  aesop

theorem acceptance_implies_terminal_close (trace : CampaignTrace)
    (h : accepts trace = true) :
    trace.closed = true ∧ terminalDigestMatches trace = true := by
  simp [accepts] at h
  aesop

def checkFile (path : System.FilePath) : IO UInt32 := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse contents)
  let trace : CampaignTrace ← IO.ofExcept (fromJson? json)
  IO.println s!"APM-TRACE-BINDING-CHAIN {if memoryValid trace then "VALID" else "INVALID"}"
  IO.println s!"APM-TRACE-REVIEW-RESOLUTION {if reviewResolutionValid trace then "VALID" else "INVALID"}"
  for pass in trace.reviewPasses do
    if !traceReviewPassResolved pass then
      IO.println s!"APM-TRACE-UNRESOLVED-PASS {pass.phase} {pass.ordinal}"
  if accepts trace then
    IO.println "APM-TRACE-ACCEPTED"
    pure 0
  else
    IO.eprintln "APM-TRACE-REJECTED"
    pure 1

def run (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: APMCampaignTraceChecker TRACE.json"
      pure 2

end DarkTower.APMCampaignTraceChecker

def main (args : List String) : IO UInt32 :=
  DarkTower.APMCampaignTraceChecker.run args
