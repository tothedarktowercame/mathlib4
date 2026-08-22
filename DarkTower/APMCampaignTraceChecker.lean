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
  deriving FromJson, Repr

structure TraceStudentBinding where
  ordinal : Nat
  sessionId : String
  snapshotDigest : String
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
  snapshotAdmittedAfterSolveVerify : Bool
  snapshotDepositor : String
  snapshotReviewer : String
  studentBindings : List TraceStudentBinding
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
  !step.timeoutTreatedAsSuccess

def dispatchLifecycleValid (steps : List TraceStep) : Bool :=
  steps.all validDispatchStep &&
  (steps.map (·.jobId)).Nodup

def memoryValid (trace : CampaignTrace) : Bool :=
  !trace.solverSnapshotDigest.isEmpty &&
  trace.snapshotAdmittedAfterSolveVerify &&
  !trace.snapshotDepositor.isEmpty &&
  !trace.snapshotReviewer.isEmpty &&
  trace.snapshotDepositor != trace.snapshotReviewer &&
  trace.studentBindings.map (·.ordinal) == [1, 2, 3] &&
  (trace.studentBindings.map (·.sessionId)).Nodup &&
  trace.studentBindings.all
    fun binding => binding.snapshotDigest == trace.solverSnapshotDigest

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
