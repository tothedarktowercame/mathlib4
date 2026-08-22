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

def validStudentBindings (snapshotDigest : String)
    (attempts : List StudentBinding) : Prop :=
  attempts.map (·.ordinal) = [1, 2, 3] ∧
  (attempts.map (·.sessionId)).Nodup ∧
  ∀ attempt ∈ attempts, attempt.snapshotDigest = snapshotDigest

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
