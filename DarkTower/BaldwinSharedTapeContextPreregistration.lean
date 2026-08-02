/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.BaldwinMechanismPreregistration
import DarkTower.ExperimentalDesign

/-!
# Preregistration: context invariance under a shared rewrite tape

The earlier context profile used a fresh rewrite tape in every evaluation.  It
therefore could not decide whether the four-bit context is a stable heritable
coordinate.  This cheap diagnostic repeats the profile with the rewrite tape
fixed, retaining the variable-tape cell as a paired comparator.

The material criterion is fixed before observing the shared-tape result: at
least four of sixteen contexts have one modal rule across all eight environment
seeds, and those stable modes capture at least 25% of all context observations.
-/

namespace BaldwinSharedTapeContextPreregistration

open ExperimentPreregistration ExperimentalDesign

def environmentSeeds : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]
def commonRewriteSeed : Nat := 20260802
def contextCount : Nat := 16
def minimumStableContexts : Nat := 4
def minimumCaptureBasisPoints : Nat := 2500

structure Trace where
  sourceRevisionBound : Bool
  inputChecksumBound : Bool
  environmentSeedsObserved : List Nat
  commonRewriteSeedObserved : Nat
  variableTapeContextsObserved : Nat
  sharedTapeContextsObserved : Nat
  variableTapeStableContexts : Nat
  sharedTapeStableContexts : Nat
  variableTapeCaptureBasisPoints : Nat
  sharedTapeCaptureBasisPoints : Nat
  fixedP0SharedTapeExact : Bool
  artifactsComplete : Bool
  artifactsChecksummed : Bool
  deadlineExceeded : Bool
  deriving Repr

def protocol : Flag Trace where
  name := "source, seeds, tape and context alphabet are exact"
  observable :=
    { name := "the registered eight environments and common tape were observed"
      holds := fun t =>
        t.sourceRevisionBound = true ∧ t.inputChecksumBound = true ∧
        t.environmentSeedsObserved = environmentSeeds ∧
        t.commonRewriteSeedObserved = commonRewriteSeed ∧
        t.variableTapeContextsObserved = contextCount ∧
        t.sharedTapeContextsObserved = contextCount
      check := fun t =>
        t.sourceRevisionBound && t.inputChecksumBound &&
        decide (t.environmentSeedsObserved = environmentSeeds) &&
        (t.commonRewriteSeedObserved == commonRewriteSeed) &&
        (t.variableTapeContextsObserved == contextCount) &&
        (t.sharedTapeContextsObserved == contextCount)
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using h }

def apparatus : Flag Trace where
  name := "fully fixed apparatus control remains exact"
  observable :=
    { name := "fixed p0 plus shared tape reproduces exactly"
      holds := fun t => t.fixedP0SharedTapeExact = true
      check := fun t => t.fixedP0SharedTapeExact
      check_sound := by simp }

def complete : Flag Trace where
  name := "raw profiles, summaries and checksums are complete"
  observable :=
    { name := "artifact and checksum gates pass before interpretation"
      holds := fun t => t.artifactsComplete = true ∧ t.artifactsChecksummed = true
      check := fun t => t.artifactsComplete && t.artifactsChecksummed
      check_sound := by simp }

def validTrace (t : Trace) : Bool :=
  protocol.observable.check t && apparatus.observable.check t &&
  complete.observable.check t && !t.deadlineExceeded

noncomputable def variableTapeArm : Arm where
  name := "variable p0 / variable rewrite tape context profile"
  neutral := false
  axes := []
  role := .baselineNeutral

noncomputable def sharedTapeArm : Arm where
  name := "variable p0 / shared rewrite tape context profile"
  neutral := false
  axes := []

noncomputable def fixedApparatusArm : Arm where
  name := "fixed p0 / shared rewrite tape exact apparatus control"
  neutral := true
  axes := []
  role := .positiveControl

noncomputable def base : Registration Trace where
  name := "metaca-shared-tape-context-invariance"
  claim := .comparative
  arms := [variableTapeArm, sharedTapeArm, fixedApparatusArm]
  flags := [protocol, apparatus, complete]
  estimatedCost := 10
  budgetCap := 30
  teardownDeadline := some 30

def replication : ReplicationPlan where
  pilotSeeds := environmentSeeds
  confirmationSeeds := [101, 102, 103, 104, 105, 106, 107, 108]
  pilotNonempty := by simp [environmentSeeds]
  confirmationNonempty := by simp
  disjoint := by simp [environmentSeeds]

inductive Outcome
  | invalid
  | materiallyContextInvariant
  | sharedTapeImprovesButSubmaterial
  | noSharedTapeContextGain
  deriving DecidableEq, Repr

def classify (t : Trace) : Outcome :=
  if !validTrace t then .invalid
  else if minimumStableContexts ≤ t.sharedTapeStableContexts &&
      minimumCaptureBasisPoints ≤ t.sharedTapeCaptureBasisPoints then
    .materiallyContextInvariant
  else if t.variableTapeStableContexts < t.sharedTapeStableContexts &&
      t.variableTapeCaptureBasisPoints < t.sharedTapeCaptureBasisPoints then
    .sharedTapeImprovesButSubmaterial
  else .noSharedTapeContextGain

def decision : DecisionRule Trace Outcome where
  name := "shared tape must improve context invariance and meet a material gate"
  classify := classify

def invalidProtocol : StopRule Trace where
  name := "protocol, apparatus, artifact or deadline gate failed"
  fires := fun t => validTrace t = false
  check := fun t => !validTrace t
  check_iff := by intro t; cases h : validTrace t <;> simp

noncomputable def experiment : ProspectiveRegistration Trace Outcome where
  base := base
  replication := replication
  stopRules := [invalidProtocol]
  stopRulesNonempty := by simp
  decision := decision

def validExample : Trace where
  sourceRevisionBound := true
  inputChecksumBound := true
  environmentSeedsObserved := environmentSeeds
  commonRewriteSeedObserved := commonRewriteSeed
  variableTapeContextsObserved := contextCount
  sharedTapeContextsObserved := contextCount
  variableTapeStableContexts := 4
  sharedTapeStableContexts := 8
  variableTapeCaptureBasisPoints := 1400
  sharedTapeCaptureBasisPoints := 3000
  fixedP0SharedTapeExact := true
  artifactsComplete := true
  artifactsChecksummed := true
  deadlineExceeded := false

theorem material_outcome_reachable :
    classify validExample = .materiallyContextInvariant := by decide

theorem invalid_outcome_reachable :
    classify { validExample with artifactsComplete := false } = .invalid := by decide

end BaldwinSharedTapeContextPreregistration
