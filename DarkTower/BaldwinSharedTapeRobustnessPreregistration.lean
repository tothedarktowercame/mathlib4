/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.BaldwinSharedTapeContextPreregistration

/-!
# Amendment: robustness of the shared-tape context diagnostic

The first shared-tape diagnostic fixed one rewrite tape.  Pipeline reruns prove
determinism, not reproduction across the ablated dimension.  This prospective
robustness check repeats only that cheap arm on three new rewrite tapes.  These
are disjoint from both the first tape and the reserved evolutionary seeds.

This registration does not gate the locus/rule masking experiment: that study
does not consume the four-bit context coordinate.  It decides only whether the
single-tape context result hardens, reverses, or is heterogeneous.
-/

namespace BaldwinSharedTapeRobustnessPreregistration

open ExperimentPreregistration ExperimentalDesign

def rewriteSeeds : List Nat := [20260811, 20260812, 20260813]
def baselineStableContexts : Nat := 4
def baselineCaptureBasisPoints : Nat := 2003
def expectedContexts : Nat := 16

theorem rewriteSeeds_nodup : rewriteSeeds.Nodup := by decide
theorem rewriteSeeds_exclude_first_tape :
    BaldwinSharedTapeContextPreregistration.commonRewriteSeed ∉ rewriteSeeds := by decide

structure TapeResult where
  rewriteSeed : Nat
  contextCount : Nat
  stableContexts : Nat
  captureBasisPoints : Nat
  fixedApparatusExact : Bool
  deriving BEq, DecidableEq, Repr

structure Trace where
  sourceRevisionBound : Bool
  inputChecksumBound : Bool
  environmentSeedsObserved : List Nat
  results : List TapeResult
  artifactsComplete : Bool
  artifactsChecksummed : Bool
  deadlineExceeded : Bool
  deriving Repr

def protocol : Flag Trace where
  name := "three new rewrite tapes and the original eight environments are exact"
  observable :=
    { name := "source, input, schedules and apparatus controls are complete"
      holds := fun t =>
        t.sourceRevisionBound = true ∧ t.inputChecksumBound = true ∧
        t.environmentSeedsObserved = BaldwinSharedTapeContextPreregistration.environmentSeeds ∧
        t.results.map (·.rewriteSeed) = rewriteSeeds ∧
        t.results.all (fun r => r.contextCount = expectedContexts ∧ r.fixedApparatusExact)
      check := fun t =>
        t.sourceRevisionBound && t.inputChecksumBound &&
        decide (t.environmentSeedsObserved =
          BaldwinSharedTapeContextPreregistration.environmentSeeds) &&
        decide (t.results.map (·.rewriteSeed) = rewriteSeeds) &&
        t.results.all (fun r => r.contextCount == expectedContexts && r.fixedApparatusExact)
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          beq_iff_eq, and_assoc] using h }

def artifacts : Flag Trace where
  name := "raw profiles and checksums are banked before classification"
  observable :=
    { name := "terminal evidence is complete"
      holds := fun t => t.artifactsComplete = true ∧ t.artifactsChecksummed = true
      check := fun t => t.artifactsComplete && t.artifactsChecksummed
      check_sound := by simp }

def validTrace (t : Trace) : Bool :=
  protocol.observable.check t && artifacts.observable.check t && !t.deadlineExceeded

def noGain (r : TapeResult) : Bool :=
  r.stableContexts ≤ baselineStableContexts &&
    r.captureBasisPoints ≤ baselineCaptureBasisPoints

def gain (r : TapeResult) : Bool :=
  baselineStableContexts < r.stableContexts &&
    baselineCaptureBasisPoints < r.captureBasisPoints

def noGainCount (t : Trace) : Nat := (t.results.filter noGain).length
def gainCount (t : Trace) : Nat := (t.results.filter gain).length

noncomputable def sharedTapeReplicates : Arm where
  name := "shared-tape context profiles on three new rewrite tapes"
  neutral := false
  axes := []

noncomputable def base : Registration Trace where
  name := "metaca-shared-tape-context-robustness-amendment"
  claim := .comparative
  arms := [sharedTapeReplicates]
  flags := [protocol, artifacts]
  estimatedCost := 10
  budgetCap := 30
  teardownDeadline := some 30

def replication : ReplicationPlan Nat :=
  ReplicationPlan.seededConfirmation "first-shared-tape-diagnostic" (by decide)
    rewriteSeeds [20260821, 20260822, 20260823]
    (by simp [rewriteSeeds]) (by simp) (by simp [rewriteSeeds])

inductive Outcome
  | invalid
  | noGainReproduced
  | gainReproduced
  | tapeHeterogeneous
  deriving DecidableEq, Repr

def classify (t : Trace) : Outcome :=
  if !validTrace t then .invalid
  else if 2 ≤ noGainCount t then .noGainReproduced
  else if 2 ≤ gainCount t then .gainReproduced
  else .tapeHeterogeneous

def decision : DecisionRule Trace Outcome where
  name := "two of three rewrite tapes must agree before a directional conclusion"
  classify := classify

def invalidProtocol : StopRule Trace where
  name := "schedule, apparatus, artifact or deadline gate failed"
  fires := fun t => validTrace t = false
  check := fun t => !validTrace t
  check_iff := by intro t; cases h : validTrace t <;> simp

noncomputable def experiment : ProspectiveRegistration Nat Trace Outcome where
  base := base
  replication := replication
  stopRules := [invalidProtocol]
  stopRulesNonempty := by simp
  decision := decision

end BaldwinSharedTapeRobustnessPreregistration
