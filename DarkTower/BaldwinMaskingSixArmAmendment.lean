/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.BaldwinMaskingSixArmPreregistration

/-!
# Dated amendment to the six-arm masking registration (2026-08-02)

The original registration incorrectly made success of the four-bit context
diagnostic a prerequisite.  None of its six locus/rule interventions consumes
that coordinate.  The diagnostic is therefore recorded as failed, while the
source map, panel, tape, intervention, aggregation and artifact gates remain
unchanged.  This is a new registration, not an edit that erases the original.

The amendment follows external review and precedes every held-out evaluation.
The original confirmation environment seeds remain unspent.
-/

namespace BaldwinMaskingSixArmAmendment

open ExperimentPreregistration ExperimentalDesign
open BaldwinMaskingSixArmPreregistration

def amendedProvenance : Flag Trace where
  name := "discovery map and exact panel are bound; failed context diagnostic recorded"
  observable :=
    { name := "revision, hash and rederived panel agree; unrelated context gate failed"
      holds := fun t =>
        t.sourceRevisionObserved = BaldwinMaskingInterventionPreregistration.discoveryRevision ∧
        t.sourceMapSha256Observed = BaldwinMaskingInterventionPreregistration.discoveryMapSha256 ∧
        t.panelSelectionRecomputed = true ∧
        t.observedPanel = BaldwinMaskingInterventionPreregistration.registeredPanel ∧
        t.sharedTapeContextPrerequisitePassed = false
      check := fun t =>
        (t.sourceRevisionObserved ==
          BaldwinMaskingInterventionPreregistration.discoveryRevision) &&
        (t.sourceMapSha256Observed ==
          BaldwinMaskingInterventionPreregistration.discoveryMapSha256) &&
        t.panelSelectionRecomputed &&
        decide (t.observedPanel = BaldwinMaskingInterventionPreregistration.registeredPanel) &&
        !t.sharedTapeContextPrerequisitePassed
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
          Bool.not_eq_true, Bool.eq_false_eq_not_eq_true, Bool.not_eq_true',
          and_assoc] using h }

def validTrace (t : Trace) : Bool :=
  amendedProvenance.observable.check t && tapeProtocol.observable.check t &&
  interventions.observable.check t && contrastsComplete.observable.check t &&
  artifacts.observable.check t && !t.deadlineExceeded

noncomputable def base : Registration Trace where
  name := "metaca-six-arm-masking-and-tape-intervention-amended-2026-08-02"
  claim := .comparative
  arms := [plasticCurrentArm, heldCurrentArm, plasticGoodArm, heldGoodArm,
    heldBadArm, heldGoodNovelTapeArm]
  flags := [amendedProvenance, tapeProtocol, interventions, contrastsComplete, artifacts]
  estimatedCost := 140
  budgetCap := 240
  teardownDeadline := some 240

def classify (t : Trace) : Outcome :=
  if !validTrace t then .invalid
  else
    let heldVsCurrent := familywiseWin t.goodHeldVsCurrentHeld.wins
      t.goodHeldVsCurrentHeld.losses
    let heldVsBad := familywiseWin t.goodHeldVsBadHeld.wins
      t.goodHeldVsBadHeld.losses
    let heldVsPlastic := familywiseWin t.goodHeldVsPlasticGood.wins
      t.goodHeldVsPlasticGood.losses
    let plasticVisible := familywiseWin t.plasticGoodVsPlasticCurrent.wins
      t.plasticGoodVsPlasticCurrent.losses
    let tapeDegrades := familywiseWin t.discoveryHeldGoodVsNovelHeldGood.wins
      t.discoveryHeldGoodVsNovelHeldGood.losses
    if tapeDegrades then .tapeDegradationDetected
    else if heldVsCurrent && heldVsBad && heldVsPlastic && !plasticVisible then
      .jointOnlyNoTapeDegradationDetected
    else if heldVsCurrent && heldVsBad && heldVsPlastic && plasticVisible then
      .visibleContentAndJointAdvantage
    else if heldVsCurrent && heldVsBad && !heldVsPlastic then .heldContentSpecific
    else if plasticVisible && !heldVsCurrent && !heldVsBad then .plasticContentOnly
    else if !heldVsCurrent && !heldVsBad && !heldVsPlastic && !plasticVisible then
      .noRegisteredMechanism
    else .mixedEvidence

def decision : DecisionRule Trace Outcome where
  name := "amended masking interpretation with context result recorded, not gating"
  classify := classify

def invalidProtocol : StopRule Trace where
  name := "map, panel, tape, intervention, aggregation or artifact gate failed"
  fires := fun t => validTrace t = false
  check := fun t => !validTrace t
  check_iff := by intro t; cases h : validTrace t <;> simp

noncomputable def experiment : ProspectiveRegistration Nat Trace Outcome where
  base := base
  replication := BaldwinMaskingSixArmPreregistration.replication
  stopRules := [invalidProtocol]
  stopRulesNonempty := by simp
  decision := decision

end BaldwinMaskingSixArmAmendment
