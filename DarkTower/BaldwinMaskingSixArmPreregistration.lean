/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.BaldwinMaskingInterventionPreregistration
import DarkTower.BaldwinSharedTapeContextPreregistration
import Mathlib.Tactic.NormNum

/-!
# Six-arm inherited-content / hold / rewrite-tape intervention

This supersedes the five-arm registration. The first five arms are evaluated on
the three rewrite tapes used to derive the endpoint map. The sixth repeats the
held-good intervention on three preregistered disjoint tapes. Environment seeds
and sites remain held out and are crossed with each tape.

The extra arm is a negative-capable overfitting test: a significant advantage
for discovery-tape held-good over novel-tape held-good detects tape degradation.
Failure to detect degradation is not called generalization. Certifying positive
generalization would require novel-tape held-current and held-bad controls too.
-/

namespace BaldwinMaskingSixArmPreregistration

open ExperimentPreregistration ExperimentalDesign
open BaldwinMaskingInterventionPreregistration

def discoveryRewriteTapes : List Nat := [1, 2, 3]
def novelRewriteTapes : List Nat := [1001, 1002, 1003]
def confirmationEnvironmentSeeds : List Nat :=
  [101, 102, 103, 104, 105, 106, 107, 108]
def primaryContrastFamilySize : Nat := 5
def expectedRawUnitsPerArm : Nat :=
  registeredPanel.length * confirmationEnvironmentSeeds.length *
    discoveryRewriteTapes.length * evaluationSites.length

theorem rewrite_tape_sets_disjoint :
    ∀ x ∈ discoveryRewriteTapes, x ∉ novelRewriteTapes := by decide

theorem expected_units_per_arm : expectedRawUnitsPerArm = 3072 := by decide

def familywiseWin (wins losses : Nat) : Bool :=
  BaldwinMaskingInterventionPreregistration.familywiseWin
    wins losses primaryContrastFamilySize

theorem production_14_of_16_passes : familywiseWin 14 2 = true := by decide
theorem production_13_of_16_fails : familywiseWin 13 3 = false := by decide

structure Trace where
  sourceRevisionObserved : String
  sourceMapSha256Observed : String
  panelSelectionRecomputed : Bool
  observedPanel : List PanelEntry
  sharedTapeContextPrerequisitePassed : Bool
  discoveryRewriteTapesObserved : List Nat
  novelRewriteTapesObserved : List Nat
  environmentSeedsObserved : List Nat
  evaluationSitesObserved : List Nat
  panelInterventionsExact : Bool
  capacityCostBasisPointsObserved : Nat
  pairedEnvironmentTapeSiteSchedule : Bool
  withinLocusAggregationValid : Bool
  armUnits : List Nat
  positiveControlPassed : Bool
  treatmentSeparated : Bool
  goodHeldVsCurrentHeld : Contrast
  goodHeldVsBadHeld : Contrast
  goodHeldVsPlasticGood : Contrast
  plasticGoodVsPlasticCurrent : Contrast
  discoveryHeldGoodVsNovelHeldGood : Contrast
  heldCurrentVsPlasticCurrent : Contrast
  artifactsComplete : Bool
  artifactsChecksummed : Bool
  deadlineExceeded : Bool
  deriving Repr

def provenance : Flag Trace where
  name := "discovery map, exact panel and context prerequisite are bound"
  observable :=
    { name := "revision, hash, rederived panel and shared-tape diagnostic agree"
      holds := fun t =>
        t.sourceRevisionObserved = discoveryRevision ∧
        t.sourceMapSha256Observed = discoveryMapSha256 ∧
        t.panelSelectionRecomputed = true ∧ t.observedPanel = registeredPanel ∧
        t.sharedTapeContextPrerequisitePassed = true
      check := fun t =>
        (t.sourceRevisionObserved == discoveryRevision) &&
        (t.sourceMapSha256Observed == discoveryMapSha256) &&
        t.panelSelectionRecomputed && decide (t.observedPanel = registeredPanel) &&
        t.sharedTapeContextPrerequisitePassed
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using h }

def tapeProtocol : Flag Trace where
  name := "discovery and novel rewrite tapes are exact and disjoint"
  observable :=
    { name := "both tape sets, environment seeds and sites equal registration"
      holds := fun t =>
        t.discoveryRewriteTapesObserved = discoveryRewriteTapes ∧
        t.novelRewriteTapesObserved = novelRewriteTapes ∧
        t.environmentSeedsObserved = confirmationEnvironmentSeeds ∧
        t.evaluationSitesObserved = evaluationSites
      check := fun t =>
        decide (t.discoveryRewriteTapesObserved = discoveryRewriteTapes) &&
        decide (t.novelRewriteTapesObserved = novelRewriteTapes) &&
        decide (t.environmentSeedsObserved = confirmationEnvironmentSeeds) &&
        decide (t.evaluationSitesObserved = evaluationSites)
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h }

def interventions : Flag Trace where
  name := "all six interventions and the registered capacity cost are exact"
  observable :=
    { name := "six arms each emit 3072 raw units with paired locus aggregation"
      holds := fun t =>
        t.panelInterventionsExact = true ∧
        t.capacityCostBasisPointsObserved = capacityCostBasisPoints ∧
        t.pairedEnvironmentTapeSiteSchedule = true ∧
        t.withinLocusAggregationValid = true ∧
        t.armUnits = List.replicate 6 expectedRawUnitsPerArm
      check := fun t =>
        t.panelInterventionsExact &&
        (t.capacityCostBasisPointsObserved == capacityCostBasisPoints) &&
        t.pairedEnvironmentTapeSiteSchedule && t.withinLocusAggregationValid &&
        decide (t.armUnits = List.replicate 6 expectedRawUnitsPerArm)
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using h }

def contrastsComplete : Flag Trace where
  name := "every contrast aggregates exactly once over sixteen loci"
  observable :=
    { name := "five primary and one descriptive contrast are complete"
      holds := fun t =>
        t.goodHeldVsCurrentHeld.complete ∧ t.goodHeldVsBadHeld.complete ∧
        t.goodHeldVsPlasticGood.complete ∧ t.plasticGoodVsPlasticCurrent.complete ∧
        t.discoveryHeldGoodVsNovelHeldGood.complete ∧
        t.heldCurrentVsPlasticCurrent.complete
      check := fun t =>
        t.goodHeldVsCurrentHeld.completeCheck && t.goodHeldVsBadHeld.completeCheck &&
        t.goodHeldVsPlasticGood.completeCheck &&
        t.plasticGoodVsPlasticCurrent.completeCheck &&
        t.discoveryHeldGoodVsNovelHeldGood.completeCheck &&
        t.heldCurrentVsPlasticCurrent.completeCheck
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, Contrast.completeCheck, Contrast.complete,
          beq_iff_eq, and_assoc] using h }

def artifacts : Flag Trace where
  name := "positive control, separation, artifacts and checksums pass"
  observable :=
    { name := "all terminal evidence is present before interpretation"
      holds := fun t =>
        t.positiveControlPassed = true ∧ t.treatmentSeparated = true ∧
        t.artifactsComplete = true ∧ t.artifactsChecksummed = true
      check := fun t =>
        t.positiveControlPassed && t.treatmentSeparated &&
        t.artifactsComplete && t.artifactsChecksummed
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, and_assoc] using h }

def validTrace (t : Trace) : Bool :=
  provenance.observable.check t && tapeProtocol.observable.check t &&
  interventions.observable.check t && contrastsComplete.observable.check t &&
  artifacts.observable.check t && !t.deadlineExceeded

noncomputable def plasticCurrentArm : Arm where
  name := "plastic-current / discovery tapes"
  neutral := false
  axes := []
  role := .baselineNeutral

noncomputable def heldCurrentArm : Arm where
  name := "held-current / discovery tapes"
  neutral := false
  axes := []

noncomputable def plasticGoodArm : Arm where
  name := "plastic-good / discovery tapes"
  neutral := false
  axes := []

noncomputable def heldGoodArm : Arm where
  name := "held-good / discovery tapes"
  neutral := false
  axes := []

noncomputable def heldBadArm : Arm where
  name := "held-bad / discovery tapes"
  neutral := false
  axes := []

noncomputable def heldGoodNovelTapeArm : Arm where
  name := "held-good / novel tapes"
  neutral := false
  axes := []

noncomputable def base : Registration Trace where
  name := "metaca-six-arm-plastic-masking-and-tape-intervention"
  claim := .comparative
  arms := [plasticCurrentArm, heldCurrentArm, plasticGoodArm, heldGoodArm,
    heldBadArm, heldGoodNovelTapeArm]
  flags := [provenance, tapeProtocol, interventions, contrastsComplete, artifacts]
  estimatedCost := 140
  budgetCap := 240
  teardownDeadline := some 240

def replication : ReplicationPlan Nat :=
  ReplicationPlan.seededConfirmation "pilot" (by decide)
    [901, 902, 903] confirmationEnvironmentSeeds (by simp)
    (by simp [confirmationEnvironmentSeeds]) (by simp [confirmationEnvironmentSeeds])

inductive Outcome
  | invalid
  | tapeDegradationDetected
  | jointOnlyNoTapeDegradationDetected
  | visibleContentAndJointAdvantage
  | heldContentSpecific
  | plasticContentOnly
  | noRegisteredMechanism
  | mixedEvidence
  deriving DecidableEq, Repr

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
  name := "separate tape degradation from inherited-content and holding effects"
  classify := classify

def invalidProtocol : StopRule Trace where
  name := "prerequisite, tape, intervention, aggregation or artifact gate failed"
  fires := fun t => validTrace t = false
  check := fun t => !validTrace t
  check_iff := by intro t; cases h : validTrace t <;> simp

noncomputable def experiment : ProspectiveRegistration Nat Trace Outcome where
  base := base
  replication := replication
  stopRules := [invalidProtocol]
  stopRulesNonempty := by simp
  decision := decision

end BaldwinMaskingSixArmPreregistration
