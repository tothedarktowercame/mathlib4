/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.BaldwinMechanismBatteryPreregistration
import DarkTower.ExperimentalDesign
import Mathlib.Tactic.NormNum

/-!
# Preregistration: does plastic rewriting mask useful inherited content?

The mechanism battery returned `contentFlatUsefulEndpoint`: no inherited allele
passed its 640-probe familywise response gate, while the complete held map contained
1,062 selectable, function-preserving endpoints.  This follow-up tests the causal
bridge directly.  For each preregistered locus it crosses plastic/held state with
current/mapped-good/matched-bad inherited content.

The inferential unit is the locus, not the seed/site evaluation.  Within a locus,
paired seed/site deltas vote on a direction; a strict majority produces one locus
vote and an even or empty split is a tie.  Exact one-sided sign tests then run over
the sixteen loci, Bonferroni-corrected across the four primary contrasts.

Importantly, failure of the plastic-good contrast is not treated as proof that the
two plastic arms are equal.  The corresponding outcome is named `jointOnlyDetected`,
not “masking proved”.  It records the positive joint contrasts and the absence of a
detected plastic contrast without converting a null into evidence.
-/

namespace BaldwinMaskingInterventionPreregistration

open ExperimentPreregistration ExperimentalDesign

/-! ## Discovery-bound confirmation panel -/

def discoveryRevision : String :=
  "f893a4005842ca0ceeb472020990ed131bb2de67"

def discoveryMapSha256 : String :=
  "2d883386dfb04420af393b6c11513216ab810e062f984a61d1fb818e9dbb4b63"

def panelSelectionRule : String :=
  "Within loci 0-19 and 20-39 take the four greatest positive endpoint counts; " ++
  "within loci 40-59 and 60-79 take the four least positive endpoint counts; " ++
  "break count ties by locus. At each locus choose the useful rule of greatest " ++
  "fitness (rule tie ascending), then the non-useful rule of least fitness at the " ++
  "same Hamming distance from the current rule (rule tie ascending)."

inductive Stratum
  | earlyDense
  | middleDense
  | middleSparse
  | lateSparse
  deriving BEq, DecidableEq, Repr

structure PanelEntry where
  stratum : Stratum
  locus : Nat
  currentRule : Nat
  goodRule : Nat
  badRule : Nat
  hammingDistance : Nat
  deriving BEq, DecidableEq, Repr

/-- Exact entries derived from the checksummed discovery map before any held-out run. -/
def registeredPanel : List PanelEntry :=
  [ ⟨.earlyDense, 0, 224, 52, 138, 4⟩
  , ⟨.earlyDense, 1, 41, 2, 174, 4⟩
  , ⟨.earlyDense, 2, 191, 47, 167, 2⟩
  , ⟨.earlyDense, 3, 59, 102, 65, 5⟩
  , ⟨.middleDense, 24, 168, 50, 59, 4⟩
  , ⟨.middleDense, 26, 200, 71, 123, 5⟩
  , ⟨.middleDense, 28, 69, 125, 108, 3⟩
  , ⟨.middleDense, 29, 24, 97, 100, 5⟩
  , ⟨.middleSparse, 45, 28, 146, 7, 4⟩
  , ⟨.middleSparse, 51, 64, 169, 27, 5⟩
  , ⟨.middleSparse, 52, 105, 37, 8, 3⟩
  , ⟨.middleSparse, 54, 206, 193, 4, 4⟩
  , ⟨.lateSparse, 60, 122, 97, 2, 4⟩
  , ⟨.lateSparse, 67, 197, 18, 10, 6⟩
  , ⟨.lateSparse, 75, 230, 56, 121, 6⟩
  , ⟨.lateSparse, 76, 174, 180, 30, 3⟩ ]

def expectedLoci : Nat := registeredPanel.length
def primaryContrastFamilySize : Nat := 4
def pilotEvaluationSeeds : List Nat := [901, 902, 903]
def confirmationEvaluationSeeds : List Nat := [101, 102, 103, 104, 105, 106, 107, 108]
def evaluationSites : List Nat := [0, 10, 20, 30, 40, 50, 60, 70]
def expectedRawUnitsPerArm : Nat :=
  expectedLoci * confirmationEvaluationSeeds.length * evaluationSites.length
def capacityCostBasisPoints : Nat := 500

theorem registeredPanel_has_sixteen_loci : expectedLoci = 16 := by decide

theorem registeredPanel_loci_nodup : (registeredPanel.map (·.locus)).Nodup := by decide

theorem registeredPanel_rules_are_distinct :
    registeredPanel.all (fun e => e.currentRule != e.goodRule &&
      e.goodRule != e.badRule && e.currentRule != e.badRule) = true := by decide

theorem expected_raw_units_per_arm : expectedRawUnitsPerArm = 1024 := by decide

/-! ## Trace and exact tests -/

structure Contrast where
  wins : Nat
  losses : Nat
  ties : Nat
  deriving BEq, DecidableEq, Repr

def Contrast.complete (c : Contrast) : Prop :=
  c.wins + c.losses + c.ties = expectedLoci

def Contrast.completeCheck (c : Contrast) : Bool :=
  c.wins + c.losses + c.ties == expectedLoci

theorem Contrast.complete_of_check {c : Contrast} (h : c.completeCheck = true) :
    c.complete := by
  simpa [Contrast.completeCheck, Contrast.complete] using h

/-- Upper tail of the fair-binomial null, in exact natural arithmetic. -/
def binomTail (n k : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun i => k ≤ i)).foldl
    (fun acc i => acc + Nat.choose n i) 0

/-- One-sided exact sign test with Bonferroni familywise alpha 0.05.

Ties are excluded, so `wins + losses` is the sample size.  The integer test is
`tail / 2^n ≤ 0.05 / familySize`, equivalently
`20 * familySize * tail ≤ 2^n`. -/
def familywiseWin (wins losses familySize : Nat) : Bool :=
  let n := wins + losses
  decide (0 < n) && decide (0 < familySize) && decide (losses < wins) &&
    decide (20 * familySize * binomTail n wins ≤ 2 ^ n)

theorem production_13_of_16_passes :
    familywiseWin 13 3 primaryContrastFamilySize = true := by decide

theorem production_12_of_16_fails :
    familywiseWin 12 4 primaryContrastFamilySize = false := by decide

structure Trace where
  sourceRevisionObserved : String
  sourceMapSha256Observed : String
  panelSelectionRecomputed : Bool
  observedPanel : List PanelEntry
  panelInterventionsExact : Bool
  observedEvaluationSeeds : List Nat
  observedEvaluationSites : List Nat
  discoveryUnitsExcluded : Bool
  capacityCostBasisPointsObserved : Nat
  pairedSeedSiteSchedule : Bool
  withinLocusAggregationValid : Bool
  plasticCurrentObserved : Bool
  heldCurrentObserved : Bool
  plasticGoodObserved : Bool
  heldGoodObserved : Bool
  heldBadObserved : Bool
  plasticCurrentUnits : Nat
  heldCurrentUnits : Nat
  plasticGoodUnits : Nat
  heldGoodUnits : Nat
  heldBadUnits : Nat
  positiveControlPassed : Bool
  treatmentSeparated : Bool
  /-- Mapped-good held rule versus the current held rule. -/
  goodHeldVsCurrentHeld : Contrast
  /-- Mapped-good held rule versus the distance-matched bad held rule. -/
  goodHeldVsBadHeld : Contrast
  /-- Mapped-good held rule versus the same good rule left plastic. -/
  goodHeldVsPlasticGood : Contrast
  /-- Mapped-good plastic rule versus the current plastic rule. -/
  plasticGoodVsPlasticCurrent : Contrast
  /-- Secondary descriptive contrast, not part of the four-test family. -/
  heldCurrentVsPlasticCurrent : Contrast
  artifactsComplete : Bool
  artifactsChecksummed : Bool
  deadlineExceeded : Bool
  deriving Repr

def provenance : Flag Trace where
  name := "discovery map, derivation, and confirmation panel are immutable"
  observable :=
    { name := "revision and map hash match, and the exact panel was rederived"
      holds := fun t =>
        t.sourceRevisionObserved = discoveryRevision ∧
        t.sourceMapSha256Observed = discoveryMapSha256 ∧
        t.panelSelectionRecomputed = true ∧ t.observedPanel = registeredPanel
      check := fun t =>
        (t.sourceRevisionObserved == discoveryRevision) &&
        (t.sourceMapSha256Observed == discoveryMapSha256) &&
        t.panelSelectionRecomputed && decide (t.observedPanel = registeredPanel)
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using h }

def heldOutEvaluation : Flag Trace where
  name := "discovery evaluations are excluded from confirmation"
  observable :=
    { name := "observed seeds and sites equal the preregistered held-out panel"
      holds := fun t =>
        t.observedEvaluationSeeds = confirmationEvaluationSeeds ∧
        t.observedEvaluationSites = evaluationSites ∧
        t.discoveryUnitsExcluded = true
      check := fun t =>
        decide (t.observedEvaluationSeeds = confirmationEvaluationSeeds) &&
        decide (t.observedEvaluationSites = evaluationSites) &&
        t.discoveryUnitsExcluded
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h }

def interventionProtocol : Flag Trace where
  name := "panel interventions and capacity cost equal the registration"
  observable :=
    { name := "all current/good/bad rules are exact and cost is 500 basis points"
      holds := fun t =>
        t.panelInterventionsExact = true ∧
        t.capacityCostBasisPointsObserved = capacityCostBasisPoints
      check := fun t =>
        t.panelInterventionsExact &&
        (t.capacityCostBasisPointsObserved == capacityCostBasisPoints)
      check_sound := by simp }

def pairedAggregation : Flag Trace where
  name := "paired seed/site schedules aggregate once per locus"
  observable :=
    { name := "all five contrasts contain exactly the sixteen locus units"
      holds := fun t =>
        t.pairedSeedSiteSchedule = true ∧ t.withinLocusAggregationValid = true ∧
        t.goodHeldVsCurrentHeld.complete ∧ t.goodHeldVsBadHeld.complete ∧
        t.goodHeldVsPlasticGood.complete ∧ t.plasticGoodVsPlasticCurrent.complete ∧
        t.heldCurrentVsPlasticCurrent.complete
      check := fun t =>
        t.pairedSeedSiteSchedule && t.withinLocusAggregationValid &&
        t.goodHeldVsCurrentHeld.completeCheck &&
        t.goodHeldVsBadHeld.completeCheck &&
        t.goodHeldVsPlasticGood.completeCheck &&
        t.plasticGoodVsPlasticCurrent.completeCheck &&
        t.heldCurrentVsPlasticCurrent.completeCheck
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, Contrast.completeCheck, beq_iff_eq,
          Contrast.complete, and_assoc] using h }

def allArmsExercised : Flag Trace where
  name := "all five factorial intervention arms execute"
  observable :=
    { name := "plastic-current, held-current, plastic-good, held-good and held-bad emit"
      holds := fun t =>
        t.plasticCurrentObserved = true ∧ t.heldCurrentObserved = true ∧
        t.plasticGoodObserved = true ∧ t.heldGoodObserved = true ∧
        t.heldBadObserved = true ∧
        t.plasticCurrentUnits = expectedRawUnitsPerArm ∧
        t.heldCurrentUnits = expectedRawUnitsPerArm ∧
        t.plasticGoodUnits = expectedRawUnitsPerArm ∧
        t.heldGoodUnits = expectedRawUnitsPerArm ∧
        t.heldBadUnits = expectedRawUnitsPerArm
      check := fun t =>
        t.plasticCurrentObserved && t.heldCurrentObserved &&
        t.plasticGoodObserved && t.heldGoodObserved && t.heldBadObserved &&
        (t.plasticCurrentUnits == expectedRawUnitsPerArm) &&
        (t.heldCurrentUnits == expectedRawUnitsPerArm) &&
        (t.plasticGoodUnits == expectedRawUnitsPerArm) &&
        (t.heldGoodUnits == expectedRawUnitsPerArm) &&
        (t.heldBadUnits == expectedRawUnitsPerArm)
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using h }

def completeArtifacts : Flag Trace where
  name := "raw pairs, locus votes, summaries and checksums are complete"
  observable :=
    { name := "artifact validator and checksum gate both pass"
      holds := fun t => t.artifactsComplete = true ∧ t.artifactsChecksummed = true
      check := fun t => t.artifactsComplete && t.artifactsChecksummed
      check_sound := by simp }

def validTrace (t : Trace) : Bool :=
  provenance.observable.check t && heldOutEvaluation.observable.check t &&
  interventionProtocol.observable.check t && pairedAggregation.observable.check t &&
  allArmsExercised.observable.check t && completeArtifacts.observable.check t &&
  t.positiveControlPassed && t.treatmentSeparated && !t.deadlineExceeded

/-! ## Arms and production protocol -/

noncomputable def holdAxis : Axis where
  name := "plastic versus held locus"
  levels := [0, 1]
  score := id

noncomputable def contentAxis : Axis where
  name := "current, mapped-good, or distance-matched bad inherited rule"
  levels := [0, 1, 2]
  score := id

theorem holdAxis_navigable : holdAxis.Navigable := by
  unfold Axis.Navigable Axis.gradientSteps holdAxis
  norm_num

theorem contentAxis_navigable : contentAxis.Navigable := by
  unfold Axis.Navigable Axis.gradientSteps contentAxis
  norm_num

noncomputable def plasticCurrentArm : Arm where
  name := "plastic locus with current inherited rule"
  neutral := false
  axes := []
  role := .baselineNeutral

noncomputable def heldCurrentArm : Arm where
  name := "held locus with current inherited rule"
  neutral := false
  axes := [holdAxis]

noncomputable def plasticGoodArm : Arm where
  name := "plastic locus with mapped-good inherited rule"
  neutral := false
  axes := [contentAxis]

noncomputable def heldGoodArm : Arm where
  name := "held locus with mapped-good inherited rule"
  neutral := false
  axes := [holdAxis, contentAxis]

noncomputable def heldBadArm : Arm where
  name := "held locus with distance-matched bad inherited rule"
  neutral := false
  axes := [holdAxis, contentAxis]

structure ProductionProtocol where
  panel : List PanelEntry
  evaluationSites : List Nat
  withinLocusRule : String
  capacityCost : ℝ
  positiveControl : String
  maxMinutes : Nat

noncomputable def productionProtocol : ProductionProtocol where
  panel := registeredPanel
  evaluationSites := evaluationSites
  withinLocusRule :=
    "For each contrast and locus, paired seed/site deltas vote positive, negative, " ++
    "or tie. Exclude tied deltas; a strict sign majority gives one locus vote, " ++
    "otherwise the locus is tied."
  capacityCost := 0.05
  positiveControl := "Hinton--Nowlan assimilation reaches zero plastic loci at full function"
  maxMinutes := 180

noncomputable def base : Registration Trace where
  name := "metaca-plastic-masking-factorial-intervention"
  claim := .comparative
  arms := [plasticCurrentArm, heldCurrentArm, plasticGoodArm, heldGoodArm, heldBadArm]
  flags := [provenance, heldOutEvaluation, interventionProtocol, pairedAggregation,
    allArmsExercised, completeArtifacts]
  estimatedCost := 90
  budgetCap := 180
  teardownDeadline := some 180

def replication : ReplicationPlan where
  pilotSeeds := pilotEvaluationSeeds
  confirmationSeeds := confirmationEvaluationSeeds
  pilotNonempty := by simp [pilotEvaluationSeeds]
  confirmationNonempty := by simp [confirmationEvaluationSeeds]
  disjoint := by simp [pilotEvaluationSeeds, confirmationEvaluationSeeds]

/-! ## Stopping and interpretation -/

def invalidProtocol : StopRule Trace where
  name := "provenance, held-out panel, pairing, arm, or artifact gate failed"
  fires := fun t => validTrace t = false
  check := fun t => !validTrace t
  check_iff := by intro t; cases h : validTrace t <;> simp

def failedPositiveControl : StopRule Trace where
  name := "Hinton--Nowlan positive assimilation control failed"
  fires := fun t => t.positiveControlPassed = false
  check := fun t => !t.positiveControlPassed
  check_iff := by intro t; cases t.positiveControlPassed <;> simp

def inertTreatment : StopRule Trace where
  name := "the five intervention modes were not observably distinct"
  fires := fun t => t.treatmentSeparated = false
  check := fun t => !t.treatmentSeparated
  check_iff := by intro t; cases t.treatmentSeparated <;> simp

def deadline : StopRule Trace where
  name := "independent dead-man deadline exceeded"
  fires := fun t => t.deadlineExceeded = true
  check := fun t => t.deadlineExceeded
  check_iff := by simp

inductive Outcome
  | invalid
  /-- All positive joint contrasts pass, while plastic-good is not detected.
  This is compatible with masking but does not prove equality of the plastic arms. -/
  | jointOnlyDetected
  /-- Good content is visible while plastic and gains further advantage when held. -/
  | visibleContentAndJointAdvantage
  /-- Good content beats both held controls, but holding it does not beat plastic-good. -/
  | heldContentSpecific
  /-- Content is detected while plastic, but the mapped held endpoint does not replicate. -/
  | plasticContentOnly
  /-- No primary contrast passes its familywise gate. -/
  | noRegisteredMechanism
  /-- At least one primary contrast passes without matching a named causal pattern. -/
  | mixedEvidence
  deriving DecidableEq, Repr

def classify (t : Trace) : Outcome :=
  if !validTrace t then .invalid
  else
    let heldVsCurrent := familywiseWin t.goodHeldVsCurrentHeld.wins
      t.goodHeldVsCurrentHeld.losses primaryContrastFamilySize
    let heldVsBad := familywiseWin t.goodHeldVsBadHeld.wins
      t.goodHeldVsBadHeld.losses primaryContrastFamilySize
    let heldVsPlastic := familywiseWin t.goodHeldVsPlasticGood.wins
      t.goodHeldVsPlasticGood.losses primaryContrastFamilySize
    let plasticVisible := familywiseWin t.plasticGoodVsPlasticCurrent.wins
      t.plasticGoodVsPlasticCurrent.losses primaryContrastFamilySize
    let heldSpecific := heldVsCurrent && heldVsBad
    let jointAdvantage := heldSpecific && heldVsPlastic
    if jointAdvantage && plasticVisible then .visibleContentAndJointAdvantage
    else if jointAdvantage then .jointOnlyDetected
    else if heldSpecific then .heldContentSpecific
    else if plasticVisible then .plasticContentOnly
    else if heldVsCurrent || heldVsBad || heldVsPlastic then .mixedEvidence
    else .noRegisteredMechanism

def decision : DecisionRule Trace Outcome where
  name := "separate plastic visibility, held content specificity, and joint advantage"
  classify := classify

noncomputable def experiment : ProspectiveRegistration Trace Outcome where
  base := base
  replication := replication
  stopRules := [invalidProtocol, failedPositiveControl, inertTreatment, deadline]
  stopRulesNonempty := by simp
  decision := decision

/-! The decision vocabulary is live: every constructor is reached by a complete
synthetic trace, rather than being dead prose in the registration. -/

def passingContrast : Contrast := ⟨13, 3, 0⟩
def nullContrast : Contrast := ⟨8, 8, 0⟩

def syntheticTrace (heldCurrent heldBad heldPlastic plasticVisible : Contrast) : Trace where
  sourceRevisionObserved := discoveryRevision
  sourceMapSha256Observed := discoveryMapSha256
  panelSelectionRecomputed := true
  observedPanel := registeredPanel
  panelInterventionsExact := true
  observedEvaluationSeeds := confirmationEvaluationSeeds
  observedEvaluationSites := evaluationSites
  discoveryUnitsExcluded := true
  capacityCostBasisPointsObserved := capacityCostBasisPoints
  pairedSeedSiteSchedule := true
  withinLocusAggregationValid := true
  plasticCurrentObserved := true
  heldCurrentObserved := true
  plasticGoodObserved := true
  heldGoodObserved := true
  heldBadObserved := true
  plasticCurrentUnits := expectedRawUnitsPerArm
  heldCurrentUnits := expectedRawUnitsPerArm
  plasticGoodUnits := expectedRawUnitsPerArm
  heldGoodUnits := expectedRawUnitsPerArm
  heldBadUnits := expectedRawUnitsPerArm
  positiveControlPassed := true
  treatmentSeparated := true
  goodHeldVsCurrentHeld := heldCurrent
  goodHeldVsBadHeld := heldBad
  goodHeldVsPlasticGood := heldPlastic
  plasticGoodVsPlasticCurrent := plasticVisible
  heldCurrentVsPlasticCurrent := nullContrast
  artifactsComplete := true
  artifactsChecksummed := true
  deadlineExceeded := false

theorem invalid_reachable :
    classify ({ syntheticTrace nullContrast nullContrast nullContrast nullContrast with
      artifactsComplete := false }) = .invalid := by decide

theorem jointOnlyDetected_reachable :
    classify (syntheticTrace passingContrast passingContrast passingContrast nullContrast) =
      .jointOnlyDetected := by decide

theorem visibleContentAndJointAdvantage_reachable :
    classify (syntheticTrace passingContrast passingContrast passingContrast passingContrast) =
      .visibleContentAndJointAdvantage := by decide

theorem heldContentSpecific_reachable :
    classify (syntheticTrace passingContrast passingContrast nullContrast nullContrast) =
      .heldContentSpecific := by decide

theorem plasticContentOnly_reachable :
    classify (syntheticTrace nullContrast nullContrast nullContrast passingContrast) =
      .plasticContentOnly := by decide

theorem noRegisteredMechanism_reachable :
    classify (syntheticTrace nullContrast nullContrast nullContrast nullContrast) =
      .noRegisteredMechanism := by decide

theorem mixedEvidence_reachable :
    classify (syntheticTrace passingContrast nullContrast nullContrast nullContrast) =
      .mixedEvidence := by decide

theorem joint_positive_contrasts_without_plastic_detection
    (t : Trace) (hvalid : validTrace t = true)
    (hcurrent : familywiseWin t.goodHeldVsCurrentHeld.wins
      t.goodHeldVsCurrentHeld.losses primaryContrastFamilySize = true)
    (hbad : familywiseWin t.goodHeldVsBadHeld.wins
      t.goodHeldVsBadHeld.losses primaryContrastFamilySize = true)
    (hheld : familywiseWin t.goodHeldVsPlasticGood.wins
      t.goodHeldVsPlasticGood.losses primaryContrastFamilySize = true)
    (hplastic : familywiseWin t.plasticGoodVsPlasticCurrent.wins
      t.plasticGoodVsPlasticCurrent.losses primaryContrastFamilySize = false) :
    classify t = .jointOnlyDetected := by
  simp [classify, hvalid, hcurrent, hbad, hheld, hplastic]

theorem joint_and_plastic_positive_contrasts
    (t : Trace) (hvalid : validTrace t = true)
    (hcurrent : familywiseWin t.goodHeldVsCurrentHeld.wins
      t.goodHeldVsCurrentHeld.losses primaryContrastFamilySize = true)
    (hbad : familywiseWin t.goodHeldVsBadHeld.wins
      t.goodHeldVsBadHeld.losses primaryContrastFamilySize = true)
    (hheld : familywiseWin t.goodHeldVsPlasticGood.wins
      t.goodHeldVsPlasticGood.losses primaryContrastFamilySize = true)
    (hplastic : familywiseWin t.plasticGoodVsPlasticCurrent.wins
      t.plasticGoodVsPlasticCurrent.losses primaryContrastFamilySize = true) :
    classify t = .visibleContentAndJointAdvantage := by
  simp [classify, hvalid, hcurrent, hbad, hheld, hplastic]

end BaldwinMaskingInterventionPreregistration
