/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.APMDemonstrationPreregistration

/-!
# Model-internal verification spike for the APM demonstration registration

This file uses fabricated data only.  It checks coherence of the Lean
specification; it says nothing about a running system or the model--artifact
bridge.
-/

namespace DarkTower.APMDemonstration.VerifySpike

open ExperimentPreregistration ExperimentalDesign
open DarkTower.APMDemonstration

noncomputable section

def problem : ProblemUnit where
  problemId := "synthetic/frame-0"
  difficultyStratum := "synthetic-stratum"
  regime := "synthetic-regime"
  lockedLemmaExposure := ["synthetic/locked-lemma"]

def probes : List CapabilityProbe :=
  [{ capability := .frameContainmentWitnessed, evidenceId := "probe/containment", recorded := true },
   { capability := .createdFrameWorked, evidenceId := "probe/frame-worked", recorded := true },
   { capability := .uniqueDisposition, evidenceId := "probe/disposition", recorded := true },
   { capability := .offerUseDisposition, evidenceId := "probe/offer-use", recorded := true },
   { capability := .needRetrieval, evidenceId := "probe/need-retrieval", recorded := true },
   { capability := .promotionImportable, evidenceId := "probe/importable", recorded := true },
   { capability := .promotionNeedTaggable, evidenceId := "probe/need-tagged", recorded := true },
   { capability := .measurementPopulated, evidenceId := "probe/measurement", recorded := true }]

def positiveTrace : Trace where
  problem := problem
  frame := { scaffoldHash := "scaffold", closingHash := "worked", changed := by decide }
  cycleClosed := true
  dispositionIds := ["disposition/closed"]
  memoryOfferIds := ["offer/one"]
  memoryDispositionOfferIds := ["offer/one"]
  stratumFrozenAt := 1
  assignedAt := 2
  comparisonRegimes := ["synthetic-regime"]
  denominatorDeclared := true
  denominatorInferredFromCorpus := false
  availableArtifactIds := ["artifact/one"]
  needProbeRetrievedIds := ["artifact/one"]
  containmentClaimed := true
  containmentProbeRecorded := true
  containmentProbePassed := true
  capabilityProbes := probes
  requiredMeasurementFields := registeredMeasurementFields
  populatedMeasurementFields := registeredMeasurementFields
  promotedArtifactIds := ["promotion/one"]
  importablePromotedArtifactIds := ["promotion/one"]
  needTaggedPromotedArtifactIds := ["promotion/one"]

def evidence : Evidence where
  toolchainExercised := true
  codeIdentityAsserted := true
  teardownExercised := true
  armsShownDistinct := false

def base : Registration Trace := round1Base 1 2 (some 3)

/-- Every registered runtime flag is genuinely satisfied by the positive trace. -/
theorem positive_flag_honoured (f : Flag Trace) (hf : f ∈ systemFlags) :
    f.honoured positiveTrace := by
  simp [systemFlags, systemDesign] at hf
  rcases hf with h | h | h | h | h | h | h | h | h | h
  all_goals subst f
  all_goals
    simp [Flag.honoured, runtimeInvariantObservable, positiveTrace,
      f2UniqueDisposition, f3OfferDispositions,
      f4StratumFrozen, f5SingleRegime, f6DeclaredDenominator,
      f7NeedRetrievable, f8WitnessedContainment, f9CapabilityProbes,
      Capability.holds, registeredCapabilities, probes,
      measurementVectorPopulated, promotionsImportable, promotionsNeedTagged,
      observable]
  all_goals decide

/-- The positive matrix row: an actual readiness witness, not merely a Boolean check. -/
def positiveReady : ReadyToRun base evidence positiveTrace where
  apparatus := by simp [Evidence.apparatusSound, evidence]
  discharged := by
    intro o ho
    cases o with
    | axisNavigable a => simp [base, round1Base, Registration.obligations,
        measurementArm] at ho
    | axisPredictedNonNavigable a => simp [base, round1Base,
        Registration.obligations, measurementArm] at ho
    | controlPresent => simp [base, round1Base, Registration.obligations,
        measurementArm] at ho
    | armsSeparable => simp [base, round1Base, Registration.obligations,
        measurementArm] at ho
    | flagHonoured f =>
        apply positive_flag_honoured f
        simpa [base, round1Base, Registration.obligations, measurementArm] using ho
    | withinBudget => norm_num [Discharged, base, round1Base]
    | teardownScheduled => simp [Discharged, base, round1Base]

theorem positive_probes_nonempty : positiveTrace.capabilityProbes ≠ [] := by decide
theorem positive_offers_nonempty : positiveTrace.memoryOfferIds ≠ [] := by decide
theorem positive_measurements_nonempty : positiveTrace.populatedMeasurementFields ≠ [] := by
  simp [positiveTrace, registeredMeasurementFields]

/-! ## Negative rows -/

def negativeF2 : Trace := { positiveTrace with dispositionIds := [] }
def negativeF3 : Trace := { positiveTrace with memoryDispositionOfferIds := [] }
def negativeF4 : Trace := { positiveTrace with stratumFrozenAt := 2, assignedAt := 1 }
def negativeF5 : Trace := { positiveTrace with comparisonRegimes := ["r1", "r2"] }
def negativeF6 : Trace := { positiveTrace with denominatorDeclared := false }
def negativeF8 : Trace := { positiveTrace with containmentProbePassed := false }
def negativeF9 : Trace := { positiveTrace with capabilityProbes := probes.tail }

theorem negative_F2_refused : IsEmpty (ReadyToRun base evidence negativeF2) :=
  no_round1_witness_of_failed_invariant 1 2 (some 3) evidence negativeF2 .F2 (by
    simp [runtimeInvariantObservable, f2UniqueDisposition, negativeF2, positiveTrace, observable])

theorem negative_F3_refused : IsEmpty (ReadyToRun base evidence negativeF3) :=
  no_round1_witness_of_failed_invariant 1 2 (some 3) evidence negativeF3 .F3 (by
    simp [runtimeInvariantObservable, f3OfferDispositions, negativeF3, positiveTrace, observable])

theorem negative_F4_refused : IsEmpty (ReadyToRun base evidence negativeF4) :=
  no_round1_witness_of_failed_invariant 1 2 (some 3) evidence negativeF4 .F4 (by
    simp [runtimeInvariantObservable, f4StratumFrozen, negativeF4, observable])

theorem negative_F5_refused : IsEmpty (ReadyToRun base evidence negativeF5) :=
  no_round1_witness_of_failed_invariant 1 2 (some 3) evidence negativeF5 .F5 (by
    change ¬ (["r1", "r2"].eraseDups.length ≤ 1)
    decide)

theorem negative_F6_refused : IsEmpty (ReadyToRun base evidence negativeF6) :=
  no_round1_witness_of_failed_invariant 1 2 (some 3) evidence negativeF6 .F6 (by
    simp [runtimeInvariantObservable, f6DeclaredDenominator, negativeF6, observable])

theorem negative_F8_refused : IsEmpty (ReadyToRun base evidence negativeF8) :=
  no_round1_witness_of_failed_invariant 1 2 (some 3) evidence negativeF8 .F8 (by
    simp [runtimeInvariantObservable, f8WitnessedContainment, negativeF8, positiveTrace, observable])

theorem negative_F9_refused : IsEmpty (ReadyToRun base evidence negativeF9) :=
  no_round1_witness_of_failed_invariant 1 2 (some 3) evidence negativeF9 .F9 (by
    simp [runtimeInvariantObservable, f9CapabilityProbes, negativeF9,
      registeredCapabilities, probes, positiveTrace, Capability.holds,
      f2UniqueDisposition, f3OfferDispositions, f7NeedRetrievable,
      f8WitnessedContainment, measurementVectorPopulated, promotionsImportable,
      promotionsNeedTagged, observable])

def allOtherRuntimeInvariantsHold (target : RuntimeInvariant) (t : Trace) : Prop :=
  ∀ i, i ≠ target → (runtimeInvariantObservable i).holds t

/-- F4, F5, F6, and F9 are clean single-violation rows. -/
theorem negative_F4_is_single : allOtherRuntimeInvariantsHold .F4 negativeF4 := by
  intro i hi
  cases i <;> simp_all [runtimeInvariantObservable, negativeF4, positiveTrace,
    f2UniqueDisposition, f3OfferDispositions, f5SingleRegime,
    f6DeclaredDenominator, f7NeedRetrievable, f8WitnessedContainment,
    f9CapabilityProbes, Capability.holds, registeredCapabilities, probes,
    measurementVectorPopulated, promotionsImportable, promotionsNeedTagged, observable]
  all_goals decide

theorem negative_F5_is_single : allOtherRuntimeInvariantsHold .F5 negativeF5 := by
  intro i hi
  cases i <;> simp_all [runtimeInvariantObservable, negativeF5, positiveTrace,
    f2UniqueDisposition, f3OfferDispositions, f4StratumFrozen,
    f6DeclaredDenominator, f7NeedRetrievable, f8WitnessedContainment,
    f9CapabilityProbes, Capability.holds, registeredCapabilities, probes,
    measurementVectorPopulated, promotionsImportable, promotionsNeedTagged, observable]

theorem negative_F6_is_single : allOtherRuntimeInvariantsHold .F6 negativeF6 := by
  intro i hi
  cases i <;> simp_all [runtimeInvariantObservable, negativeF6, positiveTrace,
    f2UniqueDisposition, f3OfferDispositions, f4StratumFrozen, f5SingleRegime,
    f7NeedRetrievable, f8WitnessedContainment, f9CapabilityProbes,
    Capability.holds, registeredCapabilities, probes, measurementVectorPopulated,
    promotionsImportable, promotionsNeedTagged, observable]
  all_goals decide

theorem negative_F9_is_single : allOtherRuntimeInvariantsHold .F9 negativeF9 := by
  intro i hi
  cases i <;> simp_all [runtimeInvariantObservable, negativeF9, positiveTrace,
    f2UniqueDisposition, f3OfferDispositions, f4StratumFrozen, f5SingleRegime,
    f6DeclaredDenominator, f8WitnessedContainment, observable]
  all_goals decide

/-! F9 intentionally subsumes concrete capabilities.  These are machine-checked
entanglement findings: F2, F3, and F8 cannot be clean single-violation rows
while F9 retains its repaired semantics. -/

theorem F2_failure_entails_F9_failure (t : Trace) (h : ¬ f2UniqueDisposition.holds t) :
    ¬ f9CapabilityProbes.holds t := by
  intro hf
  exact h ((hf .uniqueDisposition (by simp [registeredCapabilities])).1)

theorem F3_failure_entails_F9_failure (t : Trace) (h : ¬ f3OfferDispositions.holds t) :
    ¬ f9CapabilityProbes.holds t := by
  intro hf
  exact h ((hf .offerUseDisposition (by simp [registeredCapabilities])).1)

theorem F8_failure_entails_F9_failure (t : Trace) (h : ¬ f8WitnessedContainment.holds t) :
    ¬ f9CapabilityProbes.holds t := by
  intro hf
  exact h ((hf .frameContainmentWitnessed (by simp [registeredCapabilities])).1)

/-! The F1 negative is an expected elaboration failure, guarded by Lean itself. -/

/--
error: Tactic `rfl` failed: Expected the goal to be a binary relation

Hint: Reflexivity tactics can only be used on goals of the form `x ~ x` or `R x x`

⊢ "same" ≠ "same"
-/
#guard_msgs in
example : WorkedFrame where
  scaffoldHash := "same"
  closingHash := "same"
  changed := by rfl

end

end DarkTower.APMDemonstration.VerifySpike
