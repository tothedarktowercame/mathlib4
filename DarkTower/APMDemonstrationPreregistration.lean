/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.ExperimentalDesign

/-!
# APM demonstration: one-shot measurement registration

This is the first formal pass over the consolidated DERIVE candidate in
`M-apm-demonstration.md`.  It deliberately does not instantiate policy which the
candidate leaves open: the round-one problem, variation endpoint, budget, teardown,
stop rule, and total interpretation remain explicit arguments.

There is one measurement arm and no within-problem contrast.  Learning is a claim
about a later series, not about this registration.
-/

namespace DarkTower.APMDemonstration

open ExperimentPreregistration

/-! ## Modules and their known invariant obligations -/

inductive Module
  | registration
  | frame
  | solver
  | adjudicator
  | memory
  | promotion
  | measurement
  deriving DecidableEq, Repr

inductive Invariant
  | F1 | F2 | F3 | F4 | F5 | F6 | F7 | F8 | F9
  deriving DecidableEq, Repr

inductive RuntimeInvariant
  | F2 | F3 | F4 | F5 | F6 | F7 | F8 | F9
  deriving DecidableEq, Repr

def RuntimeInvariant.invariant : RuntimeInvariant → Invariant
  | .F2 => .F2 | .F3 => .F3 | .F4 => .F4 | .F5 => .F5
  | .F6 => .F6 | .F7 => .F7 | .F8 => .F8 | .F9 => .F9

/-- The module graph is part of the registration input, with a proof that every
named enforcer is installed.  F1 is separated because it is structural, not a
runtime flag. -/
structure SystemDesign where
  modules : List Module
  enforcedBy : Invariant → List Module
  enforcersInstalled : ∀ i m, m ∈ enforcedBy i → m ∈ modules
  structuralInvariants : List Invariant
  runtimeInvariants : List RuntimeInvariant

def systemDesign : SystemDesign where
  modules :=
    [.registration, .frame, .solver, .adjudicator, .memory, .promotion, .measurement]
  enforcedBy
    | .F1 => [.solver]
    | .F2 => [.adjudicator]
    | .F3 => [.adjudicator, .memory]
    | .F4 => [.registration]
    | .F5 => [.registration]
    | .F6 => [.measurement]
    | .F7 => [.memory, .promotion]
    | .F8 => [.frame]
    | .F9 => [.registration]
  enforcersInstalled := by
    intro i m hm
    cases i <;> simp at hm ⊢ <;> aesop
  structuralInvariants := [.F1]
  runtimeInvariants := [.F2, .F3, .F4, .F5, .F6, .F7, .F8, .F9]

/-- The previously decorative module assignment is now a field used by the
registration, and this theorem exposes its load-bearing coverage proof. -/
theorem every_enforcer_is_installed (i : Invariant) (m : Module)
    (h : m ∈ systemDesign.enforcedBy i) : m ∈ systemDesign.modules :=
  systemDesign.enforcersInstalled i m h

/-! ## Recorded trace -/

/-- The choice which round one has not yet made.  These are the three properties
whose values the choice fixes for the later series. -/
structure ProblemUnit where
  problemId : String
  difficultyStratum : String
  regime : String
  lockedLemmaExposure : List String
  deriving DecidableEq, Repr

/-- A closing frame can only be constructed with evidence that work changed it.
There is no raw `closingHash` field elsewhere in the run trace. -/
structure WorkedFrame where
  scaffoldHash : String
  closingHash : String
  changed : closingHash ≠ scaffoldHash

inductive Capability
  | registrationGatesLaunch
  | frameContainmentWitnessed
  | createdFrameWorked
  | uniqueDisposition
  | offerUseDisposition
  | needRetrieval
  | promotionImportable
  | promotionNeedTaggable
  | measurementPopulated
  deriving DecidableEq, Repr

/-- A typed probe receipt.  The capability is not inferred from `evidenceId`;
the id names the recorded witness and `capability` determines the predicate that
must independently pass. -/
structure CapabilityProbe where
  capability : Capability
  evidenceId : String
  recorded : Bool
  deriving DecidableEq, Repr

/-- Only fields used by a probe appear here.  A runtime trace may carry more data. -/
structure Trace where
  problem : ProblemUnit
  frame : WorkedFrame
  launchGateRefusedWithoutWitness : Bool
  cycleClosed : Bool
  dispositionIds : List String
  memoryOfferIds : List String
  memoryDispositionOfferIds : List String
  stratumFrozenAt : Nat
  assignedAt : Nat
  comparisonRegimes : List String
  denominatorDeclared : Bool
  denominatorInferredFromCorpus : Bool
  availableArtifactIds : List String
  needProbeRetrievedIds : List String
  containmentClaimed : Bool
  containmentProbeRecorded : Bool
  containmentProbePassed : Bool
  capabilityProbes : List CapabilityProbe
  requiredMeasurementFields : List String
  populatedMeasurementFields : List String
  promotedArtifactIds : List String
  importablePromotedArtifactIds : List String
  needTaggedPromotedArtifactIds : List String

/-- Turn any decidable trace proposition into an executable, sound observable. -/
def observable (name : String) (holds : Trace → Prop) [DecidablePred holds] :
    Observable Trace where
  name := name
  holds := holds
  check := fun t => decide (holds t)
  check_sound := by
    intro t h
    exact of_decide_eq_true h

/-- Claims fixed by the consolidated candidate, not supplied by the observed trace. -/
def registeredCapabilities : List Capability :=
  [.registrationGatesLaunch, .frameContainmentWitnessed, .createdFrameWorked,
   .uniqueDisposition, .offerUseDisposition, .needRetrieval,
   .promotionImportable, .promotionNeedTaggable, .measurementPopulated]

/-- X's fields fixed before round one.  A trace may not shrink this denominator. -/
def registeredMeasurementFields : List String :=
  ["statement defects at review",
   "terminal disposition",
   "residual executable sorries",
   "attempts or closer hops",
   "axiom cleanliness",
   "memories promoted",
   "review escape rate",
   "promoted then surfaced then used",
   "contract leaks",
   "duplicate declarations",
   "locked-lemma exposure",
   "promotion coverage",
   "unconsumed promotions",
   "import-only edges",
   "scribe lane coverage",
   "arc-lane yield",
   "rewrite rule offered and used"]

/-! ## F1 by construction; F2--F9 as probe-backed observables -/

/-- F1 is obtained from the only frame constructor admitted to a trace, not by
testing a possibly scaffold-identical closing trace. -/
theorem frame_is_worked (t : Trace) : t.frame.closingHash ≠ t.frame.scaffoldHash :=
  t.frame.changed

def f2UniqueDisposition : Observable Trace :=
  observable "F2: every closed cycle has exactly one disposition" fun t =>
    t.cycleClosed = true → t.dispositionIds.length = 1

def f3OfferDispositions : Observable Trace :=
  observable "F3: every memory offer has a use-disposition" fun t =>
    ∀ offer ∈ t.memoryOfferIds, offer ∈ t.memoryDispositionOfferIds

def f4StratumFrozen : Observable Trace :=
  observable "F4: difficulty stratum was frozen before assignment" fun t =>
    t.stratumFrozenAt < t.assignedAt

def f5SingleRegime : Observable Trace :=
  observable "F5: a comparison does not span regimes unstratified" fun t =>
    t.comparisonRegimes.eraseDups.length ≤ 1

def f6DeclaredDenominator : Observable Trace :=
  observable "F6: denominator is declared and not inferred from corpus size" fun t =>
    t.denominatorDeclared = true ∧ t.denominatorInferredFromCorpus = false

def f7NeedRetrievable : Observable Trace :=
  observable "F7: every available artifact is returned by a need-vocabulary probe" fun t =>
    ∀ artifact ∈ t.availableArtifactIds, artifact ∈ t.needProbeRetrievedIds

def f8WitnessedContainment : Observable Trace :=
  observable "F8: claimed containment has a recorded passing probe" fun t =>
    t.containmentClaimed = true →
      t.containmentProbeRecorded = true ∧ t.containmentProbePassed = true

/-- X's population guarantee, separate from denominator discipline F6. -/
def measurementVectorPopulated : Observable Trace :=
  observable "X: every required measurement field is populated" fun t =>
    t.requiredMeasurementFields = registeredMeasurementFields ∧
      ∀ field ∈ registeredMeasurementFields, field ∈ t.populatedMeasurementFields

/-- P's importability guarantee. -/
def promotionsImportable : Observable Trace :=
  observable "P: every promoted artifact is importable" fun t =>
    ∀ artifact ∈ t.promotedArtifactIds, artifact ∈ t.importablePromotedArtifactIds

/-- P's need-taggability guarantee. -/
def promotionsNeedTagged : Observable Trace :=
  observable "P: every promoted artifact carries need vocabulary" fun t =>
    ∀ artifact ∈ t.promotedArtifactIds, artifact ∈ t.needTaggedPromotedArtifactIds

/-- The concrete predicate a capability probe must support.  Probe identity and
capability truth are checked independently. -/
def Capability.holds : Capability → Trace → Prop
  | .registrationGatesLaunch, t => t.launchGateRefusedWithoutWitness = true
  | .frameContainmentWitnessed, t => f8WitnessedContainment.holds t
  | .createdFrameWorked, t => t.frame.closingHash ≠ t.frame.scaffoldHash
  | .uniqueDisposition, t => f2UniqueDisposition.holds t
  | .offerUseDisposition, t => f3OfferDispositions.holds t
  | .needRetrieval, t => f7NeedRetrievable.holds t
  | .promotionImportable, t => promotionsImportable.holds t
  | .promotionNeedTaggable, t => promotionsNeedTagged.holds t
  | .measurementPopulated, t => measurementVectorPopulated.holds t

noncomputable def f9CapabilityProbes : Observable Trace := by
  classical
  exact observable "F9: every claimed capability has recorded evidence for its predicate" fun t =>
    ∀ capability ∈ registeredCapabilities,
      capability.holds t ∧
        ∃ probe ∈ t.capabilityProbes,
          probe.capability = capability ∧ probe.recorded = true ∧ probe.evidenceId ≠ ""

noncomputable def runtimeInvariantObservable : RuntimeInvariant → Observable Trace
  | .F2 => f2UniqueDisposition
  | .F3 => f3OfferDispositions
  | .F4 => f4StratumFrozen
  | .F5 => f5SingleRegime
  | .F6 => f6DeclaredDenominator
  | .F7 => f7NeedRetrievable
  | .F8 => f8WitnessedContainment
  | .F9 => f9CapabilityProbes

noncomputable def systemFlags : List (Flag Trace) :=
  (systemDesign.runtimeInvariants.map fun i => ⟨s!"{repr i}", runtimeInvariantObservable i⟩) ++
    [⟨"measurement vector populated", measurementVectorPopulated⟩,
     ⟨"promotions importable", promotionsImportable⟩,
     ⟨"promotions need-tagged", promotionsNeedTagged⟩]

/-! ## Round one: parameterized prospective registration -/

/-- A one-shot measurement has one descriptive arm and no treatment axis. -/
def measurementArm : Arm where
  name := "one problem, one-shot measurement"
  neutral := false
  axes := []

/-- Round one is the pilot unit.  The candidate does not determine whether its
variation is controlled or measured, nor the endpoint that either constructor requires,
so that choice remains an argument. -/
def round1Replication (problem : ProblemUnit) (variation : VariationPlan) :
    ReplicationPlan ProblemUnit :=
  .pilot [problem] (by simp) variation

/-- The base registration, with mandatory but currently unspecified operational
quantities exposed as inputs rather than invented constants. -/
noncomputable def round1Base (estimatedCost budgetCap : ℝ) (teardownDeadline : Option ℝ) :
    Registration Trace where
  name := "APM demonstration round 1: build measurability on one problem"
  claim := .descriptive
  arms := [measurementArm]
  flags := systemFlags
  estimatedCost := estimatedCost
  budgetCap := budgetCap
  teardownDeadline := teardownDeadline

/-- A round-one preregistration can be constructed once the candidate's missing
variation endpoint, stopping semantics, total outcome interpretation, and operational
quantities are supplied.  Requiring these arguments is the formal underspecification
result of this pass. -/
noncomputable def round1Registration (Outcome : Type*) (problem : ProblemUnit)
    (variation : VariationPlan) (estimatedCost budgetCap : ℝ)
    (teardownDeadline : Option ℝ) (stopRules : List (StopRule Trace))
    (stopRulesNonempty : stopRules ≠ []) (decision : DecisionRule Trace Outcome) :
    ProspectiveRegistration ProblemUnit Trace Outcome where
  base := round1Base estimatedCost budgetCap teardownDeadline
  replication := round1Replication problem variation
  stopRules := stopRules
  stopRulesNonempty := stopRulesNonempty
  decision := decision

/-! The generic gate applies without a second APM-specific launch path. -/

theorem no_round1_witness_of_failed_invariant
    (estimatedCost budgetCap : ℝ) (teardownDeadline : Option ℝ)
    (e : ExperimentalDesign.Evidence) (smoke : Trace) (i : RuntimeInvariant)
    (hfail : ¬ (runtimeInvariantObservable i).holds smoke) :
    IsEmpty (ExperimentalDesign.ReadyToRun
      (round1Base estimatedCost budgetCap teardownDeadline) e smoke) := by
  apply ExperimentalDesign.no_witness_of_inert_flag
    (r := round1Base estimatedCost budgetCap teardownDeadline)
    (f := ⟨s!"{repr i}", runtimeInvariantObservable i⟩)
  · unfold round1Base systemFlags
    cases i <;> simp [systemDesign, runtimeInvariantObservable]
  · exact hfail

end DarkTower.APMDemonstration
