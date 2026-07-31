/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.ExperimentalDesign
import Mathlib.Tactic.NormNum

/-!
# Prospective preregistration of the Baldwin search-operator experiment

The previous battery found a selectable one-locus assimilation step but ordinary
evolution did not retain it.  This experiment asks whether that is a mutation-supply
problem.  In the existing operator, changing a rule and changing its hold bit are
independent mutations; the Hinton--Nowlan analogue changes `?` to a fixed allele in one
event.  The planted treatment therefore couples a plastic-to-held transition with an
*uninformed uniform* rule draw.  It does not use the rule maps to choose an allele.

The mutation treatment is crossed with a second, mechanistically distinct treatment:
all evaluations either draw their usual initial phenotype or face one preregistered
fixed initial phenotype.  This separates a coordination problem from a moving-target
problem without treating either repair as Baldwin evidence by itself.

This file deliberately does not construct `ProspectiveReadyToRun`.  The Clojure runner
does not yet implement or smoke-test the two new modes.  The final theorem makes that
refusal explicit: a prose plan cannot launch.
-/

namespace BaldwinSearchPreregistration

open ExperimentPreregistration ExperimentalDesign

/-- What the cross-arm smoke test and final analysis must report. -/
structure Trace where
  independentMutationObserved : Bool
  coupledMutationObserved : Bool
  variableP0Observed : Bool
  fixedP0Observed : Bool
  sharedRandomTape : Bool
  configurationValid : Bool
  positiveControlPassed : Bool
  treatmentSeparated : Bool
  artifactsComplete : Bool
  deadlineExceeded : Bool
  baselineWitness : Bool
  coupledWitness : Bool
  fixedP0Witness : Bool
  coupledFixedP0Witness : Bool
  deriving Repr

def independentMutation : Flag Trace where
  name := "independent hold/rule mutation"
  observable :=
    { name := "baseline arm records independent hold and rule proposals"
      holds := fun t => t.independentMutationObserved = true
      check := fun t => t.independentMutationObserved
      check_sound := by simp }

def coupledMutation : Flag Trace where
  name := "coupled plastic-to-held mutation"
  observable :=
    { name := "a plastic-to-held event draws exactly one uniform rule allele"
      holds := fun t => t.coupledMutationObserved = true
      check := fun t => t.coupledMutationObserved
      check_sound := by simp }

def variableP0 : Flag Trace where
  name := "evaluation-specific p0"
  observable :=
    { name := "baseline evaluations retain their seeded initial phenotypes"
      holds := fun t => t.variableP0Observed = true
      check := fun t => t.variableP0Observed
      check_sound := by simp }

def fixedP0 : Flag Trace where
  name := "preregistered fixed p0"
  observable :=
    { name := "every evaluation records the same preregistered initial phenotype"
      holds := fun t => t.fixedP0Observed = true
      check := fun t => t.fixedP0Observed
      check_sound := by simp }

def alignedTape : Flag Trace where
  name := "treatment-independent random tape"
  observable :=
    { name := "all arms consume the same scheduled draws, including discarded draws"
      holds := fun t => t.sharedRandomTape = true
      check := fun t => t.sharedRandomTape
      check_sound := by simp }

/--
Proposal supply under independent versus coupled mutation.  At rate `0.02`, an
independent proposal must flip both genes and then draw one of 256 rules; coupling
removes one factor of `0.02`.  This is an analytic apparatus axis, not an asserted
fitness response.
-/
noncomputable def proposalAxis : Axis where
  name := "plastic-to-held proposal supply"
  levels := [0, 1]
  score := fun treatment => if treatment = 0 then 0.02 ^ 2 / 256 else 0.02 / 256

theorem proposalAxis_navigable : proposalAxis.Navigable := by
  unfold Axis.Navigable Axis.gradientSteps proposalAxis
  norm_num

noncomputable def neutralArm : Arm where
  name := "no-selection mutation null"
  neutral := true
  axes := [proposalAxis]

noncomputable def independentVariableArm : Arm where
  name := "independent mutation / variable p0"
  neutral := false
  axes := [proposalAxis]

noncomputable def coupledVariableArm : Arm where
  name := "coupled mutation / variable p0"
  neutral := false
  axes := [proposalAxis]

noncomputable def independentFixedArm : Arm where
  name := "independent mutation / fixed p0"
  neutral := false
  axes := [proposalAxis]

noncomputable def coupledFixedArm : Arm where
  name := "coupled mutation / fixed p0"
  neutral := false
  axes := [proposalAxis]

noncomputable def baseRegistration : Registration Trace where
  name := "baldwin-search-operator-2x2"
  claim := .comparative
  arms := [neutralArm, independentVariableArm, coupledVariableArm,
    independentFixedArm, coupledFixedArm]
  flags := [independentMutation, coupledMutation, variableP0, fixedP0, alignedTape]
  estimatedCost := 180
  budgetCap := 240
  teardownDeadline := some 240

def replication : ReplicationPlan where
  pilotSeeds := [20260730]
  confirmationSeeds := [20260801, 20260802]
  pilotNonempty := by simp
  confirmationNonempty := by simp
  disjoint := by simp

def invalidConfiguration : StopRule Trace where
  name := "configuration or mode assertion failed"
  fires := fun t => t.configurationValid = false
  check := fun t => !t.configurationValid
  check_iff := by intro t; cases t.configurationValid <;> simp

def failedPositiveControl : StopRule Trace where
  name := "planted Hinton--Nowlan positive control failed"
  fires := fun t => t.positiveControlPassed = false
  check := fun t => !t.positiveControlPassed
  check_iff := by intro t; cases t.positiveControlPassed <;> simp

def inertTreatment : StopRule Trace where
  name := "coupled and independent proposal streams were not separable"
  fires := fun t => t.treatmentSeparated = false
  check := fun t => !t.treatmentSeparated
  check_iff := by intro t; cases t.treatmentSeparated <;> simp

def missingArtifacts : StopRule Trace where
  name := "required artifact or checksum is absent"
  fires := fun t => t.artifactsComplete = false
  check := fun t => !t.artifactsComplete
  check_iff := by intro t; cases t.artifactsComplete <;> simp

def deadline : StopRule Trace where
  name := "independent dead-man deadline exceeded"
  fires := fun t => t.deadlineExceeded = true
  check := fun t => t.deadlineExceeded
  check_iff := by simp

inductive Outcome
  | baselineAssimilation
  | coordinationBottleneck
  | movingTargetBottleneck
  | interaction
  | noTestedRepair
  deriving DecidableEq, Repr

/--
Only a complete executable Baldwin witness counts as assimilation.  Treatment effects
without such a witness diagnose a search mechanism; they do not become weaker Baldwin
claims.
-/
def classify (t : Trace) : Outcome :=
  if t.baselineWitness then .baselineAssimilation
  else if t.coupledFixedP0Witness then .interaction
  else if t.coupledWitness then .coordinationBottleneck
  else if t.fixedP0Witness then .movingTargetBottleneck
  else .noTestedRepair

def decision : DecisionRule Trace Outcome where
  name := "precommitted 2x2 Baldwin witness interpretation"
  classify := classify

noncomputable def experiment : ProspectiveRegistration Trace Outcome where
  base := baseRegistration
  replication := replication
  stopRules := [invalidConfiguration, failedPositiveControl, inertTreatment,
    missingArtifacts, deadline]
  stopRulesNonempty := by simp
  decision := decision

/-- A baseline Baldwin claim can only be emitted from a certified baseline witness bit. -/
theorem baselineAssimilation_requires_witness {t : Trace}
    (h : classify t = .baselineAssimilation) : t.baselineWitness = true := by
  cases hbase : t.baselineWitness
  · cases hcfx : t.coupledFixedP0Witness <;>
      cases hc : t.coupledWitness <;>
      cases hf : t.fixedP0Witness <;>
      simp [classify, hbase, hcfx, hc, hf] at h
  · rfl

/-- The unimplemented modes cannot be laundered into a launch certificate. -/
def unimplementedSmoke : Trace where
  independentMutationObserved := true
  coupledMutationObserved := false
  variableP0Observed := true
  fixedP0Observed := false
  sharedRandomTape := false
  configurationValid := false
  positiveControlPassed := false
  treatmentSeparated := false
  artifactsComplete := false
  deadlineExceeded := false
  baselineWitness := false
  coupledWitness := false
  fixedP0Witness := false
  coupledFixedP0Witness := false

theorem no_launch_before_coupled_mutation_smoke (e : Evidence) :
    IsEmpty (ReadyToRun experiment.base e unimplementedSmoke) := by
  apply no_witness_of_inert_flag (f := coupledMutation)
  · simp [experiment, baseRegistration]
  · simp [Flag.honoured, coupledMutation, unimplementedSmoke]

end BaldwinSearchPreregistration
