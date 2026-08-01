/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.ExperimentalDesign

/-!
# Preregistration: does MetaCA rewriting leave a heritable target?

This diagnostic precedes another paid Baldwin selection run.  It crosses the two
identified sources of cross-lifetime variation: the initial phenotype and the
rewrite tape.  Agreement is recorded in ten-thousandths, avoiding rounded real
comparisons in the decision rule.

`400` (4%) is the above-chance screen: three equal rules among eighty loci already
exceeds it, against exact-rule chance `1/256`.  `2500` (25%) is the precommitted
threshold for a materially encodable target.  Neither threshold may be revised
after the diagnostic grid is read.
-/

namespace BaldwinMechanismPreregistration

open ExperimentPreregistration ExperimentalDesign

structure Trace where
  variableP0VariableRewrite : Nat
  fixedP0VariableRewrite : Nat
  variableP0SharedRewrite : Nat
  fixedP0SharedRewrite : Nat
  apparatusValid : Bool
  artifactsComplete : Bool
  deriving Repr

def chanceScreen : Nat := 400
def materialTarget : Nat := 2500
def exactAgreement : Nat := 10000

def apparatus : Flag Trace where
  name := "fully stationary positive apparatus control"
  observable :=
    { name := "fixed p0 and shared rewrite tape give exact field agreement"
      holds := fun t =>
        t.apparatusValid = true ∧ t.fixedP0SharedRewrite = exactAgreement
      check := fun t =>
        t.apparatusValid && (t.fixedP0SharedRewrite == exactAgreement)
      check_sound := by simp }

def complete : Flag Trace where
  name := "four-cell stationarity grid is complete"
  observable :=
    { name := "the diagnostic emitted and checksummed all four cells"
      holds := fun t => t.artifactsComplete = true
      check := fun t => t.artifactsComplete
      check_sound := by simp }

noncomputable def p0Axis : Axis where
  name := "initial phenotype schedule"
  levels := [0, 1]
  score := id

noncomputable def rewriteAxis : Axis where
  name := "rewrite randomness schedule"
  levels := [0, 1]
  score := id

noncomputable def variableVariableArm : Arm where
  name := "variable p0 / variable rewrite tape"
  neutral := false
  axes := [p0Axis, rewriteAxis]

noncomputable def fixedVariableArm : Arm where
  name := "fixed p0 / variable rewrite tape"
  neutral := false
  axes := [p0Axis, rewriteAxis]

noncomputable def variableSharedArm : Arm where
  name := "variable p0 / shared rewrite tape"
  neutral := false
  axes := [p0Axis, rewriteAxis]

noncomputable def fixedSharedArm : Arm where
  name := "fixed p0 / shared rewrite tape apparatus control"
  neutral := true
  axes := [p0Axis, rewriteAxis]

noncomputable def base : Registration Trace where
  name := "metaca-rewrite-target-stationarity"
  claim := .comparative
  arms := [variableVariableArm, fixedVariableArm, variableSharedArm, fixedSharedArm]
  flags := [apparatus, complete]
  estimatedCost := 10
  budgetCap := 30
  teardownDeadline := some 30

def replication : ReplicationPlan where
  pilotSeeds := [1, 2, 3, 4, 5, 6, 7, 8]
  confirmationSeeds := [101, 102, 103, 104, 105, 106, 107, 108]
  pilotNonempty := by simp
  confirmationNonempty := by simp
  disjoint := by simp

inductive Outcome
  | invalid
  | targetChanceLike
  | rewriteTapeDominant
  | phenotypeDominant
  | bothSourcesDestabilize
  | materiallyStationary
  deriving DecidableEq, Repr

def classify (t : Trace) : Outcome :=
  if !t.apparatusValid || t.fixedP0SharedRewrite != exactAgreement ||
      !t.artifactsComplete then .invalid
  else if t.variableP0VariableRewrite ≤ chanceScreen &&
      t.fixedP0VariableRewrite ≤ chanceScreen &&
      t.variableP0SharedRewrite ≤ chanceScreen then .targetChanceLike
  else if t.fixedP0VariableRewrite < materialTarget &&
      materialTarget ≤ t.variableP0SharedRewrite then .rewriteTapeDominant
  else if materialTarget ≤ t.fixedP0VariableRewrite &&
      t.variableP0SharedRewrite < materialTarget then .phenotypeDominant
  else if t.fixedP0VariableRewrite < materialTarget &&
      t.variableP0SharedRewrite < materialTarget then .bothSourcesDestabilize
  else .materiallyStationary

def decision : DecisionRule Trace Outcome where
  name := "precommitted stationarity-source classification"
  classify := classify

def badApparatus : StopRule Trace where
  name := "fully fixed cell is not exactly reproducible"
  fires := fun t => t.apparatusValid = false ∨
    t.fixedP0SharedRewrite ≠ exactAgreement
  check := fun t => !t.apparatusValid ||
    t.fixedP0SharedRewrite != exactAgreement
  check_iff := by
    intro t
    cases t.apparatusValid <;> simp

def missingArtifacts : StopRule Trace where
  name := "stationarity grid artifact is incomplete"
  fires := fun t => t.artifactsComplete = false
  check := fun t => !t.artifactsComplete
  check_iff := by intro t; cases t.artifactsComplete <;> simp

noncomputable def experiment : ProspectiveRegistration Trace Outcome where
  base := base
  replication := replication
  stopRules := [badApparatus, missingArtifacts]
  stopRulesNonempty := by simp
  decision := decision

theorem fixed_control_failure_is_invalid (t : Trace)
    (h : t.fixedP0SharedRewrite ≠ exactAgreement) : classify t = .invalid := by
  simp [classify, h]

end BaldwinMechanismPreregistration
