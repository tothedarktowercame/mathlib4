/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.BaldwinDesign
import DarkTower.ExperimentalDesign
import Mathlib.Tactic.NormNum

/-!
# Preregistration: does lifetime rewriting guide MetaCA evolution?

The earlier registrations targeted complete static assimilation.  This one asks the
logically prior question: does evolution with lifetime rewriting produce inherited
starting points which learn sooner and generalise better than evolution without
rewriting?  Static assimilation remains a separately certified secondary outcome.

The contrast is evolutionary, not merely phenotypic.  The two selected arms begin from
the same ancestor, use paired genetic randomness and fixed train/held-out task sets,
then undergo identical learning-budget ablations.  A `GuidanceWitness` is required for
the guidance outcome; final reach after unrestricted learning is not a substitute.

This file intentionally supplies no `ProspectiveReadyToRun`: the Clojure system must
first implement and smoke-test these modes and emit the typed certificates.
-/

namespace BaldwinGuidancePreregistration

open DarkTower.BaldwinDesign
open ExperimentPreregistration ExperimentalDesign

universe u v

/-- Exact tasks are fixed by deterministic generator version, seed, and count. -/
def trainingTaskSpecification : String :=
  "metaca-guidance-tasks-v1/train/seeds=1..3/sites=0,20,40,60"

def heldOutTaskSpecification : String :=
  "metaca-guidance-tasks-v1/heldout/seeds=101..103/sites=0,20,40,60"

/-- Learning budgets at which every evolved endpoint is evaluated. -/
def learningBudgets : List Nat := [0, 4, 16, 64, 120]

/--
What the smoke test and final analysis must report.  The outcome fields contain real
Lean certificates, not booleans whose connection to the claim is left implicit.
-/
structure Trace {ι : Type u} {Rule : Type v} (d : GuidanceDesign ι Rule) (n : Nat) where
  learningEnabledObserved : Bool
  learningDisabledObserved : Bool
  pairedGeneticTape : Bool
  pairedEvaluationTape : Bool
  trainingTasksObserved : String
  heldOutTasksObserved : String
  taskSetsDisjoint : Bool
  observedLearningBudgets : List Nat
  configurationValid : Bool
  positiveControlPassed : Bool
  treatmentSeparated : Bool
  artifactsComplete : Bool
  deadlineExceeded : Bool
  guidanceCertificate : Option (d.GuidanceWitness n)
  assimilationCertificate : Option (d.toExperimentalDesign.BaldwinWitness n)

def learningEnabled {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule} {n : Nat} :
    Flag (Trace d n) where
  name := "lifetime rewriting enabled during evolution"
  observable :=
    { name := "learning arm records realised within-lifetime rewrites"
      holds := fun t => t.learningEnabledObserved = true
      check := fun t => t.learningEnabledObserved
      check_sound := by simp }

def learningDisabled {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule} {n : Nat} :
    Flag (Trace d n) where
  name := "lifetime rewriting disabled during control evolution"
  observable :=
    { name := "no-learning arm records zero realised within-lifetime rewrites"
      holds := fun t => t.learningDisabledObserved = true
      check := fun t => t.learningDisabledObserved
      check_sound := by simp }

def alignedRandomness {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule} {n : Nat} :
    Flag (Trace d n) where
  name := "paired genetic and evaluation random tapes"
  observable :=
    { name := "treatments consume identical scheduled draws, including discarded draws"
      holds := fun t => t.pairedGeneticTape = true ∧ t.pairedEvaluationTape = true
      check := fun t => t.pairedGeneticTape && t.pairedEvaluationTape
      check_sound := by simp }

def fixedTaskPartition {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule} {n : Nat} :
    Flag (Trace d n) where
  name := "preregistered disjoint training and held-out tasks"
  observable :=
    { name := "task specifications equal the registration and the two sets are disjoint"
      holds := fun t =>
        t.trainingTasksObserved = trainingTaskSpecification ∧
          t.heldOutTasksObserved = heldOutTaskSpecification ∧ t.taskSetsDisjoint = true
      check := fun t =>
        (t.trainingTasksObserved == trainingTaskSpecification) &&
          (t.heldOutTasksObserved == heldOutTaskSpecification) && t.taskSetsDisjoint
      check_sound := by
        intro t h
        simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using h }

def learningCurveReadout {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule}
    {n : Nat} : Flag (Trace d n) where
  name := "zero, truncated, and full learning-budget ablations"
  observable :=
    { name := "every endpoint is evaluated at the preregistered budgets"
      holds := fun t => t.observedLearningBudgets = learningBudgets
      check := fun t => t.observedLearningBudgets == learningBudgets
      check_sound := by simp }

/-- The treatment axis is executable only if both learning regimes are reachable. -/
noncomputable def learningRegimeAxis : Axis where
  name := "lifetime rewriting during evolutionary evaluation"
  levels := [0, 1]
  score := id

theorem learningRegimeAxis_navigable : learningRegimeAxis.Navigable := by
  unfold Axis.Navigable Axis.gradientSteps learningRegimeAxis
  norm_num

noncomputable def mutationOnlyArm : Arm where
  name := "mutation-only lifecycle null"
  neutral := true
  axes := [learningRegimeAxis]

noncomputable def noLearningEvolutionArm : Arm where
  name := "selection with lifetime rewriting disabled"
  neutral := false
  axes := [learningRegimeAxis]

noncomputable def learningEvolutionArm : Arm where
  name := "selection with lifetime rewriting enabled"
  neutral := false
  axes := [learningRegimeAxis]

noncomputable def baseRegistration {ι : Type u} {Rule : Type v}
    (d : GuidanceDesign ι Rule) (n : Nat) : Registration (Trace d n) where
  name := "metaca-evolution-of-learnability"
  claim := .comparative
  arms := [mutationOnlyArm, noLearningEvolutionArm, learningEvolutionArm]
  flags := [learningEnabled, learningDisabled, alignedRandomness,
    fixedTaskPartition, learningCurveReadout]
  estimatedCost := 240
  budgetCap := 300
  teardownDeadline := some 300

/-- Paid-run settings, fixed before task materialisation or pilot inspection. -/
structure ProductionProtocol where
  generations : Nat
  population : Nat
  evaluationSeeds : Nat
  evaluationSites : Nat
  trainingTasks : Nat
  heldOutTasks : Nat
  budgets : List Nat
  plasticityCost : ℝ
  hgt : Bool
  pilotEvolutionSeed : Nat
  armTimeoutMinutes : Nat

noncomputable def productionProtocol : ProductionProtocol where
  generations := 40
  population := 32
  evaluationSeeds := 3
  evaluationSites := 4
  trainingTasks := 12
  heldOutTasks := 12
  budgets := learningBudgets
  plasticityCost := 0
  hgt := false
  pilotEvolutionSeed := 20260802
  armTimeoutMinutes := 80

def replication : ReplicationPlan Nat :=
  ReplicationPlan.seededConfirmation "pilot" (by decide)
    [20260802] [20260803, 20260804, 20260805] (by simp) (by simp) (by simp)

def invalidConfiguration {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule}
    {n : Nat} : StopRule (Trace d n) where
  name := "configuration, task-specification, or mode assertion failed"
  fires := fun t => t.configurationValid = false
  check := fun t => !t.configurationValid
  check_iff := by intro t; cases t.configurationValid <;> simp

def failedPositiveControl {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule}
    {n : Nat} : StopRule (Trace d n) where
  name := "planted Hinton--Nowlan selective-neighbourhood control failed"
  fires := fun t => t.positiveControlPassed = false
  check := fun t => !t.positiveControlPassed
  check_iff := by intro t; cases t.positiveControlPassed <;> simp

def inertTreatment {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule}
    {n : Nat} : StopRule (Trace d n) where
  name := "learning and no-learning evolutionary treatments were not separable"
  fires := fun t => t.treatmentSeparated = false
  check := fun t => !t.treatmentSeparated
  check_iff := by intro t; cases t.treatmentSeparated <;> simp

def missingArtifacts {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule}
    {n : Nat} : StopRule (Trace d n) where
  name := "required trajectory, ablation, checksum, or certificate is absent"
  fires := fun t => t.artifactsComplete = false
  check := fun t => !t.artifactsComplete
  check_iff := by intro t; cases t.artifactsComplete <;> simp

def deadline {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule} {n : Nat} :
    StopRule (Trace d n) where
  name := "independent dead-man deadline exceeded"
  fires := fun t => t.deadlineExceeded = true
  check := fun t => t.deadlineExceeded
  check_iff := by simp

/-- Guidance and assimilation are two independent certificate bits, not one scale. -/
inductive Outcome
  | guidanceAndAssimilation
  | guidanceOnly
  | assimilationWithoutGuidance
  | neitherCertified
  deriving DecidableEq, Repr

def classify {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule} {n : Nat}
    (t : Trace d n) : Outcome :=
  match t.guidanceCertificate, t.assimilationCertificate with
  | some _, some _ => .guidanceAndAssimilation
  | some _, none => .guidanceOnly
  | none, some _ => .assimilationWithoutGuidance
  | none, none => .neitherCertified

def decision {ι : Type u} {Rule : Type v} {d : GuidanceDesign ι Rule} {n : Nat} :
    DecisionRule (Trace d n) Outcome where
  name := "separate guidance and strong-assimilation certificates"
  classify := classify

noncomputable def experiment {ι : Type u} {Rule : Type v}
    (d : GuidanceDesign ι Rule) (n : Nat) : ProspectiveRegistration Nat (Trace d n) Outcome where
  base := baseRegistration d n
  replication := replication
  stopRules := [invalidConfiguration, failedPositiveControl, inertTreatment,
    missingArtifacts, deadline]
  stopRulesNonempty := by simp
  decision := decision

/-- A guidance-labelled outcome contains an actual `GuidanceWitness`. -/
theorem guidance_outcome_has_witness {ι : Type u} {Rule : Type v}
    {d : GuidanceDesign ι Rule} {n : Nat} {t : Trace d n}
    (h : classify t = .guidanceOnly ∨ classify t = .guidanceAndAssimilation) :
    ∃ w, t.guidanceCertificate = some w := by
  cases hg : t.guidanceCertificate with
  | none =>
      cases ha : t.assimilationCertificate <;> simp [classify, hg, ha] at h
  | some w => exact ⟨w, rfl⟩

/-- An assimilation-labelled outcome contains the existing strong Baldwin witness. -/
theorem assimilation_outcome_has_witness {ι : Type u} {Rule : Type v}
    {d : GuidanceDesign ι Rule} {n : Nat} {t : Trace d n}
    (h : classify t = .assimilationWithoutGuidance ∨
      classify t = .guidanceAndAssimilation) :
    ∃ w, t.assimilationCertificate = some w := by
  cases ha : t.assimilationCertificate with
  | none =>
      cases hg : t.guidanceCertificate <;> simp [classify, hg, ha] at h
  | some w => exact ⟨w, rfl⟩

/-- Placeholder smoke evidence: none of the new modes is assumed implemented. -/
def unimplementedSmoke {ι : Type u} {Rule : Type v} (d : GuidanceDesign ι Rule)
    (n : Nat) : Trace d n where
  learningEnabledObserved := false
  learningDisabledObserved := false
  pairedGeneticTape := false
  pairedEvaluationTape := false
  trainingTasksObserved := ""
  heldOutTasksObserved := ""
  taskSetsDisjoint := false
  observedLearningBudgets := []
  configurationValid := false
  positiveControlPassed := false
  treatmentSeparated := false
  artifactsComplete := false
  deadlineExceeded := false
  guidanceCertificate := none
  assimilationCertificate := none

/-- A prose registration cannot launch before the no-learning treatment acts in smoke. -/
theorem no_launch_before_no_learning_smoke {ι : Type u} {Rule : Type v}
    (d : GuidanceDesign ι Rule) (n : Nat) (e : Evidence) :
    IsEmpty (ReadyToRun (experiment d n).base e (unimplementedSmoke d n)) := by
  apply no_witness_of_inert_flag (f := learningDisabled)
  · simp [experiment, baseRegistration]
  · simp [Flag.honoured, learningDisabled, unimplementedSmoke]

end BaldwinGuidancePreregistration
