/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.ExperimentalDesign

/-!
# Preregistration: temperature cooling, reference-scored (exotype Slice 6e)

## Revision history

**v1 was reviewed by an independent agent and found unfit to register.** It did not
compile, and it carried two defects that the review is worth recording verbatim
against:

* *The positive control certified itself from missing data.* Its axis `score` fell
  through to `0` whenever the control's results were absent, producing a perfectly
  flat axis, which **discharged** the predicted-non-navigable obligation. Absence of
  evidence read as evidence of absence, inside a file whose whole purpose is to
  prevent that.
* *The motivating argument was wrong.* v1 claimed expected free energy `G` is
  incomparable across settings "because it contains the swept coefficient". This
  experiment sweeps `tau` while holding the coefficient fixed, so that argument did
  not apply to the design as written.

Both are fixed below, and the fixes are marked `-- v2:` so a reader can audit them.

## Why this experiment exists

Slices 1-6d were exploratory and are treated as apparatus development, not evidence.
They fixed the settings used here:

* copy-only exotype dynamics are **absorbing**; a pseudocount floor `mu` breaks the
  absorbing chain;
* a per-pattern preference **un-saturates the risk term** (median 0.2184 < max 0.7693,
  discriminating in 100% of sampled decisions);
* the epistemic term needs weight `c ~ 5` -- about 3.4x risk's within-decision range,
  and **not** the parity point 1.475, where nothing happens;
* at `c = 5` the field is mixed but is **confetti**: high entropy, low spatial
  structure, still declining at t=6000.

The problem those slices exposed: **they were all scored by Shannon entropy, which
confetti maximises.** Slice 3's own temperature sweep put its entropy maximum at the
hot end of the grid, which is nearly tautological. The programme was steering by a
statistic that cannot separate the state we want from the state we kept getting.

## The score

-- v2: the score is a log score against a FROZEN REFERENCE PREDICTOR, fixed across
-- every temperature and every arm, declared before the run.
--
-- v1 scored each pattern against its own NEXT claim. The review's objection is
-- correct and is not the naive circularity one: scoring a forecast against its
-- realised outcome is ordinary proper scoring. The defect is that BOTH the acting
-- pattern mixture AND the forecast being scored move with temperature, so mean
-- self-surprise conflates predictive accuracy, forecast sharpness, which patterns
-- survive, and which contexts they visit. A temperature could score well by
-- selecting easily-predicted contexts without producing any field organisation.
--
-- The frozen reference is one common conditional observer in every condition, so the
-- forecast function itself is not a moving target.  Temperature still changes the
-- distribution of patterns and contexts presented to that observer; this is part of
-- the registered estimand: predictability of the temperature-induced field under one
-- common observer.  The own-NEXT score is retained as a SECONDARY mechanistic
-- measurement, and calibration and sharpness are reported separately rather than
-- summed into one number.

**Prediction, committed before running:** the reference log score has an *interior*
minimum in temperature, the minimising field is classified late-window stationary, and
its entropy and spatial autocorrelation both exceed the measured confetti floor by a
declared margin.

**Comparative commitment:** fixed-temperature and linear-annealed cooling are compared
by summed reference log loss across the seven matched endpoints (equivalently mean loss,
because completeness fixes both profiles at seven cells).  Equality is an explicit
failure to separate, while every substantive outcome records which arm is lower.  The
no-selection arm supplies the empirical structural floor rather than the arm contrast.

It is refuted if the score is monotone across the ladder, if the minimiser sits at an
endpoint, if the minimiser is still in transient decline, or if its structure does not
clear the measured floor.
-/

namespace ExotypeCoolingPreregistration

open ExperimentPreregistration ExperimentalDesign

/-! ## Replicate units

-- v2: v1 declared 60 seeds per cell in its cost while registering four confirmation
-- units, which the review correctly called a contradiction. The replicate unit is a
-- seed BLOCK; four confirmation blocks of fifteen seeds is the 60 the cost assumes. -/

def seedsPerUnit : Nat := 15
def pilotUnits : List Nat := [20260803, 20260804, 20260805]
def confirmationUnits : List Nat := [20260901, 20260902, 20260903, 20260904]

def seedsPerCell : Nat := confirmationUnits.length * seedsPerUnit
def totalRuns : Nat := 4 * 7 * 60
def budgetMinutes : Nat := 30

theorem seedsPerCell_eq : seedsPerCell = 60 := by decide
theorem totalRuns_eq : totalRuns = 1680 := by decide

theorem pilotUnits_nodup : pilotUnits.Nodup := by decide
theorem confirmationUnits_nodup : confirmationUnits.Nodup := by decide

-- v2: `List.Disjoint` has no `Decidable` instance, so `by decide` failed to compile.
theorem units_disjoint : pilotUnits.Disjoint confirmationUnits := by
  intro a ha hb
  simp only [pilotUnits, confirmationUnits, List.mem_cons, List.not_mem_nil,
    or_false] at ha hb
  omega

/-! ## The temperature ladder

`tau` is the Boltzmann temperature of the existing softmax over expected free energy,
`exp ((G_min - G) / tau)`, so `1 / tau` is the AIF precision over policies. `tau = 0`
is the hard-argmin limit, already special-cased in the implementation.

-- v2: levels are indexed by basis points and the real ladder is derived from them.
-- v1 used `Nat.floor` to go the other way, which is a real Mathlib constant but is not
-- imported by this apparatus, and the conversion was the thing that made the axis
-- lookup order-dependent. -/

def temperatureBp : List Nat := [0, 300, 1000, 2000, 3000, 10000, 30000]

noncomputable def temperatureLevels : List ℝ :=
  temperatureBp.map (fun n => (n : ℝ) / 10000)

theorem temperatureBp_length : temperatureBp.length = 7 := by decide
theorem temperatureBp_nodup : temperatureBp.Nodup := by decide

def heldLambdaBp : Nat := 5500
def heldMuBp : Nat := 1000
def heldCoefficientBp : Nat := 50000
def fieldWidth : Nat := 80
def runSteps : Nat := 6000

/-- The exact Futon5 revision on which the run and representative rate measurement must
execute. -/
def registeredSourceRevision : String :=
  "541ef9eee18c69c1d46ba93094a39881f88b8bf5"

/-- SHA-256 of the canonical input manifest enumerated by `registeredCellSettings`
below, including replicate-block labels and the fixed run dimensions. -/
def registeredInputManifestSha256 : String :=
  "cfe147692080ae8e7f75ea1ff91b0ae6beaf9be7244500ded3d18c849ac858f4"

/-! ## Measured outcomes -/

/-- Temperature's complete operational status within one cell.  `linearAnneal` means
linear interpolation at every step, including both declared endpoints.  `notApplied`
records a nominal reporting level which is not supplied to selection. -/
inductive TemperatureSchedule
  | fixed (temperatureBp : Nat)
  | linearAnneal (startTemperatureBp endTemperatureBp startStep endStep : Nat)
  | notApplied (nominalTemperatureBp : Nat)
  deriving BEq, DecidableEq, Repr

/-- Exact settings read back from one arm/temperature cell. -/
structure CellSettings where
  armName : String
  temperatureBasisPoints : Nat
  lambdaBp : Nat
  muBp : Nat
  coefficientBp : Nat
  width : Nat
  steps : Nat
  schedule : TemperatureSchedule
  deriving BEq, DecidableEq, Repr

structure LevelResult where
  temperatureBasisPoints : Nat
  /-- **The registered score.** Mean log loss of the realised local context under the
  FROZEN REFERENCE predictor, basis points of nats. Lower is better. -/
  referenceLogLossBp : Nat
  /-- Secondary, mechanistic: log loss under each acting pattern's own NEXT claim.
  Reported, never used for the verdict. -/
  ownNextLogLossBp : Nat
  /-- v2: calibration and sharpness are reported separately rather than summed,
  so a diffuse-forecast win is visible instead of hidden. -/
  calibrationErrorBp : Nat
  sharpnessBp : Nat
  entropyBp : Nat
  autocorrelationBp : Nat
  /-- v2: v1 recorded this and then ignored it, so its prediction could pass on a
  still-declining minimum -- after the whole programme insisted that a slower decline
  is not a plateau. It is now required at the minimiser. -/
  latePlateau : Bool
  /-- Registered replicate-block identities contributing to this cell.  Expansion of a
  block into its fifteen individual seeds is deliberately deferred to finding #9. -/
  replicateUnitsObserved : List Nat
  seedsObserved : Nat
  deriving BEq, DecidableEq, Repr

structure ArmResult where
  armName : String
  levels : List LevelResult
  deriving BEq, DecidableEq, Repr

/-- Complete identity and provenance of the common observer.  Equality of this value is
the runtime boundary: a model with different code, training, ABI, or probability floor
is a different predictor rather than another instance of the registered one. -/
structure ReferencePredictorIdentity where
  identifier : String
  repositoryRevision : String
  implementationSha256 : String
  observationAbi : List String
  trainingDataSha256 : Option String
  fittingProcedure : String
  scoringProcedure : String
  probabilityFloorNumerator : Nat
  probabilityFloorDenominator : Nat
  deriving BEq, DecidableEq, Repr

/-- The preregistered observer is the existing deterministic, unfitted EFE predictor.
The source file was clean at the recorded revision when its SHA-256 was taken. -/
def registeredReferencePredictor : ReferencePredictorIdentity where
  identifier := "futon5.exotype.efe/predict"
  repositoryRevision := "541ef9eee18c69c1d46ba93094a39881f88b8bf5"
  implementationSha256 :=
    "523c9d46b82894f09aeb0434d11bbe55a0324f4e522a6e23fdcaaca34cab66f8"
  observationAbi := ["rule-change", "activity", "diversity", "hunger"]
  trainingDataSha256 := none
  fittingProcedure := "none: fixed declared constants with deterministic local shrinkage"
  scoringProcedure :=
    "mean channel negative log likelihood; Bernoulli outcome; clamp p to [1e-9,1-1e-9]"
  probabilityFloorNumerator := 1
  probabilityFloorDenominator := 1000000000

/-- Identity of the workload whose throughput may justify the billing-run budget. -/
structure BenchmarkWorkload where
  sourceRevision : String
  inputManifestSha256 : String
  width : Nat
  steps : Nat
  instrumentation : List String
  schedulesExercised : List String
  deriving BEq, DecidableEq, Repr

def registeredBenchmarkWorkload : BenchmarkWorkload where
  sourceRevision := registeredSourceRevision
  inputManifestSha256 := registeredInputManifestSha256
  width := fieldWidth
  steps := runSteps
  instrumentation := ["reference-log-loss", "own-next-log-loss", "calibration", "sharpness"]
  schedulesExercised := ["fixed", "linear-anneal", "not-applied"]

/-- Raw timing evidence, not an asserted rate.  The budget comparison below is derived
from completed runs and elapsed milliseconds without division or rounding. -/
structure BenchmarkObservation where
  workload : BenchmarkWorkload
  completedRuns : Nat
  elapsedMilliseconds : Nat
  deriving BEq, DecidableEq, Repr

structure Trace where
  sourceRevisionObserved : String
  inputManifestSha256Observed : String
  /-- Read back from the run, not from the declaration. -/
  temperaturesObserved : List Nat
  /-- Exact settings and full within-run temperature schedule read back per cell. -/
  cellSettingsObserved : List CellSettings
  /-- Identity read from the scorer artifact actually used by the run. -/
  referencePredictorObserved : ReferencePredictorIdentity
  /-- Positive-control readback: the number of calls to temperature-dependent
  selection at each nominal temperature.  The replay control requires seven zeros. -/
  controlSelectionCallsObserved : List Nat
  /-- Positive-control readback: a checksum of the complete pattern/action and realised
  context tape presented to the scorer at each nominal temperature.  The replay control
  requires the same nonzero checksum at every level. -/
  controlReplayChecksumsObserved : List Nat
  benchmarkObserved : BenchmarkObservation
  results : List ArmResult
  toolchainExercised : Bool
  codeIdentityAsserted : Bool
  teardownExercised : Bool
  artifactsComplete : Bool
  artifactsChecksummed : Bool
  deadlineExceeded : Bool
  deriving Repr

/-! ## Completeness

-- v2: THE CENTRAL FIX. Every downstream reading is gated on this, and -- crucially --
-- an incomplete trace makes the control axis NAVIGABLE rather than flat, so missing
-- data now FAILS the positive-control obligation instead of discharging it. -/

def armNames : List String :=
  ["fixed-temperature", "annealed", "no-selection", "selection-bypassed-replay-control"]

def levelsWellFormed (ls : List LevelResult) : Bool :=
  (ls.map (·.temperatureBasisPoints) == temperatureBp) &&
  ls.all (fun r =>
    r.replicateUnitsObserved == confirmationUnits &&
    r.seedsObserved == seedsPerCell)

def resultsWellFormed (t : Trace) : Bool :=
  (t.results.map (·.armName) == armNames) &&
  t.results.all (fun arm => levelsWellFormed arm.levels)

def registeredSchedule (armName : String) (temperature : Nat) : TemperatureSchedule :=
  if armName == "fixed-temperature" then .fixed temperature
  else if armName == "annealed" then .linearAnneal 30000 temperature 0 runSteps
  else .notApplied temperature

def registeredCellSettings : List CellSettings :=
  armNames.flatMap (fun armName => temperatureBp.map (fun temperature =>
    { armName := armName
      temperatureBasisPoints := temperature
      lambdaBp := heldLambdaBp
      muBp := heldMuBp
      coefficientBp := heldCoefficientBp
      width := fieldWidth
      steps := runSteps
      schedule := registeredSchedule armName temperature }))

def benchmarkWellFormed (t : Trace) : Bool :=
  (t.benchmarkObserved.workload == registeredBenchmarkWorkload) &&
  0 < t.benchmarkObserved.completedRuns &&
  0 < t.benchmarkObserved.elapsedMilliseconds

def benchmarkWithinBudget (t : Trace) : Bool :=
  totalRuns * t.benchmarkObserved.elapsedMilliseconds ≤
    budgetMinutes * 60000 * t.benchmarkObserved.completedRuns

/-- The no-selection arm and level from which both structural floors are derived.
Choosing the source here prevents choosing a favourable baseline after seeing the
treatment.  At `tau = 0.3` this is the registered empirical confetti reference. -/
def confettiReferenceTemperatureBp : Nat := 3000

def confettiReference (t : Trace) : Option LevelResult := do
  let arm ← t.results.find? (fun a => a.armName == "no-selection")
  arm.levels.find? (fun r => r.temperatureBasisPoints == confettiReferenceTemperatureBp)

/-- The positive control closes both causal routes from temperature to its measured
distribution.  Selection is never invoked, so temperature cannot alter which pattern
acts.  The identical complete action/context tape is replayed at every nominal level,
so temperature cannot alter context composition indirectly through later dynamics. -/
def controlRouteClosed (t : Trace) : Bool :=
  (t.controlSelectionCallsObserved == List.replicate temperatureBp.length 0) &&
  match t.controlReplayChecksumsObserved with
  | [] => false
  | checksum :: _ =>
      (checksum != 0) &&
      (t.controlReplayChecksumsObserved ==
        List.replicate temperatureBp.length checksum)

def traceComplete (t : Trace) : Bool :=
  (t.sourceRevisionObserved == registeredSourceRevision) &&
  (t.inputManifestSha256Observed == registeredInputManifestSha256) &&
  (t.temperaturesObserved == temperatureBp) &&
  (t.cellSettingsObserved == registeredCellSettings) &&
  (t.referencePredictorObserved == registeredReferencePredictor) &&
  controlRouteClosed t &&
  resultsWellFormed t &&
  benchmarkWellFormed t &&
  benchmarkWithinBudget t &&
  t.artifactsComplete && t.artifactsChecksummed

/-! ## Scoring an axis

Invalid data must fail either polarity of axis obligation.  A treatment requires a
navigable axis, so its invalid-data fallback is constant.  The positive control requires
a non-navigable axis, so its invalid-data fallback varies with the nominal level.  The
completeness flag independently rejects the trace as a whole; these role-specific
fallbacks ensure that no individual axis obligation is spuriously discharged either. -/

noncomputable def scoreOf (t : Trace) (name : String) (x : ℝ) : ℝ :=
  if traceComplete t then
    match t.results.find? (fun a => a.armName == name) with
    | some a =>
        match a.levels.find? (fun r => ((r.temperatureBasisPoints : ℝ) / 10000) = x) with
        | some r => - (r.referenceLogLossBp : ℝ)
        | none => 0
    | none => 0
  else 0

/-- Positive-control score.  Complete traces expose the measured reference log loss.
Incomplete traces deliberately vary with the nominal level, preventing missing control
data from satisfying the exact predicted-null obligation. -/
noncomputable def controlScoreOf (t : Trace) (x : ℝ) : ℝ :=
  if traceComplete t then
    match t.results.find? (fun a => a.armName == "selection-bypassed-replay-control") with
    | some a =>
        match a.levels.find? (fun r => ((r.temperatureBasisPoints : ℝ) / 10000) = x) with
        | some r => - (r.referenceLogLossBp : ℝ)
        | none => x + 1
    | none => x + 1
  else x + 1

/-! ## Flags -/

def settingsHonoured : Flag Trace where
  name := "ladder in force, registered reference predictor matched, every cell complete"
  observable :=
    { name := "declared ladder, exact registered observer, and full cells observed"
      holds := fun t =>
        t.sourceRevisionObserved = registeredSourceRevision ∧
        t.inputManifestSha256Observed = registeredInputManifestSha256 ∧
        traceComplete t = true
      check := fun t =>
        (t.sourceRevisionObserved == registeredSourceRevision) &&
        (t.inputManifestSha256Observed == registeredInputManifestSha256) &&
        traceComplete t
      check_sound := by
        intro t h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨h.1.1, h.1.2, h.2⟩ }

/-! ## Arms -/

noncomputable def fixedCooling (t : Trace) : Arm where
  name := "fixed-temperature"
  neutral := false
  role := .treatment
  axes := [{ name := "tau (fixed)", levels := temperatureLevels
             score := scoreOf t "fixed-temperature" }]

noncomputable def annealedCooling (t : Trace) : Arm where
  name := "annealed"
  neutral := false
  role := .treatment
  axes := [{ name := "tau (annealing endpoint)", levels := temperatureLevels
             score := scoreOf t "annealed" }]

def noSelection : Arm where
  name := "no-selection"
  neutral := true
  role := .baselineNeutral
  axes := []

/-- The positive control bypasses selection and replays one identical, checksummed
pattern/action/context tape at every nominal temperature.  Temperature is recorded as a
label but is not supplied to the control dynamics.  It therefore has no route either to
same-kind pattern selection or to context composition.  With identical scorer input,
the registered null is exact; any score movement is instrumentation or configuration
leakage and abandons the run. -/
noncomputable def selectionBypassedReplayControl (t : Trace) : Arm where
  name := "selection-bypassed-replay-control"
  neutral := false
  role := .positiveControl
  axes := [{ name := "nominal tau (selection bypassed, identical tape replayed)"
             levels := temperatureLevels
             onViolation := some .abandonRun
             score := controlScoreOf t }]

/-! ## Registered arm contrast -/

/-- Aggregate frozen-reference loss for one named arm.  Completeness has already fixed
the exact ordered seven-level profile; this function remains total on arbitrary traces
so the decision rule can classify malformed input as incomplete. -/
def armReferenceLossTotal (t : Trace) (name : String) : Option Nat := do
  let arm ← t.results.find? (fun result => result.armName == name)
  if levelsWellFormed arm.levels then
    some (arm.levels.foldl (fun total level => total + level.referenceLogLossBp) 0)
  else none

def fixedAnnealedTotals (t : Trace) : Option (Nat × Nat) := do
  let fixed ← armReferenceLossTotal t "fixed-temperature"
  let annealed ← armReferenceLossTotal t "annealed"
  pure (fixed, annealed)

/-- Direction of the preregistered fixed-versus-annealed contrast.  There is no equality
constructor: equality is the explicit `fixedAnnealedNotSeparated` outcome below. -/
inductive ContrastDirection
  | fixedLower
  | annealedLower
  deriving DecidableEq, Repr

def separatedDirection (fixed annealed : Nat) : Option ContrastDirection :=
  if fixed < annealed then some .fixedLower
  else if annealed < fixed then some .annealedLower
  else none

/-! ## Evidence

The comparative evidence is computed from the named pair and registered statistic.
There is no trace Boolean which can assert separation without exhibiting the two
validated profiles. -/

def evidenceOf (t : Trace) : Evidence where
  toolchainExercised := t.toolchainExercised
  codeIdentityAsserted := t.codeIdentityAsserted
  teardownExercised := t.teardownExercised
  armsShownDistinct :=
    match fixedAnnealedTotals t with
    | some (fixed, annealed) => decide (fixed ≠ annealed)
    | none => false

/-! ## Cost -/

/-- Cross-multiplied runtime estimate derived from raw representative timing evidence.
The budget obligation compares these quantities directly, avoiding an asserted or
rounded runs-per-minute field. -/
def estimatedRunMilliseconds (t : Trace) : Nat :=
  totalRuns * t.benchmarkObserved.elapsedMilliseconds

def benchmarkBudgetCapacity (t : Trace) : Nat :=
  budgetMinutes * 60000 * t.benchmarkObserved.completedRuns

/-- Invalid or absent benchmark evidence must fail the budget obligation itself, not
merely the independent completeness flag. -/
def registeredEstimatedCost (t : Trace) : Nat :=
  if benchmarkWellFormed t then estimatedRunMilliseconds t else 1

def registeredBudgetCap (t : Trace) : Nat :=
  if benchmarkWellFormed t then benchmarkBudgetCapacity t else 0

/-! ## Interpretation

-- v2: v1's rule called everything that was not an interior minimum "monotone",
-- so `[1,3,2]` -- plainly not monotone -- was reported as monotone. It also used
-- `headD`/`getLastD`, ordering by list position rather than by temperature, and
-- silently accepted endpoint ties. Both are fixed, and ties are now explicit. -/

def nondecreasing (xs : List Nat) : Bool :=
  (xs.zip xs.tail).all (fun p => p.1 ≤ p.2)

def nonincreasing (xs : List Nat) : Bool :=
  (xs.zip xs.tail).all (fun p => p.2 ≤ p.1)

def isMonotone (xs : List Nat) : Bool := nondecreasing xs || nonincreasing xs

/-- A strict, unique interior minimum: strictly below both endpoints, and attained at
exactly one level. -/
def strictInteriorMinimum (xs : List Nat) : Option Nat :=
  match xs with
  | [] => none
  | x :: rest =>
      let last := (x :: rest).getLast (by simp)
      let best := (x :: rest).foldl min x
      if best < x ∧ best < last ∧ (xs.filter (fun v => v == best)).length = 1
      then some best else none

inductive Outcome
  /-- The registered prediction: interior minimum, stationary there, structure above
  the measured floor, carrying the fixed-versus-annealed contrast direction. -/
  | interiorMinimumWithStructure (contrast : ContrastDirection)
  /-- v2: new. Interior minimum, but still in transient decline at the minimiser. -/
  | interiorMinimumStillTransient (contrast : ContrastDirection)
  /-- Interior minimum whose field does not clear the measured confetti floor. -/
  | interiorMinimumWithoutStructure (contrast : ContrastDirection)
  /-- Genuinely monotone across the ladder: cooling buys nothing. -/
  | monotone (contrast : ContrastDirection)
  /-- v2: new. Non-monotone with no strict interior minimum -- ties, or a minimum
  at an endpoint. v1 reported these as `monotone`, which was false. -/
  | noStrictInteriorMinimum (contrast : ContrastDirection)
  /-- The named fixed-temperature and annealed profiles have equal aggregate reference
  loss, so the comparative claim fails to separate. -/
  | fixedAnnealedNotSeparated
  /-- The selection-bypassed replay control moved despite identical scorer input. -/
  | controlMoved
  /-- v2: new. Trace incomplete; nothing is interpretable. -/
  | incomplete
  | stopped
  deriving DecidableEq, Repr

/-- Margin by which the minimiser must clear the measured confetti floor. -/
def structuralMarginBp : Nat := 500

def spread (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => (x :: rest).foldl max x - (x :: rest).foldl min x

def decision (t : Trace) : Outcome :=
  if t.deadlineExceeded then Outcome.stopped
  else if !traceComplete t then Outcome.incomplete
  else
    match t.results.find? (fun a => a.armName == "selection-bypassed-replay-control"),
          t.results.find? (fun a => a.armName == "fixed-temperature") with
    | some ctrl, some arm =>
        if 0 < spread (ctrl.levels.map (·.referenceLogLossBp))
        then Outcome.controlMoved
        else
          match fixedAnnealedTotals t with
          | none => Outcome.incomplete
          | some (fixed, annealed) =>
              match separatedDirection fixed annealed with
              | none => Outcome.fixedAnnealedNotSeparated
              | some contrast =>
                  let ss := arm.levels.map (·.referenceLogLossBp)
                  match strictInteriorMinimum ss with
                  | none => if isMonotone ss then Outcome.monotone contrast
                            else Outcome.noStrictInteriorMinimum contrast
                  | some best =>
                      match arm.levels.find? (fun r => r.referenceLogLossBp == best),
                            confettiReference t with
                      | some r, some confetti =>
                          if !r.latePlateau then
                            Outcome.interiorMinimumStillTransient contrast
                          else if confetti.entropyBp + structuralMarginBp ≤ r.entropyBp ∧
                                  confetti.autocorrelationBp + structuralMarginBp
                                    ≤ r.autocorrelationBp
                          then Outcome.interiorMinimumWithStructure contrast
                          else Outcome.interiorMinimumWithoutStructure contrast
                      | _, _ => Outcome.incomplete
    | _, _ => Outcome.incomplete

def decisionRule : DecisionRule Trace Outcome where
  name := "fixed-vs-annealed contrast plus interior fixed-temperature minimum"
  classify := decision

/-! ## Stop rules -/

def deadlineStop : StopRule Trace where
  name := "deadline exceeded"
  fires := fun t => t.deadlineExceeded = true
  check := fun t => t.deadlineExceeded
  check_iff := by intro t; constructor <;> (intro h; exact h)

def instrumentStop : StopRule Trace where
  name := "observed reference predictor differs from the preregistered identity"
  fires := fun t => t.referencePredictorObserved ≠ registeredReferencePredictor
  check := fun t => decide (t.referencePredictorObserved ≠ registeredReferencePredictor)
  check_iff := by intro t; simp

def identityStop : StopRule Trace where
  name := "source revision or input manifest differs from the registration"
  fires := fun t =>
    t.sourceRevisionObserved ≠ registeredSourceRevision ∨
    t.inputManifestSha256Observed ≠ registeredInputManifestSha256
  check := fun t => decide
    (t.sourceRevisionObserved ≠ registeredSourceRevision ∨
     t.inputManifestSha256Observed ≠ registeredInputManifestSha256)
  check_iff := by intro t; simp

def completenessStop : StopRule Trace where
  name := "trace identity, settings, schedule, sampling, or benchmark contradicts registration"
  fires := fun t => traceComplete t = false
  check := fun t => !traceComplete t
  check_iff := by
    intro t; constructor
    · intro h; simpa using h
    · intro h; simpa using h

/-! ## The registration -/

private noncomputable def registration (t : Trace) : Registration Trace where
  name := "exotype-6e-cooling-reference-scored"
  claim := .comparative
  arms := [fixedCooling t, annealedCooling t, noSelection,
    selectionBypassedReplayControl t]
  flags := [settingsHonoured]
  estimatedCost := (registeredEstimatedCost t : ℝ)
  budgetCap := (registeredBudgetCap t : ℝ)
  teardownDeadline := some 90

def replication : ReplicationPlan Nat :=
  ReplicationPlan.confirmation
    { name := "exotype-6c-c5-mixed-field", nameNonempty := by decide }
    pilotUnits confirmationUnits (by decide) (by decide) units_disjoint
    (VariationPlan.measured
      { name := "control-vs-control reference log score at fixed tau"
        nameNonempty := by decide })

private noncomputable def prospective (t : Trace) :
    ProspectiveRegistration Nat Trace Outcome where
  base := registration t
  replication := replication
  stopRules := [deadlineStop, instrumentStop, identityStop, completenessStop]
  stopRulesNonempty := by simp
  decision := decisionRule

/-- The only launch entry point licensed by this registration.  The registration,
apparatus evidence, and smoke trace are all derived from the same trace argument, so an
unrelated observation cannot discharge `armsSeparable`. -/
abbrev ReadyToLaunch (t : Trace) :=
  ProspectiveReadyToRun (prospective t) (evidenceOf t) t

noncomputable def launch (t : Trace) (_ready : ReadyToLaunch t)
    (run : ProspectiveRegistration Nat Trace Outcome → Trace) : Trace :=
  ProspectiveLaunch (prospective t) (evidenceOf t) t _ready run

/-- Equal aggregate fixed and annealed losses make the trace unable to supply the
registration-specific launch token. -/
theorem no_ready_of_fixedAnnealed_not_separated (t : Trace)
    (h : (evidenceOf t).armsShownDistinct = false) : IsEmpty (ReadyToLaunch t) := by
  refine ⟨fun ready => ?_⟩
  have discharged := ready.baseReady.discharged Obligation.armsSeparable (by
    simp [prospective, registration, Registration.obligations])
  change (evidenceOf t).armsShownDistinct = true at discharged
  rw [h] at discharged
  contradiction

/-! ## What this registration does NOT license

* Not a claim about `lambda*`. Every measurement of it was made with a saturated risk
  term, and Slice 6 showed the diversity under that configuration depended on the
  saturation. That needs its own registration.
* Not "the epistemic term works". Slice 6c showed only that a weight near 3.4x risk's
  range holds the field open, on one horizon, at one width.
* Not the exploratory slices as evidence. They are apparatus development, cited only
  for the settings they fixed.
* Not a causal claim from the own-NEXT score, which is retained as a mechanistic
  secondary and is deliberately excluded from `decision`.
-/

end ExotypeCoolingPreregistration
