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

theorem seedsPerCell_eq : seedsPerCell = 60 := by decide

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

/-! ## Measured outcomes -/

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

structure Trace where
  sourceRevisionBound : Bool
  inputChecksumBound : Bool
  /-- Read back from the run, not from the declaration. -/
  temperaturesObserved : List Nat
  /-- Identity read from the scorer artifact actually used by the run. -/
  referencePredictorObserved : ReferencePredictorIdentity
  /-- Positive-control readback: the number of calls to temperature-dependent
  selection at each nominal temperature.  The replay control requires seven zeros. -/
  controlSelectionCallsObserved : List Nat
  /-- Positive-control readback: a checksum of the complete pattern/action and realised
  context tape presented to the scorer at each nominal temperature.  The replay control
  requires the same nonzero checksum at every level. -/
  controlReplayChecksumsObserved : List Nat
  results : List ArmResult
  /-- v2: now actually consumed, via `evidenceOf` below. In v1 this field existed
  and nothing read it, so the comparative claim's obligation was decorative. -/
  armOutputsDiffer : Bool
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
  ls.all (fun r => seedsPerCell ≤ r.seedsObserved)

def armWellFormed (t : Trace) (name : String) : Bool :=
  match t.results.find? (fun a => a.armName == name) with
  | some a => levelsWellFormed a.levels
  | none => false

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
  (t.temperaturesObserved == temperatureBp) &&
  (t.referencePredictorObserved == registeredReferencePredictor) &&
  controlRouteClosed t &&
  armNames.all (armWellFormed t) &&
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
        t.sourceRevisionBound = true ∧ t.inputChecksumBound = true ∧
        traceComplete t = true
      check := fun t =>
        t.sourceRevisionBound && t.inputChecksumBound && traceComplete t
      check_sound := by
        intro t h
        simp only [Bool.and_eq_true] at h
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

/-! ## Evidence

-- v2: `armsSeparable` is discharged by `Evidence.armsShownDistinct`, and v1 never
-- connected that to anything observed. It is now derived from the trace. -/

def evidenceOf (t : Trace) : Evidence where
  toolchainExercised := t.toolchainExercised
  codeIdentityAsserted := t.codeIdentityAsserted
  teardownExercised := t.teardownExercised
  armsShownDistinct := t.armOutputsDiffer

/-! ## Cost

-- v2: stated as a product with no division, which is also what made v1's
-- `norm_num` goal unprovable. 4 arms x 7 levels x 60 seeds = 1680 runs; the rate is
-- 121 runs/min MEASURED WITHOUT retained scoring or annealing, so a timed pilot is
-- required by `pilotRateMustBeRemeasured` before this estimate may be relied on. -/

def totalRuns : Nat := 4 * 7 * 60
def measuredRunsPerMinute : Nat := 121
def budgetMinutes : Nat := 30

theorem totalRuns_eq : totalRuns = 1680 := by decide

theorem within_declared_cap : totalRuns ≤ budgetMinutes * measuredRunsPerMinute := by
  decide

/-- The rate above was measured under different instrumentation. Registering it as
sufficient is not the same as having measured it here. -/
def pilotRateMustBeRemeasured : Prop :=
  ∃ observedRunsPerMinute : Nat,
    totalRuns ≤ budgetMinutes * observedRunsPerMinute

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
  the measured floor. -/
  | interiorMinimumWithStructure
  /-- v2: new. Interior minimum, but still in transient decline at the minimiser. -/
  | interiorMinimumStillTransient
  /-- Interior minimum whose field does not clear the measured confetti floor. -/
  | interiorMinimumWithoutStructure
  /-- Genuinely monotone across the ladder: cooling buys nothing. -/
  | monotone
  /-- v2: new. Non-monotone with no strict interior minimum -- ties, or a minimum
  at an endpoint. v1 reported these as `monotone`, which was false. -/
  | noStrictInteriorMinimum
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
          let ss := arm.levels.map (·.referenceLogLossBp)
          match strictInteriorMinimum ss with
          | none => if isMonotone ss then Outcome.monotone
                    else Outcome.noStrictInteriorMinimum
          | some best =>
              match arm.levels.find? (fun r => r.referenceLogLossBp == best),
                    confettiReference t with
              | some r, some confetti =>
                  if !r.latePlateau then Outcome.interiorMinimumStillTransient
                  else if confetti.entropyBp + structuralMarginBp ≤ r.entropyBp ∧
                          confetti.autocorrelationBp + structuralMarginBp
                            ≤ r.autocorrelationBp
                  then Outcome.interiorMinimumWithStructure
                  else Outcome.interiorMinimumWithoutStructure
              | _, _ => Outcome.incomplete
    | _, _ => Outcome.incomplete

def decisionRule : DecisionRule Trace Outcome where
  name := "interior reference-score minimum, stationary, above the measured floor"
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

def completenessStop : StopRule Trace where
  name := "a declared cell is missing or under-seeded"
  fires := fun t => traceComplete t = false
  check := fun t => !traceComplete t
  check_iff := by
    intro t; constructor
    · intro h; simpa using h
    · intro h; simpa using h

/-! ## The registration -/

noncomputable def registration (t : Trace) : Registration Trace where
  name := "exotype-6e-cooling-reference-scored"
  claim := .comparative
  arms := [fixedCooling t, annealedCooling t, noSelection,
    selectionBypassedReplayControl t]
  flags := [settingsHonoured]
  estimatedCost := (totalRuns : ℝ)
  budgetCap := ((budgetMinutes * measuredRunsPerMinute : Nat) : ℝ)
  teardownDeadline := some 90

def replication : ReplicationPlan Nat :=
  ReplicationPlan.confirmation
    { name := "exotype-6c-c5-mixed-field", nameNonempty := by decide }
    pilotUnits confirmationUnits (by decide) (by decide) units_disjoint
    (VariationPlan.measured
      { name := "control-vs-control reference log score at fixed tau"
        nameNonempty := by decide })

noncomputable def prospective (t : Trace) :
    ProspectiveRegistration Nat Trace Outcome where
  base := registration t
  replication := replication
  stopRules := [deadlineStop, instrumentStop, completenessStop]
  stopRulesNonempty := by simp
  decision := decisionRule

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
