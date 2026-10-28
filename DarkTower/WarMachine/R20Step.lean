import DarkTower.WarMachine.R20Run
import DarkTower.WarMachine.CascadeEFE
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Sort

/-!
# R20 as a computed step function: carried counts

This module contains slices 1 and 2 of the R20 reconstruction.  `step` computes each click and the
state handed to its successor; `run` folds `step` from `init`.  Evidence counts
follow Friston 2017, equation 2.7.  Learned terminal-class preferences follow
the preference-count update described by Smith, Friston & Whyte 2022.

Precision follows Friston 2017 equation 2.7's fixed-count numerical iteration;
valence follows the update cited by `R20Run` from Hesp et al. 2021, pp. 286–288.
The candidate field and Giraffe facts arrive as observations; `Click` records
only the selection computed from them.
-/

namespace DarkTower.WarMachine.R20Step

open scoped BigOperators
open R15TemporalHierarchy

abbrev Hidden := R20Certificate.Hidden
abbrev ProcessObservation := R20Certificate.Observation
abbrev EndingClass := CTauClassPreference.EndingClass
abbrev CCounts := CTauClassPreference.Distribution
abbrev PatternIdentity := R20Run.PatternIdentity
abbrev Valence := R20Run.Valence
abbrev Candidate := R15InjuryTier.Candidate
abbrev Target := R15StrategicTarget.Target
abbrev TargetRelation := CTauClassPreference.TargetRelation

variable {Policy : Type} [DecidableEq Policy] [Fintype Policy] [Nonempty Policy]

/-- Facts recomputed each click by `futon3c.giraffe.pass`: readiness from need
edges, one-step unblocks, and the transitive dependency cone.  Readiness is
never stored on the task (M-giraffe; Joe, 2026-10-26). -/
inductive ReadinessStatus where
  | ready | notReady | undetermined
  deriving DecidableEq, Fintype, Nonempty

inductive TaskState where
  | doable | blocked
  deriving DecidableEq, Fintype, Nonempty

inductive ReadyGain where
  | none | one | several
  deriving DecidableEq, Fintype, Nonempty

abbrev OuterOutcome := EndingClass × ReadyGain

structure GiraffeFacts where
  status : ReadinessStatus
  unblocks : ℕ
  cone : ℕ

def GiraffeFacts.ready (facts : GiraffeFacts) : Bool := facts.status = .ready

def readyGain : ℕ → ReadyGain
  | 0 => .none
  | 1 => .one
  | _ => .several

theorem sum_taskState (f : TaskState → ℝ) :
    ∑ state, f state = f .doable + f .blocked := by
  rw [show (Finset.univ : Finset TaskState) = {.doable, .blocked} by
    ext x; fin_cases x <;> simp]
  simp [add_comm]

theorem sum_readyGain (f : ReadyGain → ℝ) :
    ∑ gain, f gain = f .none + f .one + f .several := by
  rw [show (Finset.univ : Finset ReadyGain) = {.none, .one, .several} by
    ext x; fin_cases x <;> simp]
  simp [add_assoc]

theorem card_taskState : Fintype.card TaskState = 2 := by decide
theorem card_readyGain : Fintype.card ReadyGain = 3 := by decide

/-- Gates and orders are the roles in the task-selection README.  The named
constructors express `only-what-can-start-now` and
`what-others-wait-on-first`. -/
inductive SelectionStep where
  /-- A general task-selection README gate. -/
  | gate (keep : Candidate → Bool)
  /-- A general task-selection README stable ascending order. -/
  | order (key : Candidate → ℚ)
  /-- `only-what-can-start-now`: retain Giraffe-ready candidates. -/
  | readyGate
  /-- `what-others-wait-on-first`: most direct unblocks first. -/
  | byUnblocks
  /-- `what-others-wait-on-first`: largest transitive cone first. -/
  | byCone

/-- A task-selection policy is a cascade of gates and stable orders. -/
abbrev SelectionCascade := List SelectionStep

/-- Apply one task-selection step using the current Giraffe pass. -/
noncomputable def applySelectionStep (facts : Target → GiraffeFacts)
    (field : List Candidate) : SelectionStep → List Candidate
  | .gate keep => field.filter keep
  | .order key => field.insertionSort (fun a b => key a ≤ key b)
  | .readyGate => field.filter (fun candidate => (facts candidate.target).ready)
  | .byUnblocks => field.insertionSort
      (fun a b => (facts b.target).unblocks ≤ (facts a.target).unblocks)
  | .byCone => field.insertionSort
      (fun a b => (facts b.target).cone ≤ (facts a.target).cone)

/-- Apply a task-selection cascade from left to right. -/
noncomputable def applySelectionCascade (cascade : SelectionCascade)
    (facts : Target → GiraffeFacts) (field : List Candidate) : List Candidate :=
  cascade.foldl (applySelectionStep facts) field

/-- The task selected by a cascade, if its gates leave any candidate. -/
noncomputable def cascadePick (cascade : SelectionCascade) (facts : Target → GiraffeFacts)
    (field : List Candidate) : Option Candidate :=
  (applySelectionCascade cascade facts field).head?

/-- Ready candidates first; among them most one-step unblocks first, with cone
as the stable secondary key.  `byUnblocks` is last because the last stable
sort is the primary key. -/
def whatOthersWaitOnFirst : SelectionCascade := [.readyGate, .byCone, .byUnblocks]

/-- Total rational Beta counts.  Totality makes Smith, Friston & Whyte 2022
§4 Eqs. 34 and 37 forgetting reach keys absent from a finite slow-state list. -/
abbrev RatedCounts (Key : Type) := Key → ℚ × ℚ

/-- Embed the existing integer R15 prior kit into total rational counts. -/
def ofSlowState {Key : Type} [DecidableEq Key]
    (s : R15TemporalHierarchy.SlowState Key) : RatedCounts Key := fun key =>
  ((R15TemporalHierarchy.countsFor s key).alpha,
   (R15TemporalHierarchy.countsFor s key).beta)

/-- Fixed makeup for one run.  `d₀` is the initial evidence concentration
(Friston 2017, equation 2.7); `κ` is the preference-count strength used by the
Smith, Friston & Whyte 2022 preference update. -/
structure Makeup (Policy : Type) where
  A : EvidenceFromTheProcess.Likelihood Hidden ProcessObservation
  d₀ : Hidden → ℝ
  habit₀ : SlowState Policy
  pattern : PatternIdentity
  theta₀ : SlowState PatternIdentity
  kappa : ℚ
  kappa_pos : 0 < kappa
  stateKit : ReadinessStatus → TaskState → ℚ
  stateKit_pos : ∀ status state, 0 < stateKit status state
  gainKit : ReadyGain → ℚ
  gainKit_pos : ∀ gain, 0 < gainKit gain
  /-- Evidence learning rate η_d; Smith, Friston & Whyte 2022 §4 Eq. 34. -/
  etaD : ℝ
  etaD_pos : 0 < etaD
  /-- Evidence forgetting rate ω_d; Smith, Friston & Whyte 2022 §4 Eq. 34. -/
  omegaD : ℝ
  omegaD_pos : 0 < omegaD
  omegaD_le_one : omegaD ≤ 1
  /-- Preference learning rate η_c; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  etaC : ℚ
  etaC_pos : 0 < etaC
  /-- Preference forgetting rate ω_c; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  omegaC : ℚ
  omegaC_pos : 0 < omegaC
  omegaC_le_one : omegaC ≤ 1
  /-- Habit learning rate η_h; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  etaHabit : ℚ
  etaHabit_pos : 0 < etaHabit
  /-- Habit forgetting rate ω_h; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  omegaHabit : ℚ
  omegaHabit_pos : 0 < omegaHabit
  omegaHabit_le_one : omegaHabit ≤ 1
  /-- Pattern learning rate η_θ; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  etaTheta : ℚ
  etaTheta_pos : 0 < etaTheta
  /-- Pattern forgetting rate ω_θ; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  omegaTheta : ℚ
  omegaTheta_pos : 0 < omegaTheta
  omegaTheta_le_one : omegaTheta ≤ 1
  /-- Affective level used by the Hesp et al. 2021, pp. 286–288 valence update. -/
  L : R20Run.AffectiveLevel
  /-- Initial valence belief for the Hesp et al. 2021, pp. 286–288 update. -/
  q₀ : Valence → ℝ
  /-- Fixed numerical iteration count for Friston 2017 equation 2.7. -/
  precisionIterations : ℕ
  cascades : List SelectionCascade
  cascades_nonempty : cascades ≠ []
  relation : Target → Target → TargetRelation
  initialFocus : Nat

/-- State carried from one click to the next.  `d` is the concentration from
Friston 2017, equation 2.7; `c` is the learned preference concentration from
Smith, Friston & Whyte 2022. -/
structure State (Policy : Type) where
  d : Hidden → ℝ
  habit : RatedCounts Policy
  theta : RatedCounts PatternIdentity
  c : CCounts
  stateCounts : ReadinessStatus → TaskState → ℚ
  gainCounts : ReadyGain → ℚ
  valence : Valence → ℝ
  previousFocus : Nat
  runId : Nat

/-- Exogenous facts arriving at one click.  Habit and pattern outcomes feed the
existing R15/PatternTheta updates; the ending class feeds the Smith, Friston &
Whyte 2022 preference-count update. -/
structure Observation (Policy : Type) where
  observation : ProcessObservation
  habitOutcome : FastOutcome Policy
  thetaOutcomes : List (FastOutcome PatternIdentity)
  endingClass : EndingClass
  focus : Nat
  /-- Habit evidence supplied externally in this slice; deriving it from learned habit is later work. -/
  E : Policy → ℝ
  /-- Expected free energy supplied externally in this slice; model computation is later work. -/
  G : Policy → ℝ
  /-- Free energy supplied externally in this slice; model computation is later work. -/
  F : Policy → ℝ
  /-- Candidate field supplied externally in this slice; producing it is later work. -/
  field : List Candidate
  /-- Giraffe facts supplied externally in this slice and recomputed for this click. -/
  facts : Target → GiraffeFacts

/-- Rows produced by one computed click.  Evidence uses Friston 2017,
equation 2.7; `C` is the normalized Smith, Friston & Whyte 2022 preference
count. -/
structure Click (Policy : Type) where
  d : Hidden → ℝ
  evidence : R20Certificate.EvidenceRow
  habitBefore : RatedCounts Policy
  habitAfter : RatedCounts Policy
  thetaBefore : RatedCounts PatternIdentity
  thetaAfter : RatedCounts PatternIdentity
  c : CCounts
  C : CTauClassPreference.Distribution
  precision : PrecisionFromObservation.TickRecord Policy
  valence : Valence → ℝ
  selection : Option R20FocusedSelection.OuterSelection
  cascadeIndex : Nat
  cascadeScores : List EReal
  previousFocus : Nat
  focus : Nat
  runId : Nat

/-- The 55/35/5/5 prior kit, with no mass on `notYetEvaluated`. -/
def kit : CCounts
  | .focused => 55 / 100
  | .related => 35 / 100
  | .unrelated => 5 / 100
  | .stopTheLine => 5 / 100
  | .notYetEvaluated => 0

/-- Initial learned-preference counts, `κ · (55,35,5,5)/100`, following
Smith, Friston & Whyte 2022. -/
def initialC (m : Makeup Policy) : CCounts := fun ending => m.kappa * kit ending

/-- Add the Smith, Friston & Whyte 2022 unit preference count for a terminal
ending.  `notYetEvaluated` is not a terminal outcome and adds nothing. -/
def addEnding (c : CCounts) (observed : EndingClass) : CCounts := fun ending =>
  c ending + if observed = ending ∧ ending ≠ .notYetEvaluated then 1 else 0

/-- One Smith, Friston & Whyte 2022 preference-count observation. -/
def endingDelta (observed : EndingClass) : CCounts := fun ending =>
  if observed = ending ∧ ending ≠ .notYetEvaluated then 1 else 0

/-- Normalize learned Smith, Friston & Whyte 2022 preference counts. -/
def normalizeC (c : CCounts) : CTauClassPreference.Distribution := fun ending =>
  c ending / CTauClassPreference.totalMass c

open CascadeEFE Holes

/-- Normalise strictly positive rational counts. -/
noncomputable def outerCountKernel {X : Type} [Fintype X] [Nonempty X]
    (counts : X → ℚ) (positive : ∀ x, 0 < counts x) : ProbabilityKernel Unit X :=
  finiteKernel (fun _ x => (counts x : ℝ) / (∑ y, counts y : ℚ))
    (by
      intro _ x
      exact div_nonneg (Rat.cast_nonneg.mpr (le_of_lt (positive x)))
        (Rat.cast_nonneg.mpr (Finset.sum_nonneg fun y _ => le_of_lt (positive y))))
    (by
      intro
      rw [← Finset.sum_div]
      norm_cast
      apply div_self
      exact ne_of_gt (Finset.sum_pos (fun x _ => positive x) Finset.univ_nonempty))

/-- Entropy of a binary reach/failure observation. -/
noncomputable def binaryEntropy (r : ℚ) : ℝ :=
  -(if (r : ℝ) = 0 then 0 else (r : ℝ) * Real.log r) -
    (if 1 - (r : ℝ) = 0 then 0 else (1 - r : ℚ) * Real.log (1 - r))

def boundedReach (reach : ℚ) : ℚ := max 0 (min 1 reach)

theorem boundedReach_nonnegative (reach : ℚ) : 0 ≤ boundedReach reach := le_max_left _ _
theorem boundedReach_le_one (reach : ℚ) : boundedReach reach ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)
theorem boundedReach_eq (reach : ℚ) (nonnegative : 0 ≤ reach) (le_one : reach ≤ 1) :
    boundedReach reach = reach := by simp [boundedReach, nonnegative, le_one]

/-- Observation kernel for one picked task.  Reach is clamped to `[0,1]` at
this exogenous-input boundary; in-range candidate reaches are unchanged. -/
noncomputable def pickedOuterKernel (landing : OuterOutcome) (rawReach : ℚ) :
    ProbabilityKernel TaskState OuterOutcome :=
  let reach := boundedReach rawReach
  finiteKernel (fun state outcome => match state with
    | .blocked => if outcome = (.stopTheLine, .none) then 1 else 0
    | .doable => if landing = (.stopTheLine, .none) then
        if outcome = (.stopTheLine, .none) then 1 else 0
      else if outcome = landing then (reach : ℝ)
      else if outcome = (.stopTheLine, .none) then (1 - reach : ℚ) else 0)
    (by
      intro state outcome
      cases state <;> split_ifs <;> norm_num
      all_goals first | exact_mod_cast boundedReach_nonnegative rawReach |
        exact_mod_cast boundedReach_le_one rawReach)
    (by
      intro state
      cases state with
      | blocked => simp
      | doable =>
        by_cases h : landing = (.stopTheLine, .none)
        · simp [h]
        · classical
          simp only [h, if_false]
          have point_sum (a : OuterOutcome) (v : ℝ) :
            ∑ x, (if x = a then v else 0) = v := by
            rw [Finset.sum_ite_eq' Finset.univ a]
            simp
          rw [show (∑ x : OuterOutcome,
            if x = landing then (reach : ℝ)
            else if x = (.stopTheLine, .none) then (1 - reach : ℚ) else 0) =
            (∑ x, if x = landing then (reach : ℝ) else 0) +
            (∑ x, if x = (CTauClassPreference.EndingClass.stopTheLine, ReadyGain.none)
              then (1 - reach : ℝ) else 0) by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x = landing <;>
              by_cases hs : x = (.stopTheLine, .none) <;> simp_all]
          rw [point_sum, point_sum]
          norm_num)

noncomputable def stoppedOuterKernel : ProbabilityKernel TaskState OuterOutcome :=
  finiteKernel (fun _ outcome => if outcome = (.stopTheLine, .none) then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro; simp)

/-- Product of two learned marginals.  No Q9 factorisation claim is made here. -/
noncomputable def outerPreferenceKernel (C : CTauClassPreference.Distribution)
    (C_probability : CTauClassPreference.ProbabilityDistribution C)
    (gainCounts : ReadyGain → ℚ) (gainCounts_pos : ∀ gain, 0 < gainCounts gain) :
    ProbabilityKernel Unit OuterOutcome :=
  let gain := outerCountKernel gainCounts gainCounts_pos
  finiteKernel (fun _ outcome => C outcome.1 * gain.mass () outcome.2)
    (by
      intro _ outcome
      exact mul_nonneg (by exact_mod_cast C_probability.1 outcome.1)
        (gain.nonnegative () outcome.2))
    (by
      intro
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, kernel_sum]
      simp only [mul_one]
      simp only [R15InjuryTier.sum_endingClass]
      exact_mod_cast C_probability.2)

theorem outerPreferenceKernel_mass_pos (C : CTauClassPreference.Distribution)
    (C_probability : CTauClassPreference.ProbabilityDistribution C)
    (C_pos : ∀ ending, 0 < C ending)
    (gainCounts : ReadyGain → ℚ) (gainCounts_pos : ∀ gain, 0 < gainCounts gain)
    (outcome : OuterOutcome) :
    0 < (outerPreferenceKernel C C_probability gainCounts gainCounts_pos).mass () outcome := by
  unfold outerPreferenceKernel outerCountKernel
  dsimp only [finiteKernel]
  apply mul_pos
  · exact_mod_cast C_pos outcome.1
  · apply div_pos
    · exact_mod_cast gainCounts_pos outcome.2
    · exact_mod_cast Finset.sum_pos (fun gain _ => gainCounts_pos gain) Finset.univ_nonempty

/-- The task-level hidden-state and observation kernels for one cascade.  They
read only whole-task facts: readiness status, unblocks, reach, and target relation. -/
noncomputable def outerModel (focus : Target) (relation : Target → Target → TargetRelation)
    (facts : Target → GiraffeFacts) (field : List Candidate)
    (stateCounts : ReadinessStatus → TaskState → ℚ)
    (stateCounts_pos : ∀ status state, 0 < stateCounts status state)
    (cascade : SelectionCascade) :
    ProbabilityKernel Unit TaskState × ProbabilityKernel TaskState OuterOutcome :=
  match cascadePick cascade facts field with
  | none => (point .blocked, stoppedOuterKernel)
  | some candidate =>
      let landing := match R15StrategicTarget.outcomeClass focus relation (some candidate.target) with
        | some ending => (ending, readyGain (facts candidate.target).unblocks)
        | none => (.stopTheLine, .none)
      (outerCountKernel (stateCounts (facts candidate.target).status) (stateCounts_pos _),
        pickedOuterKernel landing candidate.reach)

/-- Outer expected free energy.  As with `classRisk`, inadmissibility is `⊤`. -/
noncomputable def outerScore (focus : Target) (relation : Target → Target → TargetRelation)
    (facts : Target → GiraffeFacts) (field : List Candidate)
    (stateCounts : ReadinessStatus → TaskState → ℚ)
    (stateCounts_pos : ∀ status state, 0 < stateCounts status state)
    (C : CTauClassPreference.Distribution)
    (C_probability : CTauClassPreference.ProbabilityDistribution C)
    (gainCounts : ReadyGain → ℚ) (gainCounts_pos : ∀ gain, 0 < gainCounts gain)
    (cascade : SelectionCascade) : EReal := by
  classical
  let model := outerModel focus relation facts field stateCounts stateCounts_pos cascade
  let preference := outerPreferenceKernel C C_probability gainCounts gainCounts_pos
  exact if h : PreferenceRiskSeparation.riskAdmissible (push model.1 model.2) preference then
    (stepG model.1 model.2 preference h : ℝ)
  else ⊤

theorem outerScore_eq_stepG_of_finite (focus : Target)
    (relation : Target → Target → TargetRelation) (facts : Target → GiraffeFacts)
    (field : List Candidate) (stateCounts : ReadinessStatus → TaskState → ℚ)
    (stateCounts_pos : ∀ status state, 0 < stateCounts status state)
    (C : CTauClassPreference.Distribution)
    (C_probability : CTauClassPreference.ProbabilityDistribution C)
    (gainCounts : ReadyGain → ℚ) (gainCounts_pos : ∀ gain, 0 < gainCounts gain)
    (cascade : SelectionCascade)
    (finite : outerScore focus relation facts field stateCounts stateCounts_pos C C_probability
      gainCounts gainCounts_pos cascade ≠ ⊤) :
    ∃ h : PreferenceRiskSeparation.riskAdmissible
        (push (outerModel focus relation facts field stateCounts stateCounts_pos cascade).1
          (outerModel focus relation facts field stateCounts stateCounts_pos cascade).2)
        (outerPreferenceKernel C C_probability gainCounts gainCounts_pos),
      outerScore focus relation facts field stateCounts stateCounts_pos C C_probability
          gainCounts gainCounts_pos cascade =
        (stepG
          (outerModel focus relation facts field stateCounts stateCounts_pos cascade).1
          (outerModel focus relation facts field stateCounts stateCounts_pos cascade).2
          (outerPreferenceKernel C C_probability gainCounts gainCounts_pos) h : ℝ) := by
  classical
  simp only [outerScore] at finite ⊢
  split_ifs with h
  · exact ⟨h, rfl⟩
  · simp [h] at finite

set_option maxHeartbeats 1000000 in
theorem pickedOuterKernel_ambiguity (q : ProbabilityKernel Unit TaskState)
    (landing : OuterOutcome) (reach : ℚ) (reach_nonnegative : 0 ≤ reach)
    (reach_le_one : reach ≤ 1)
    (landing_ne_stop : landing ≠ (.stopTheLine, .none)) :
    CascadeEFE.ambiguity q (pickedOuterKernel landing reach) =
      q.mass () .doable * binaryEntropy reach := by
  classical
  have sum_task (f : TaskState → ℝ) :
      ∑ x, f x = f .doable + f .blocked := by
    rw [show (Finset.univ : Finset TaskState) = {.doable, .blocked} by
      ext x; fin_cases x <;> simp]
    simp [add_comm]
  have sum_gain (f : ReadyGain → ℝ) :
      ∑ x, f x = f .none + f .one + f .several := by
    rw [show (Finset.univ : Finset ReadyGain) = {.none, .one, .several} by
      ext x; fin_cases x <;> simp]
    simp [add_assoc]
  rcases landing with ⟨ending, gain⟩
  fin_cases ending <;> fin_cases gain <;>
    simp_all [CascadeEFE.ambiguity, binaryEntropy, CascadeEFE.entropy,
      pickedOuterKernel, finiteKernel, Fintype.sum_prod_type,
      R15InjuryTier.sum_endingClass, sum_task, sum_gain,
      boundedReach_eq reach reach_nonnegative reach_le_one] <;> ring
  all_goals simp

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
/-- The indexed cascade menu used to retain menu-order tie breaking. -/
def indexedCascades (m : Makeup Policy) : List (SelectionCascade × Nat) := m.cascades.zipIdx

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem indexedCascades_nonempty (m : Makeup Policy) : indexedCascades m ≠ [] := by
  simpa [indexedCascades] using m.cascades_nonempty

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
/-- Score against the outer model carried by `s`.  Arbitrary `State` values do
not carry admissibility proofs, so malformed carried counts receive `⊤`; states
produced from a `Makeup` kit take the `outerScore` branch. -/
noncomputable def carriedOuterScore (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy) (cascade : SelectionCascade) : EReal := by
  classical
  exact if stateCounts_pos : ∀ status state, 0 < s.stateCounts status state then
    if C_probability : CTauClassPreference.ProbabilityDistribution (normalizeC s.c) then
      if gainCounts_pos : ∀ gain, 0 < s.gainCounts gain then
        outerScore o.focus m.relation o.facts o.field s.stateCounts stateCounts_pos
          (normalizeC s.c) C_probability s.gainCounts gainCounts_pos cascade
      else ⊤
    else ⊤
  else ⊤

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem carriedOuterScore_eq_of_cascadePick_eq (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy) {left right : SelectionCascade}
    (same : cascadePick left o.facts o.field = cascadePick right o.facts o.field) :
    carriedOuterScore m s o left = carriedOuterScore m s o right := by
  classical
  unfold carriedOuterScore outerScore outerModel
  split_ifs <;> simp_all

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
/-- First minimum-outer-G cascade.  Equal scores are resolved by menu order only
so `step` is a function; such ties are a defect for better evidence to remove,
not a selection rule. -/
noncomputable def chosenCascadeEntry (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy) : SelectionCascade × Nat :=
  (indexedCascades m).argmin
    (fun entry => carriedOuterScore m s o entry.1) |>.get
      (by
        cases h : (indexedCascades m).argmin
          (fun entry => carriedOuterScore m s o entry.1) with
        | none => exact False.elim (indexedCascades_nonempty m (List.argmin_eq_none.mp h))
        | some _ => rfl)

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem chosenCascadeEntry_mem_argmin (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy) :
    chosenCascadeEntry m s o ∈ (indexedCascades m).argmin
      (fun entry => carriedOuterScore m s o entry.1) := by
  unfold chosenCascadeEntry
  exact Option.some_get _ |>.symm

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem chosenCascadeEntry_mem (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy) : chosenCascadeEntry m s o ∈ indexedCascades m :=
  List.argmin_mem (chosenCascadeEntry_mem_argmin m s o)

theorem applySelectionStep_mem {facts : Target → GiraffeFacts} {field : List Candidate}
    {step : SelectionStep} {c : Candidate}
    (present : c ∈ applySelectionStep facts field step) : c ∈ field := by
  cases step with
  | gate keep => exact (List.mem_filter.mp (by simpa [applySelectionStep] using present)).1
  | order key => simpa [applySelectionStep, List.mem_insertionSort] using present
  | readyGate =>
      exact (show c ∈ field ∧ (facts c.target).ready = true by
        simpa [applySelectionStep] using present).1
  | byUnblocks => simpa [applySelectionStep, List.mem_insertionSort] using present
  | byCone => simpa [applySelectionStep, List.mem_insertionSort] using present

theorem applySelectionCascade_mem {cascade : SelectionCascade} {facts : Target → GiraffeFacts}
    {field : List Candidate} {c : Candidate}
    (present : c ∈ applySelectionCascade cascade facts field) : c ∈ field := by
  induction cascade generalizing field with
  | nil => simpa [applySelectionCascade] using present
  | cons step cascade ih =>
      apply applySelectionStep_mem (facts := facts) (step := step)
      apply ih
      simpa [applySelectionCascade] using present

/-- A `classPreference`-shaped schedule whose terminal value is learned C. -/
def learnedClassPreference (C : CTauClassPreference.Distribution)
    (horizon tau : Nat) : CTauClassPreference.Distribution :=
  if tau = horizon then C else CTauClassPreference.waitingPreference

/-- Fixed-count numerical iteration of Friston 2017 equation 2.7, matching
SPM's bounded routine without claiming convergence. -/
noncomputable def iteratePrecision (iterations : ℕ) (betaPrior : ℝ) (E G F : Policy → ℝ) : ℝ :=
  (fun beta => PrecisionFromObservation.firstIterate betaPrior beta E G F)^[iterations]
    betaPrior

/-- Decay every total Beta count by ω once.  The rate is the forgetting rate
of Smith, Friston & Whyte 2022 §4 Eqs. 34 and 37. -/
def decayRated {Key : Type} (omega : ℚ) (counts : RatedCounts Key) : RatedCounts Key :=
  fun key => (omega * (counts key).1, omega * (counts key).2)

/-- Add η to one total Beta count after decay.  η is the learning rate of
Smith, Friston & Whyte 2022 §4 Eqs. 34 and 37. -/
def addRated {Key : Type} [DecidableEq Key] (eta : ℚ) (counts : RatedCounts Key)
    (key : Key) (succeeded : Bool) : RatedCounts Key := fun query =>
  if query = key then
    if succeeded then ((counts query).1 + eta, (counts query).2)
    else ((counts query).1, (counts query).2 + eta)
  else counts query

/-- Habit update with explicit Smith, Friston & Whyte 2022 §4 Eqs. 34 and 37
learning η and forgetting ω: decay all policies, then count the observation. -/
def advanceRated {Key : Type} [DecidableEq Key] (eta omega : ℚ)
    (before : RatedCounts Key) (outcome : FastOutcome Key) : RatedCounts Key :=
  addRated eta (decayRated omega before) outcome.policy outcome.succeeded

/-- Pattern update with explicit Smith, Friston & Whyte 2022 §4 Eqs. 34 and 37
rates: decay all keys once, then add η for each witnessed matching outcome in
the same order as `PatternTheta.advanceWitnessed`. -/
def advanceWitnessedRated (eta omega : ℚ) (pattern : PatternIdentity)
    (before : RatedCounts PatternIdentity) (outcomes : List (FastOutcome PatternIdentity)) :
    RatedCounts PatternIdentity :=
  (PatternTheta.witnessedOutcomes pattern outcomes).foldl
    (fun counts succeeded => addRated eta counts pattern succeeded)
    (decayRated omega before)

/-- Preference update with explicit Smith, Friston & Whyte 2022 §4 Eqs. 34
and 37 learning η and forgetting ω. -/
def advanceC (eta omega : ℚ) (before : CCounts) (ending : EndingClass) : CCounts :=
  omega • before + eta • endingDelta ending

/-- Initial carried state.  Evidence concentration follows Friston 2017,
equation 2.7; preference concentration follows Smith, Friston & Whyte 2022. -/
def init (m : Makeup Policy) : State Policy where
  d := m.d₀
  habit := ofSlowState m.habit₀
  theta := ofSlowState m.theta₀
  c := initialC m
  stateCounts := m.stateKit
  gainCounts := m.gainKit
  valence := m.q₀
  previousFocus := m.initialFocus
  runId := 0

/-- The evidence prior is the mean of the current Friston 2017 equation 2.7
concentration. -/
noncomputable def evidencePrior (s : State Policy) : EvidenceFromTheProcess.Belief Hidden :=
  fun hidden => s.d hidden / ∑ x, s.d x

/-- Compute one click and its successor.  The evidence concentration update is
Friston 2017 equation 2.7; the C-count update is Smith, Friston & Whyte 2022.
Slice 3d carries `stateCounts` and `gainCounts` unchanged; their updates are 3e. -/
noncomputable def step (m : Makeup Policy) (s : State Policy) (o : Observation Policy) :
    Click Policy × State Policy :=
  let prior := evidencePrior s
  let posterior := EvidenceFromTheProcess.posterior prior m.A o.observation
  let habitAfter := advanceRated m.etaHabit m.omegaHabit s.habit o.habitOutcome
  let thetaAfter := advanceWitnessedRated m.etaTheta m.omegaTheta m.pattern s.theta o.thetaOutcomes
  let cAfter := advanceC m.etaC m.omegaC s.c o.endingClass
  let betaPrior := R20Run.descend m.L s.valence
  let betaPosterior := iteratePrecision m.precisionIterations betaPrior o.E o.G o.F
  let precision : PrecisionFromObservation.TickRecord Policy :=
    { E := o.E, G := o.G, F := o.F
      prior := PrecisionFromObservation.priorPolicy betaPosterior o.E o.G
      posterior := PrecisionFromObservation.posteriorPolicy betaPosterior o.E o.G o.F
      betaPrior := betaPrior, betaPosterior := betaPosterior }
  let valenceAfter := R20Run.predict m.L
    (R20Run.valenceUpdate m.L s.valence betaPrior betaPosterior)
  let chosen := chosenCascadeEntry m s o
  let scores := m.cascades.map
    (carriedOuterScore m s o)
  let selection := (cascadePick chosen.1 o.facts o.field).map fun candidate =>
    ({ candidates := o.field, selected := candidate } : R20FocusedSelection.OuterSelection)
  ({ d := s.d
     evidence := ⟨prior, m.A, o.observation, posterior⟩
     habitBefore := s.habit
     habitAfter := habitAfter
     thetaBefore := s.theta
     thetaAfter := thetaAfter
     c := s.c
     C := normalizeC s.c
     precision := precision
     valence := s.valence
     selection := selection
     cascadeIndex := chosen.2
     cascadeScores := scores
     previousFocus := s.previousFocus
     focus := o.focus
     runId := s.runId },
   { d := m.omegaD • s.d + m.etaD • posterior
     habit := habitAfter
     theta := thetaAfter
     c := cAfter
     stateCounts := s.stateCounts
     gainCounts := s.gainCounts
     valence := valenceAfter
     previousFocus := o.focus
     runId := s.runId + 1 })

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem chosenCascade_score_le (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy) {cascade : SelectionCascade} (present : cascade ∈ m.cascades) :
    carriedOuterScore m s o (chosenCascadeEntry m s o).1 ≤
      carriedOuterScore m s o cascade := by
  obtain ⟨index, at_index⟩ := List.get_of_mem present
  have entry_present : (cascade, index.val) ∈ indexedCascades m := by
    let zippedIndex : Fin (indexedCascades m).length :=
      ⟨index.val, by simpa [indexedCascades] using index.isLt⟩
    apply List.mem_iff_get.mpr
    refine ⟨zippedIndex, ?_⟩
    simp only [indexedCascades, zippedIndex, List.get_eq_getElem, List.getElem_zipIdx,
      zero_add, Prod.mk.injEq, and_true]
    simpa only [List.get_eq_getElem] using at_index
  let scoreEntry := fun entry : SelectionCascade × Nat =>
    carriedOuterScore m s o entry.1
  change scoreEntry (chosenCascadeEntry m s o) ≤ scoreEntry (cascade, index.val)
  exact List.le_of_mem_argmin (f := scoreEntry) entry_present
    (chosenCascadeEntry_mem_argmin m s o)

theorem cascadePick_some_mem {cascade : SelectionCascade} {facts : Target → GiraffeFacts}
    {field : List Candidate} {candidate : Candidate}
    (picked : cascadePick cascade facts field = some candidate) :
    candidate ∈ field := by
  apply applySelectionCascade_mem
  apply List.mem_of_mem_head?
  simpa [cascadePick, Option.mem_def] using picked

/-- `what-others-wait-on-first` keeps only ready tasks and chooses a maximum
one-step unblock count; cone is the stable tie-breaker. -/
theorem whatOthersWaitOnFirst_pick {facts : Target → GiraffeFacts}
    {field : List Candidate} {candidate : Candidate}
    (picked : cascadePick whatOthersWaitOnFirst facts field = some candidate) :
    (facts candidate.target).ready = true ∧
      ∀ other ∈ field, (facts other.target).ready = true →
        (facts other.target).unblocks ≤ (facts candidate.target).unblocks := by
  let ready := field.filter (fun c => (facts c.target).ready)
  let coned := ready.insertionSort
    (fun a b => (facts b.target).cone ≤ (facts a.target).cone)
  let ranked := coned.insertionSort
    (fun a b => (facts b.target).unblocks ≤ (facts a.target).unblocks)
  have picked' : ranked.head? = some candidate := by
    simpa [cascadePick, applySelectionCascade, applySelectionStep,
      whatOthersWaitOnFirst, ready, coned, ranked] using picked
  have candidate_ranked : candidate ∈ ranked := List.mem_of_mem_head? picked'
  have candidate_ready : candidate ∈ ready := by
    simpa [ranked, coned, List.mem_insertionSort] using candidate_ranked
  have candidate_ready' := candidate_ready
  simp [ready] at candidate_ready'
  refine ⟨candidate_ready'.2, ?_⟩
  intro other other_field other_ready
  have other_in_ready : other ∈ ready := by
    simp [ready, other_field, other_ready]
  have other_in_ranked : other ∈ ranked := by
    simp [ranked, coned, List.mem_insertionSort, other_in_ready]
  have sorted : ranked.Pairwise
      (fun a b => (facts b.target).unblocks ≤ (facts a.target).unblocks) := by
    exact List.pairwise_insertionSort _ _
  cases hranked : ranked with
  | nil => simp [hranked] at picked'
  | cons head tail =>
      have head_eq : head = candidate := by simpa [hranked] using picked'
      subst head
      simpa [hranked] using sorted.rel_head other_in_ranked

/-- If Giraffe reports no ready task, the readiness gate leaves no pick. -/
theorem whatOthersWaitOnFirst_none_of_no_ready {facts : Target → GiraffeFacts}
    {field : List Candidate}
    (none_ready : ∀ candidate ∈ field, (facts candidate.target).ready = false) :
    cascadePick whatOthersWaitOnFirst facts field = none := by
  have filtered : field.filter (fun c => (facts c.target).ready) = [] := by
    by_contra nonempty
    obtain ⟨candidate, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    have retained := List.mem_filter.mp present
    rw [none_ready candidate retained.1] at retained
    exact Bool.noConfusion retained.2
  simp [cascadePick, applySelectionCascade, applySelectionStep,
    whatOthersWaitOnFirst, filtered]

omit [Nonempty Policy] in
theorem step_selection_some (m : Makeup Policy) (s : State Policy) (o : Observation Policy)
    (selection : R20FocusedSelection.OuterSelection)
    (selected : (step m s o).1.selection = some selection) :
    selection.selected ∈ o.field ∧ selection.candidates = o.field := by
  simp only [step] at selected
  cases picked : cascadePick (chosenCascadeEntry m s o).1 o.facts o.field with
  | none => simp [picked] at selected
  | some candidate =>
      simp [picked] at selected
      subst selection
      exact ⟨cascadePick_some_mem picked, rfl⟩

omit [Nonempty Policy] in
theorem step_selection_none_iff (m : Makeup Policy) (s : State Policy) (o : Observation Policy) :
    (step m s o).1.selection = none ↔
      cascadePick (chosenCascadeEntry m s o).1 o.facts o.field = none := by
  simp [step]

omit [Nonempty Policy] in
theorem step_scores_read_carried_C (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy) :
    (step m s o).1.cascadeScores = m.cascades.map
      (carriedOuterScore m s o) := by
  rfl

/-- Fold `step` from a supplied state, returning the computed clicks and final
state.  Its updates are exactly the Friston 2017 and Smith, Friston & Whyte
2022 updates in `step`. -/
noncomputable def runFrom (m : Makeup Policy) : State Policy → List (Observation Policy) →
    List (Click Policy) × State Policy
  | s, [] => ([], s)
  | s, o :: obs =>
      let next := step m s o
      let rest := runFrom m next.2 obs
      (next.1 :: rest.1, rest.2)

/-- Compute a run by folding `step` from `init m` (Friston 2017 equation 2.7;
Smith, Friston & Whyte 2022 preference learning). -/
noncomputable def run (m : Makeup Policy) (obs : List (Observation Policy)) :
    List (Click Policy) := (runFrom m (init m) obs).1

/-- State after a prefix of observations. -/
noncomputable def stateAfter (m : Makeup Policy) (obs : List (Observation Policy)) :
    State Policy := (runFrom m (init m) obs).2

/-- Smith, Friston & Whyte 2022 preference counts contributed by a prefix. -/
def endingCounts : List (Observation Policy) → CCounts
  | [] => 0
  | o :: obs => endingDelta o.endingClass + endingCounts obs

/-- Posteriors generated successively from Friston 2017 equation 2.7 counts. -/
noncomputable def posteriorHistoryFrom (m : Makeup Policy) :
    State Policy → List (Observation Policy) → List (Hidden → ℝ)
  | _, [] => []
  | s, o :: obs =>
      let p := EvidenceFromTheProcess.posterior (evidencePrior s) m.A o.observation
      p :: posteriorHistoryFrom m (step m s o).2 obs

/-- The Friston 2017 equation 2.7 posterior history from `init`. -/
noncomputable def posteriorHistory (m : Makeup Policy) (obs : List (Observation Policy)) :=
  posteriorHistoryFrom m (init m) obs

/-- Pointwise sum used by the Friston 2017 equation 2.7 closed form. -/
def sumBeliefs : List (Hidden → ℝ) → Hidden → ℝ
  | [] => 0
  | p :: ps => p + sumBeliefs ps

omit [Nonempty Policy] in
theorem posteriorHistoryFrom_length (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (posteriorHistoryFrom m s obs).length = obs.length := by
  induction obs generalizing s with
  | nil => rfl
  | cons o obs ih => simp [posteriorHistoryFrom, ih]

theorem addEnding_eq_add (c : CCounts) (ending : EndingClass) :
    addEnding c ending = c + endingDelta ending := by
  rfl

omit [Nonempty Policy] in
theorem runFrom_append_one (m : Makeup Policy) (s : State Policy)
    (pre : List (Observation Policy)) (o : Observation Policy) :
    (runFrom m s (pre ++ [o])).1 =
      (runFrom m s pre).1 ++ [(step m (runFrom m s pre).2 o).1] := by
  induction pre generalizing s with
  | nil => simp [runFrom]
  | cons x xs ih => simp [runFrom, ih]

/-- The power-weighted Smith, Friston & Whyte 2022 ending increments. -/
def geometricEndings (omega : ℚ) : List (Observation Policy) → CCounts
  | [] => 0
  | o :: obs => omega ^ obs.length • endingDelta o.endingClass + geometricEndings omega obs

/-- The power-weighted Friston 2017 equation 2.7 posterior increments. -/
def geometricBeliefs (omega : ℝ) : List (Hidden → ℝ) → Hidden → ℝ
  | [] => 0
  | p :: ps => omega ^ ps.length • p + geometricBeliefs omega ps

omit [Nonempty Policy] in
theorem stateAfterFrom_c (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.c =
      m.omegaC ^ obs.length • s.c + m.etaC • geometricEndings m.omegaC obs := by
  induction obs generalizing s with
  | nil => simp [runFrom, geometricEndings]
  | cons o obs ih =>
      rw [show (runFrom m s (o :: obs)).2 = (runFrom m (step m s o).2 obs).2 by rfl, ih]
      simp only [step, geometricEndings, List.length_cons, pow_succ]
      funext ending
      simp [advanceC]
      ring

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem fold_addEnding (base : CCounts) (obs : List (Observation Policy)) :
    obs.foldl (fun c o => addEnding c o.endingClass) base = base + endingCounts obs := by
  induction obs generalizing base with
  | nil => simp [endingCounts]
  | cons o obs ih =>
      rw [List.foldl_cons, ih]
      simp only [addEnding_eq_add]
      simp only [endingCounts]
      funext ending
      simp [endingDelta]
      ring

omit [Nonempty Policy] in
theorem stateAfter_c (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).c =
      m.omegaC ^ obs.length • initialC m + m.etaC • geometricEndings m.omegaC obs := by
  simpa [stateAfter, init] using stateAfterFrom_c m (init m) obs

omit [Nonempty Policy] in
theorem click_c_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    let click := (step m (stateAfter m pre) o).1
    click.c = m.omegaC ^ pre.length • initialC m +
        m.etaC • geometricEndings m.omegaC pre ∧
      click.C = normalizeC click.c := by
  simp [step, stateAfter_c]

omit [Nonempty Policy] in
theorem click_zero_C_kit (m : Makeup Policy) (o : Observation Policy) :
    let click := (step m (init m) o).1
    click.c = initialC m ∧ click.C = normalizeC (initialC m) := by
  simp [step, init]

omit [Nonempty Policy] in
theorem stateAfterFrom_d (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.d = m.omegaD ^ obs.length • s.d +
      m.etaD • geometricBeliefs m.omegaD (posteriorHistoryFrom m s obs) := by
  induction obs generalizing s with
  | nil => simp [runFrom, posteriorHistoryFrom, geometricBeliefs]
  | cons o obs ih =>
      rw [show (runFrom m s (o :: obs)).2 = (runFrom m (step m s o).2 obs).2 by rfl, ih]
      simp only [posteriorHistoryFrom, geometricBeliefs, List.length_cons, step, pow_succ]
      funext hidden
      simp [posteriorHistoryFrom_length]
      ring

omit [Nonempty Policy] in
theorem stateAfter_d (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).d = m.omegaD ^ obs.length • m.d₀ +
      m.etaD • geometricBeliefs m.omegaD (posteriorHistory m obs) := by
  simpa [stateAfter, posteriorHistory, init] using stateAfterFrom_d m (init m) obs

omit [Nonempty Policy] in
theorem click_d_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.d =
      m.omegaD ^ pre.length • m.d₀ +
        m.etaD • geometricBeliefs m.omegaD (posteriorHistory m pre) := by
  simp [step, stateAfter_d]

omit [Nonempty Policy] in
theorem stateAfterFrom_habit (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.habit =
      obs.foldl (fun habit o => advanceRated m.etaHabit m.omegaHabit habit o.habitOutcome)
        s.habit := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih => simpa [runFrom, step] using ih (step m s o).2

omit [Nonempty Policy] in
theorem stateAfter_habit (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).habit =
      obs.foldl (fun habit o => advanceRated m.etaHabit m.omegaHabit habit o.habitOutcome)
        (ofSlowState m.habit₀) := by
  simpa [stateAfter, init] using stateAfterFrom_habit m (init m) obs

omit [Nonempty Policy] in
theorem click_habit_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.habitBefore =
      pre.foldl (fun habit x => advanceRated m.etaHabit m.omegaHabit habit x.habitOutcome)
        (ofSlowState m.habit₀) := by
  simp [step, stateAfter_habit]

omit [Nonempty Policy] in
theorem stateAfterFrom_theta (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.theta =
      obs.foldl (fun theta o => advanceWitnessedRated m.etaTheta m.omegaTheta
        m.pattern theta o.thetaOutcomes)
        s.theta := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih => simpa [runFrom, step] using ih (step m s o).2

omit [Nonempty Policy] in
theorem stateAfter_theta (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).theta =
      obs.foldl (fun theta o => advanceWitnessedRated m.etaTheta m.omegaTheta
        m.pattern theta o.thetaOutcomes) (ofSlowState m.theta₀) := by
  simpa [stateAfter, init] using stateAfterFrom_theta m (init m) obs

omit [Nonempty Policy] in
theorem click_theta_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.thetaBefore =
      pre.foldl
        (fun theta x => advanceWitnessedRated m.etaTheta m.omegaTheta
          m.pattern theta x.thetaOutcomes) (ofSlowState m.theta₀) := by
  simp [step, stateAfter_theta]

/-- With η = ω = 1, the rated habit update is exactly the existing R15 update. -/
theorem advanceRated_one {Key : Type} [DecidableEq Key]
    (s : SlowState Key) (o : FastOutcome Key) :
    advanceRated 1 1 (ofSlowState s) o = ofSlowState (R15TemporalHierarchy.advance s o) := by
  funext query
  by_cases h : query = o.policy
  · subst query
    simp [advanceRated, decayRated, addRated, ofSlowState, R15TemporalHierarchy.advance,
      R15TemporalHierarchy.countsFor_setCounts_same, R15TemporalHierarchy.updatedCounts]
    split <;> simp
  · simp [advanceRated, decayRated, addRated, ofSlowState, R15TemporalHierarchy.advance, h,
      R15TemporalHierarchy.countsFor_setCounts_other _ _ _ _ h]

theorem decayRated_one {Key : Type} (counts : RatedCounts Key) :
    decayRated 1 counts = counts := by
  funext key
  simp [decayRated]

theorem fold_addRated_one_ofSlowState {Key : Type} [DecidableEq Key]
    (key : Key) (s : SlowState Key) (xs : List Bool) :
    xs.foldl (fun counts succeeded => addRated 1 counts key succeeded) (ofSlowState s) =
      ofSlowState (PatternTheta.foldFires key s xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons succeeded xs ih =>
      rw [List.foldl_cons]
      have one_step :
          addRated 1 (ofSlowState s) key succeeded =
            ofSlowState (R15TemporalHierarchy.advance s ⟨key, true, succeeded⟩) := by
        simpa [advanceRated, decayRated_one] using
          advanceRated_one s (⟨key, true, succeeded⟩ : FastOutcome Key)
      rw [one_step, ih]
      rfl

/-- With η = ω = 1, the rated witnessed-pattern update is exactly PatternTheta's update. -/
theorem advanceWitnessedRated_one (pattern : PatternIdentity)
    (s : SlowState PatternIdentity) (outcomes : List (FastOutcome PatternIdentity)) :
    advanceWitnessedRated 1 1 pattern (ofSlowState s) outcomes =
      ofSlowState (PatternTheta.advanceWitnessed pattern s outcomes) := by
  rw [advanceWitnessedRated, decayRated_one]
  simp [PatternTheta.advanceWitnessed,
    fold_addRated_one_ofSlowState]

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem geometricEndings_one (obs : List (Observation Policy)) :
    geometricEndings 1 obs = endingCounts obs := by
  induction obs with
  | nil => rfl
  | cons o obs ih => simp [geometricEndings, endingCounts, ih]

omit [DecidableEq Policy] in
theorem geometricBeliefs_one (ps : List (Hidden → ℝ)) :
    geometricBeliefs 1 ps = sumBeliefs ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [geometricBeliefs, sumBeliefs, ih]

omit [Nonempty Policy] in
theorem stateAfter_c_unit_rates (m : Makeup Policy) (obs : List (Observation Policy))
    (heta : m.etaC = 1) (homega : m.omegaC = 1) :
    (stateAfter m obs).c = initialC m + endingCounts obs := by
  rw [stateAfter_c, heta, homega, geometricEndings_one]
  simp

omit [Nonempty Policy] in
theorem stateAfter_d_unit_rates (m : Makeup Policy) (obs : List (Observation Policy))
    (heta : m.etaD = 1) (homega : m.omegaD = 1) :
    (stateAfter m obs).d = m.d₀ + sumBeliefs (posteriorHistory m obs) := by
  rw [stateAfter_d, heta, homega, geometricBeliefs_one]
  simp

omit [Nonempty Policy] in
/-- The next click's Friston 2017 equation 2.7 prior is computed from this
click's Hesp et al. 2021, pp. 286–288 valence transition. -/
theorem step_betaPrior_next (m : Makeup Policy) (s : State Policy)
    (o next : Observation Policy) :
    (step m (step m s o).2 next).1.precision.betaPrior =
      R20Run.descend m.L
        (R20Run.predict m.L (R20Run.valenceUpdate m.L s.valence
          (step m s o).1.precision.betaPrior (step m s o).1.precision.betaPosterior)) := by
  rfl

omit [Nonempty Policy] in
/-- Zero affective charge leaves only the Hesp et al. 2021, pp. 286–288
prediction step in the next valence. -/
theorem step_zero_charge_keeps_valence (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy)
    (same : (step m s o).1.precision.betaPosterior = (step m s o).1.precision.betaPrior)
    (nonzero : (step m s o).1.precision.betaPrior ≠ 0)
    (rates : ∀ k, m.L.rate k ≠ 0) (normal : ∑ k, s.valence k = 1) :
    (step m s o).2.valence = R20Run.predict m.L s.valence := by
  simp only [step] at same nonzero ⊢
  rw [same, R20Run.zero_charge_keeps_valence m.L s.valence nonzero rates normal]

omit [Nonempty Policy] in
theorem runFrom_append_one_state (m : Makeup Policy) (s : State Policy)
    (pre : List (Observation Policy)) (o : Observation Policy) :
    (runFrom m s (pre ++ [o])).2 = (step m (runFrom m s pre).2 o).2 := by
  induction pre generalizing s with
  | nil => rfl
  | cons x xs ih => simpa [runFrom] using ih (step m s x).2

omit [Nonempty Policy] in
/-- Under flat affective rates and stochastic transitions, every computed
Friston 2017 equation 2.7 prior remains the flat rate.  `nondeg` is needed
because `valenceUpdate` normalizes by that weighted evidence sum. -/
theorem click_betaPrior_constant_of_flat (m : Makeup Policy) {r : ℝ}
    (flat : ∀ k, m.L.rate k = r)
    (stoch : ∀ j, ∑ k, m.L.B k j = 1)
    (start : ∑ k, m.q₀ k = 1)
    (nondeg : ∀ (pre : List (Observation Policy)) (o : Observation Policy),
      ∑ k, (stateAfter m pre).valence k *
        R20Run.affectiveEvidence m.L
          (step m (stateAfter m pre) o).1.precision.betaPrior
          (step m (stateAfter m pre) o).1.precision.betaPosterior k ≠ 0)
    (pre : List (Observation Policy)) (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.precision.betaPrior = r := by
  have total : ∀ xs : List (Observation Policy), ∑ k, (stateAfter m xs).valence k = 1 := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil => simpa only [stateAfter, runFrom, init] using start
    | append_singleton x xs ih =>
        rw [stateAfter, runFrom_append_one_state]
        simp only [step]
        rw [R20Run.predict_sum m.L stoch]
        apply R20Run.normalize_sum
        simpa [stateAfter, R20Run.valenceUpdate, step] using nondeg x xs
  simp only [step]
  exact R20Run.descend_flat m.L flat (total pre)

omit [DecidableEq Policy] in
theorem firstIterate_constant_F (betaPrior beta : ℝ) (E G : Policy → ℝ) (c : ℝ) :
    PrecisionFromObservation.firstIterate betaPrior beta E G (fun _ => c) = betaPrior := by
  unfold PrecisionFromObservation.firstIterate PrecisionFromObservation.expectedGChange
  rw [PrecisionFromObservation.posterior_eq_prior_of_constant_F]
  simp

omit [DecidableEq Policy] in
/-- Constant F is the exact fixed point of every bounded Friston 2017
equation 2.7 iteration count. -/
theorem iteratePrecision_constant_F (iterations : ℕ) (betaPrior : ℝ)
    (E G : Policy → ℝ) (c : ℝ) :
    iteratePrecision iterations betaPrior E G (fun _ => c) = betaPrior := by
  induction iterations with
  | zero => rfl
  | succ n ih =>
      rw [iteratePrecision, Function.iterate_succ_apply']
      exact firstIterate_constant_F betaPrior _ E G c

theorem step_constant_F (m : Makeup Policy) (s : State Policy) (o : Observation Policy)
    (c : ℝ) (constant : o.F = fun _ => c) :
    (step m s o).1.precision.betaPosterior = (step m s o).1.precision.betaPrior := by
  simp [step, constant, iteratePrecision_constant_F]

omit [Nonempty Policy] in
/-- Once the bounded iterate is a positive fixed point, the computed precision
row satisfies `IsPosteriorTemperature`; no general convergence is claimed. -/
theorem step_precision_conforms_at_fixed_point (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy)
    (fixed : PrecisionFromObservation.firstIterate
      (step m s o).1.precision.betaPrior (step m s o).1.precision.betaPosterior
      o.E o.G o.F = (step m s o).1.precision.betaPosterior)
    (positive : 0 < (step m s o).1.precision.betaPosterior) :
    PrecisionFromObservation.IsPosteriorTemperature
      (step m s o).1.precision.betaPrior (step m s o).1.precision.betaPosterior
      o.E o.G o.F := by
  refine ⟨positive, ?_⟩
  unfold PrecisionFromObservation.firstIterate at fixed
  unfold PrecisionFromObservation.precisionError
  linarith

omit [Nonempty Policy] in
theorem click_evidence_conforms (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy) :
    R20Certificate.EvidenceConforms (step m s o).1.evidence := by
  rfl

omit [Nonempty Policy] in
theorem run_evidence_conforms (m : Makeup Policy) (obs : List (Observation Policy)) :
    ∀ click ∈ run m obs, R20Certificate.EvidenceConforms click.evidence := by
  intro click present
  unfold run at present
  generalize init m = s at present
  induction obs generalizing s with
  | nil => simp [runFrom] at present
  | cons o obs ih =>
      simp only [runFrom, List.mem_cons] at present
      rcases present with rfl | present
      · exact click_evidence_conforms m s o
      · exact ih (step m s o).2 present

omit [Nonempty Policy] in
theorem stateAfterFrom_runId (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.runId = s.runId + obs.length := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih =>
      rw [show (runFrom m s (o :: obs)).2 = (runFrom m (step m s o).2 obs).2 by rfl, ih]
      simp [step]
      omega

omit [Nonempty Policy] in
theorem stateAfter_runId (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).runId = obs.length := by
  simpa [stateAfter, init] using stateAfterFrom_runId m (init m) obs

omit [Nonempty Policy] in
theorem click_runId_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.runId = pre.length := by
  simp [step, stateAfter_runId]

omit [Nonempty Policy] in
theorem consecutive_runIds (m : Makeup Policy) (pre : List (Observation Policy))
    (a b : Observation Policy) :
    (step m (stateAfter m pre) a).1.runId <
      (step m (stateAfter m (pre ++ [a])) b).1.runId := by
  simp [click_runId_at]

omit [Nonempty Policy] in
theorem stateAfterFrom_focus (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.previousFocus =
      obs.foldl (fun _ o => o.focus) s.previousFocus := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih => simpa [runFrom, step] using ih (step m s o).2

omit [Nonempty Policy] in
theorem click_previousFocus_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.previousFocus =
      pre.foldl (fun _ x => x.focus) m.initialFocus := by
  simp [step, stateAfter, stateAfterFrom_focus, init]

theorem kit_total : CTauClassPreference.totalMass kit = 1 := by
  norm_num [CTauClassPreference.totalMass, kit]

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem initialC_total (m : Makeup Policy) :
    CTauClassPreference.totalMass (initialC m) = m.kappa := by
  simp [CTauClassPreference.totalMass, initialC, kit]
  ring

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem normalize_initialC (m : Makeup Policy) : normalizeC (initialC m) = kit := by
  funext ending
  unfold normalizeC
  rw [initialC_total]
  unfold initialC
  field_simp [m.kappa_pos.ne']

omit [Nonempty Policy] in
theorem click_zero_C_is_kit (m : Makeup Policy) (o : Observation Policy) :
    (step m (init m) o).1.C = kit := by
  simp [step, init, normalize_initialC]

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem initialC_nonnegative (m : Makeup Policy) :
    CTauClassPreference.Nonnegative (initialC m) := by
  intro ending
  fin_cases ending <;> simp [initialC, kit] <;> nlinarith [m.kappa_pos]

theorem addEnding_nonnegative {c : CCounts} (hc : CTauClassPreference.Nonnegative c)
    (ending : EndingClass) : CTauClassPreference.Nonnegative (addEnding c ending) := by
  intro x
  simp only [addEnding]
  split
  · linarith [hc x]
  · simpa using hc x

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem fold_addEnding_nonnegative {c : CCounts}
    (hc : CTauClassPreference.Nonnegative c) (obs : List (Observation Policy)) :
    CTauClassPreference.Nonnegative
      (obs.foldl (fun counts o => addEnding counts o.endingClass) c) := by
  induction obs generalizing c with
  | nil => simpa
  | cons o obs ih =>
      simp only [List.foldl_cons]
      exact ih (addEnding_nonnegative hc _)

theorem advanceC_nonnegative {c : CCounts} (hc : CTauClassPreference.Nonnegative c)
    (eta omega : ℚ) (heta : 0 ≤ eta) (homega : 0 ≤ omega) (ending : EndingClass) :
    CTauClassPreference.Nonnegative (advanceC eta omega c ending) := by
  intro x
  simp only [advanceC, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hdelta : 0 ≤ endingDelta ending x := by
    by_cases h : ending = x ∧ x ≠ .notYetEvaluated <;> simp [endingDelta, h]
  nlinarith [hc x]

omit [Nonempty Policy] in
theorem runFrom_c_nonnegative (m : Makeup Policy) (s : State Policy)
    (hs : CTauClassPreference.Nonnegative s.c) (obs : List (Observation Policy)) :
    CTauClassPreference.Nonnegative (runFrom m s obs).2.c := by
  induction obs generalizing s with
  | nil => simpa [runFrom]
  | cons o obs ih =>
      apply ih
      simpa [step] using advanceC_nonnegative hs m.etaC m.omegaC
        m.etaC_pos.le m.omegaC_pos.le o.endingClass

omit [Nonempty Policy] in
theorem stateAfter_c_nonnegative (m : Makeup Policy) (obs : List (Observation Policy)) :
    CTauClassPreference.Nonnegative (stateAfter m obs).c := by
  exact runFrom_c_nonnegative m (init m) (by simpa [init] using initialC_nonnegative m) obs

theorem addEnding_total (c : CCounts) (ending : EndingClass) :
    CTauClassPreference.totalMass (addEnding c ending) =
      CTauClassPreference.totalMass c + if ending = .notYetEvaluated then 0 else 1 := by
  fin_cases ending <;> simp [CTauClassPreference.totalMass, addEnding] <;> ring

theorem advanceC_total (eta omega : ℚ) (c : CCounts) (ending : EndingClass) :
    CTauClassPreference.totalMass (advanceC eta omega c ending) =
      omega * CTauClassPreference.totalMass c +
        eta * if ending = .notYetEvaluated then 0 else 1 := by
  fin_cases ending <;> simp [CTauClassPreference.totalMass, advanceC, endingDelta] <;> ring

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem fold_addEnding_total_positive {c : CCounts}
    (hc : 0 < CTauClassPreference.totalMass c) (obs : List (Observation Policy)) :
    0 < CTauClassPreference.totalMass
      (obs.foldl (fun counts o => addEnding counts o.endingClass) c) := by
  induction obs generalizing c with
  | nil => simpa
  | cons o obs ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [addEnding_total]
      split <;> linarith

omit [Nonempty Policy] in
theorem stateAfter_c_total_positive (m : Makeup Policy) (obs : List (Observation Policy)) :
    0 < CTauClassPreference.totalMass (stateAfter m obs).c := by
  have aux : ∀ (s : State Policy) (xs : List (Observation Policy)),
      0 < CTauClassPreference.totalMass s.c →
        0 < CTauClassPreference.totalMass (runFrom m s xs).2.c := by
    intro s xs hs
    induction xs generalizing s with
    | nil => simpa [runFrom]
    | cons o xs ih =>
        apply ih
        simp only [step]
        rw [advanceC_total]
        split <;> nlinarith [m.omegaC_pos, m.etaC_pos]
  apply aux (init m) obs
  simpa [init, initialC_total] using m.kappa_pos

theorem normalizeC_probability {c : CCounts}
    (nonnegative : CTauClassPreference.Nonnegative c)
    (positive : 0 < CTauClassPreference.totalMass c) :
    CTauClassPreference.ProbabilityDistribution (normalizeC c) := by
  constructor
  · intro ending
    exact div_nonneg (nonnegative ending) positive.le
  · unfold CTauClassPreference.totalMass normalizeC
    rw [show c .focused / CTauClassPreference.totalMass c +
        c .related / CTauClassPreference.totalMass c +
        c .unrelated / CTauClassPreference.totalMass c +
        c .stopTheLine / CTauClassPreference.totalMass c +
        c .notYetEvaluated / CTauClassPreference.totalMass c =
        CTauClassPreference.totalMass c / CTauClassPreference.totalMass c by
          unfold CTauClassPreference.totalMass
          ring]
    exact div_self positive.ne'

/-- The carried facts that make every outer score on a real run admissible at
the state-model boundary.  The two facts about raw `c` imply that its
normalisation is a probability distribution. -/
structure OuterStateInvariant (s : State Policy) : Prop where
  stateCounts_pos : ∀ status state, 0 < s.stateCounts status state
  gainCounts_pos : ∀ gain, 0 < s.gainCounts gain
  c_nonnegative : CTauClassPreference.Nonnegative s.c
  c_total_positive : 0 < CTauClassPreference.totalMass s.c

omit [Fintype Policy] [Nonempty Policy] in
theorem init_outerStateInvariant (m : Makeup Policy) : OuterStateInvariant (init m) := by
  refine ⟨m.stateKit_pos, m.gainKit_pos, ?_, ?_⟩
  · simpa [init] using initialC_nonnegative m
  · simpa [init, initialC_total] using m.kappa_pos

omit [Nonempty Policy] in
theorem step_outerStateInvariant (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy) (valid : OuterStateInvariant s) :
    OuterStateInvariant (step m s o).2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [step] using valid.stateCounts_pos
  · simpa [step] using valid.gainCounts_pos
  · simpa [step] using advanceC_nonnegative valid.c_nonnegative m.etaC m.omegaC
      m.etaC_pos.le m.omegaC_pos.le o.endingClass
  · simp only [step, advanceC_total]
    split <;> nlinarith [m.omegaC_pos, m.etaC_pos, valid.c_total_positive]

omit [Nonempty Policy] in
theorem runFrom_outerStateInvariant (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) (valid : OuterStateInvariant s) :
    OuterStateInvariant (runFrom m s obs).2 := by
  induction obs generalizing s with
  | nil => simpa [runFrom]
  | cons o obs ih =>
      exact ih (step m s o).2 (step_outerStateInvariant m s o valid)

omit [Nonempty Policy] in
/-- Every state reached by `run` takes the finite-model branch of
`carriedOuterScore`; its three guards cannot fail on a real run. -/
theorem stateAfter_outerStateInvariant (m : Makeup Policy)
    (obs : List (Observation Policy)) : OuterStateInvariant (stateAfter m obs) := by
  exact runFrom_outerStateInvariant m (init m) obs (init_outerStateInvariant m)

omit [Nonempty Policy] in
theorem carriedOuterScore_stateAfter_eq_outerScore (m : Makeup Policy)
    (pre : List (Observation Policy)) (o : Observation Policy)
    (cascade : SelectionCascade) :
    carriedOuterScore m (stateAfter m pre) o cascade =
      outerScore o.focus m.relation o.facts o.field
        (stateAfter m pre).stateCounts
        (stateAfter_outerStateInvariant m pre).stateCounts_pos
        (normalizeC (stateAfter m pre).c)
        (normalizeC_probability (stateAfter_outerStateInvariant m pre).c_nonnegative
          (stateAfter_outerStateInvariant m pre).c_total_positive)
        (stateAfter m pre).gainCounts
        (stateAfter_outerStateInvariant m pre).gainCounts_pos cascade := by
  classical
  let valid := stateAfter_outerStateInvariant m pre
  let C_probability := normalizeC_probability valid.c_nonnegative valid.c_total_positive
  rw [carriedOuterScore, dif_pos valid.stateCounts_pos,
    dif_pos C_probability, dif_pos valid.gainCounts_pos]

omit [Nonempty Policy] in
/-- Every score recorded by a real click is the outer `stepG` score, with no
fallback-to-`⊤` guard branch. -/
theorem click_cascadeScores_eq_outerScore (m : Makeup Policy)
    (pre : List (Observation Policy)) (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.cascadeScores =
      m.cascades.map (fun cascade =>
        outerScore o.focus m.relation o.facts o.field
          (stateAfter m pre).stateCounts
          (stateAfter_outerStateInvariant m pre).stateCounts_pos
          (normalizeC (stateAfter m pre).c)
          (normalizeC_probability (stateAfter_outerStateInvariant m pre).c_nonnegative
            (stateAfter_outerStateInvariant m pre).c_total_positive)
          (stateAfter m pre).gainCounts
          (stateAfter_outerStateInvariant m pre).gainCounts_pos cascade) := by
  rw [step_scores_read_carried_C]
  apply List.map_congr_left
  intro cascade present
  exact carriedOuterScore_stateAfter_eq_outerScore m pre o cascade

omit [Nonempty Policy] in
theorem click_C_probability (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    CTauClassPreference.ProbabilityDistribution (step m (stateAfter m pre) o).1.C := by
  simp only [step]
  exact normalizeC_probability (stateAfter_c_nonnegative m pre)
    (stateAfter_c_total_positive m pre)

/-! A concrete two-click preference update. -/

/-- Example η_d is 1 so the example isolates preference forgetting. -/
def exampleEtaD : ℝ := 1
/-- Example ω_d is 1 so the example isolates preference forgetting. -/
def exampleOmegaD : ℝ := 1
/-- Example η_c is 1 to add one focused terminal observation. -/
def exampleEtaC : ℚ := 1
/-- Example ω_c is 9/10 to exhibit a nontrivial forgetting step. -/
def exampleOmegaC : ℚ := 9 / 10
/-- Example η_h is 1 because habit rates are not the demonstrated quantity. -/
def exampleEtaHabit : ℚ := 1
/-- Example ω_h is 1 because habit rates are not the demonstrated quantity. -/
def exampleOmegaHabit : ℚ := 1
/-- Example η_θ is 1 because pattern rates are not the demonstrated quantity. -/
def exampleEtaTheta : ℚ := 1
/-- Example ω_θ is 1 because pattern rates are not the demonstrated quantity. -/
def exampleOmegaTheta : ℚ := 1

/-- Concrete makeup for the Friston 2017 / Smith, Friston & Whyte 2022 example. -/
noncomputable def exampleMakeup : Makeup Unit where
  A := fun _ _ => 1
  d₀ := fun _ => 1
  habit₀ := []
  pattern := ⟨"pattern/example"⟩
  theta₀ := []
  kappa := 100
  kappa_pos := by norm_num
  stateKit := fun _ _ => 1
  stateKit_pos := by intros; norm_num
  gainKit := fun | .none => 1 | .one => 2 | .several => 4
  gainKit_pos := by intro gain; cases gain <;> norm_num
  etaD := exampleEtaD
  etaD_pos := by norm_num [exampleEtaD]
  omegaD := exampleOmegaD
  omegaD_pos := by norm_num [exampleOmegaD]
  omegaD_le_one := by norm_num [exampleOmegaD]
  etaC := exampleEtaC
  etaC_pos := by norm_num [exampleEtaC]
  omegaC := exampleOmegaC
  omegaC_pos := by norm_num [exampleOmegaC]
  omegaC_le_one := by norm_num [exampleOmegaC]
  etaHabit := exampleEtaHabit
  etaHabit_pos := by norm_num [exampleEtaHabit]
  omegaHabit := exampleOmegaHabit
  omegaHabit_pos := by norm_num [exampleOmegaHabit]
  omegaHabit_le_one := by norm_num [exampleOmegaHabit]
  etaTheta := exampleEtaTheta
  etaTheta_pos := by norm_num [exampleEtaTheta]
  omegaTheta := exampleOmegaTheta
  omegaTheta_pos := by norm_num [exampleOmegaTheta]
  omegaTheta_le_one := by norm_num [exampleOmegaTheta]
  L := R20Run.hespLevel
  q₀ := R20Run.half
  precisionIterations := 2
  cascades := [[]]
  cascades_nonempty := by simp
  relation := fun _ _ => .other 0
  initialFocus := 7

/-- One R15 outcome used in the sourced-update example. -/
def exampleOutcome : FastOutcome Unit := ⟨(), true, true⟩

/-- One observation for the Friston 2017 / Smith, Friston & Whyte 2022 example. -/
def exampleObservation (ending : EndingClass) (focus : Nat) : Observation Unit where
  observation := true
  habitOutcome := exampleOutcome
  thetaOutcomes := []
  endingClass := ending
  focus := focus
  E := fun _ => 1
  G := fun _ => 1
  F := fun _ => 0
  field := []
  facts := fun _ => ⟨ReadinessStatus.notReady, 0, 0⟩

example :
    let clicks := run exampleMakeup
      [exampleObservation .focused 8, exampleObservation .related 9]
    clicks.map (fun click => click.c .focused) = [55, 101 / 2] := by
  have h : CTauClassPreference.EndingClass.focused ≠ .notYetEvaluated := by decide
  norm_num [run, runFrom, step, init, initialC, kit, normalizeC,
    evidencePrior, EvidenceFromTheProcess.posterior, EvidenceFromTheProcess.evidence,
    exampleMakeup, exampleObservation, exampleOutcome, advanceC, endingDelta,
    exampleEtaD, exampleOmegaD, exampleEtaC, exampleOmegaC, exampleEtaHabit,
    exampleOmegaHabit, exampleEtaTheta, exampleOmegaTheta, decayRated, addRated,
    advanceRated, advanceWitnessedRated, h]

abbrev ExamplePolicy := PrecisionFromObservation.TwoPolicy

/-- Two-policy makeup for the computed Friston 2017 precision example. -/
noncomputable def precisionExampleMakeup : Makeup ExamplePolicy where
  A := fun _ _ => 1
  d₀ := fun _ => 1
  habit₀ := []
  pattern := ⟨"pattern/precision-example"⟩
  theta₀ := []
  kappa := 100
  kappa_pos := by norm_num
  stateKit := fun _ _ => 1
  stateKit_pos := by intros; norm_num
  gainKit := fun | .none => 1 | .one => 2 | .several => 4
  gainKit_pos := by intro gain; cases gain <;> norm_num
  etaD := 1
  etaD_pos := by norm_num
  omegaD := 1
  omegaD_pos := by norm_num
  omegaD_le_one := by norm_num
  etaC := 1
  etaC_pos := by norm_num
  omegaC := 9 / 10
  omegaC_pos := by norm_num
  omegaC_le_one := by norm_num
  etaHabit := 1
  etaHabit_pos := by norm_num
  omegaHabit := 1
  omegaHabit_pos := by norm_num
  omegaHabit_le_one := by norm_num
  etaTheta := 1
  etaTheta_pos := by norm_num
  omegaTheta := 1
  omegaTheta_pos := by norm_num
  omegaTheta_le_one := by norm_num
  L := R20Run.hespLevel
  q₀ := R20Run.half
  precisionIterations := 2
  cascades := [[]]
  cascades_nonempty := by simp
  relation := fun _ _ => .other 0
  initialFocus := 7

/-- Two-policy E, G, F arrive as observations in slice 2; constant F makes
the fixed point exact while E and G remain policy-indexed. -/
def precisionExampleObservation (ending : EndingClass) (focus : Nat) :
    Observation ExamplePolicy where
  observation := true
  habitOutcome := ⟨.a, true, true⟩
  thetaOutcomes := []
  endingClass := ending
  focus := focus
  E := fun | .a => 2 | .b => 1
  G := fun | .a => 0 | .b => 1
  F := fun _ => 0
  field := []
  facts := fun _ => ⟨ReadinessStatus.notReady, 0, 0⟩

example :
    let clicks := run precisionExampleMakeup
      [precisionExampleObservation .focused 8, precisionExampleObservation .related 9]
    clicks.map (fun click => click.precision.betaPrior) = [5 / 4, 5 / 4] := by
  norm_num [run, runFrom, step, init, precisionExampleMakeup, precisionExampleObservation,
    iteratePrecision, PrecisionFromObservation.firstIterate,
    PrecisionFromObservation.expectedGChange,
    PrecisionFromObservation.posterior_eq_prior_of_constant_F,
    R20Run.descend, R20Run.predict, R20Run.valenceUpdate, R20Run.normalize,
    R20Run.affectiveEvidence, R20Run.charge, R20Run.hespLevel, R20Run.half,
    R20Run.identityB, R20Run.sum_valence]

/-! A nonconstant-F two-click example where precision changes valence. -/

/-- One Friston 2017 equation 2.7 iteration makes the nonconstant-F effect explicit. -/
noncomputable def movingPrecisionMakeup : Makeup ExamplePolicy :=
  { precisionExampleMakeup with precisionIterations := 1 }

/-- Exact two-policy scores: F cancels G/β for policy b at the initial β = 5/4. -/
noncomputable def movingPrecisionObservation (ending : EndingClass) (focus : Nat) :
    Observation ExamplePolicy where
  observation := true
  habitOutcome := ⟨.a, true, true⟩
  thetaOutcomes := []
  endingClass := ending
  focus := focus
  E := fun _ => 1
  G := fun | .a => 0 | .b => 5 / 4 * Real.log 3
  F := fun | .a => 0 | .b => -Real.log 3
  field := []
  facts := fun _ => ⟨ReadinessStatus.notReady, 0, 0⟩

/-- The exact first-click expected-G displacement. -/
noncomputable def movingX : ℝ := 5 / 16 * Real.log 3

theorem moving_click_zero_betaPosterior :
    let clicks := run movingPrecisionMakeup
      [movingPrecisionObservation .focused 8, movingPrecisionObservation .related 9]
    (clicks.head?.getD (step movingPrecisionMakeup (init movingPrecisionMakeup)
      (movingPrecisionObservation .focused 8)).1).precision.betaPosterior = 5 / 4 + movingX := by
  norm_num [run, runFrom, step, init, movingPrecisionMakeup, precisionExampleMakeup,
    movingPrecisionObservation, movingX, iteratePrecision,
    PrecisionFromObservation.firstIterate, PrecisionFromObservation.expectedGChange,
    PrecisionFromObservation.priorPolicy, PrecisionFromObservation.posteriorPolicy,
    PrecisionFromObservation.softmax, R20Run.descend, R20Run.hespLevel, R20Run.half,
    R20Run.sum_valence, PrecisionFromObservation.sum_twoPolicy, Real.exp_neg]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  ring

theorem moving_click_one_betaPrior :
    let first := movingPrecisionObservation .focused 8
    let second := movingPrecisionObservation .related 9
    (step movingPrecisionMakeup (step movingPrecisionMakeup
      (init movingPrecisionMakeup) first).2 second).1.precision.betaPrior =
      (10 + 17 * movingX) / (8 + 10 * movingX) := by
  norm_num [step, init, movingPrecisionMakeup, precisionExampleMakeup,
    movingPrecisionObservation, movingX, iteratePrecision,
    PrecisionFromObservation.firstIterate, PrecisionFromObservation.expectedGChange,
    PrecisionFromObservation.priorPolicy, PrecisionFromObservation.posteriorPolicy,
    PrecisionFromObservation.softmax, PrecisionFromObservation.sum_twoPolicy,
    R20Run.descend, R20Run.predict, R20Run.valenceUpdate, R20Run.normalize,
    R20Run.affectiveEvidence, R20Run.charge, R20Run.hespLevel, R20Run.half,
    R20Run.identityB, R20Run.sum_valence, Real.exp_neg]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have log_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  field_simp <;> ring_nf <;> nlinarith

theorem moving_click_one_betaPrior_moved :
    let first := movingPrecisionObservation .focused 8
    let second := movingPrecisionObservation .related 9
    let beta := (step movingPrecisionMakeup (step movingPrecisionMakeup
      (init movingPrecisionMakeup) first).2 second).1.precision.betaPrior
    beta ≠ 5 / 4 ∧ 5 / 4 < beta := by
  dsimp only
  rw [moving_click_one_betaPrior]
  have log_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have x_pos : 0 < movingX := by
    unfold movingX
    positivity
  have denominator_pos : 0 < 8 + 10 * movingX := by positivity
  have greater : (5 / 4 : ℝ) < (10 + 17 * movingX) / (8 + 10 * movingX) := by
    rw [lt_div_iff₀ denominator_pos]
    nlinarith
  exact ⟨ne_of_gt greater, greater⟩

/-! A concrete outer task-selection menu.

The slice-3a/3b numerical examples below are retained as source while their
outer-G arithmetic is recomputed in the follow-up example packet. -/

/-

def selectionCandidateOne : Candidate := ⟨1, 1 / 2⟩
def selectionCandidateTwo : Candidate := ⟨2, 1 / 2⟩
def selectionCandidateThree : Candidate := ⟨3, 1 / 4⟩

def selectionExampleCascadeA : SelectionCascade :=
  [.gate (fun candidate => decide (candidate.target = 2)),
   .order (fun candidate => -candidate.reach)]

def selectionExampleCascadeB : SelectionCascade :=
  [.order (fun candidate => candidate.target)]

/-- The first cascade gates to target 2; the second orders the whole field by target id. -/
def selectionExampleCascades : List SelectionCascade :=
  [selectionExampleCascadeA, selectionExampleCascadeB]

noncomputable def selectionExampleMakeup : Makeup ExamplePolicy :=
  { precisionExampleMakeup with
    cascades := selectionExampleCascades
    cascades_nonempty := by simp [selectionExampleCascades]
    relation := fun _ target => if target = 1 ∨ target = 2 then .focus else .associated }

noncomputable def selectionExampleObservation : Observation ExamplePolicy :=
  { precisionExampleObservation .focused 7 with
    field := [selectionCandidateOne, selectionCandidateTwo, selectionCandidateThree] }

noncomputable def selectionExampleScore : EReal :=
  CTauClassPreference.classRisk
    (R15InjuryTier.candidatePrediction .focused (1 / 2)) kit

/-- The 3a example deliberately ties: it checks menu-order tie breaking, not
evidence-based selection. -/
example :
    let click := (step selectionExampleMakeup (init selectionExampleMakeup)
      selectionExampleObservation).1
    click.cascadeIndex = 0 ∧
      click.cascadeScores = [selectionExampleScore, selectionExampleScore] ∧
      click.selection = some
        { candidates := selectionExampleObservation.field, selected := selectionCandidateTwo } := by
  have scoreA : cascadeScore 7 selectionExampleMakeup.relation selectionExampleObservation.facts selectionExampleObservation.field
      (normalizeC (init selectionExampleMakeup).c) selectionExampleCascadeA = selectionExampleScore := by
    norm_num [cascadeScore, cascadePrediction, cascadePick, applySelectionCascade,
      applySelectionStep, selectionExampleCascadeA, selectionExampleMakeup,
      selectionExampleObservation, selectionCandidateOne, selectionCandidateTwo,
      selectionCandidateThree, selectionExampleScore, init, normalize_initialC,
      R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass]
  have scoreB : cascadeScore 7 selectionExampleMakeup.relation selectionExampleObservation.facts selectionExampleObservation.field
      (normalizeC (init selectionExampleMakeup).c) selectionExampleCascadeB = selectionExampleScore := by
    norm_num [cascadeScore, cascadePrediction, cascadePick, applySelectionCascade,
      applySelectionStep, selectionExampleCascadeB, selectionExampleMakeup,
      selectionExampleObservation, selectionCandidateOne, selectionCandidateTwo,
      selectionCandidateThree, selectionExampleScore, init, normalize_initialC,
      R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass]
  have chosen : chosenCascadeEntry selectionExampleMakeup (init selectionExampleMakeup)
      selectionExampleObservation = (selectionExampleCascadeA, 0) := by
    unfold chosenCascadeEntry
    change (([(selectionExampleCascadeA, 0), (selectionExampleCascadeB, 1)]).argmin
      (fun entry => cascadeScore 7 selectionExampleMakeup.relation
        selectionExampleObservation.facts selectionExampleObservation.field (normalizeC (init selectionExampleMakeup).c)
        entry.1)).get _ = (selectionExampleCascadeA, 0)
    simp [List.argmin, List.argAux, scoreA, scoreB]
  simp only [step]
  rw [chosen]
  norm_num [selectionExampleMakeup,
    selectionExampleCascades, selectionExampleObservation, precisionExampleObservation,
    precisionExampleMakeup, init, cascadeScore, cascadePrediction, cascadePick,
    applySelectionCascade, applySelectionStep, selectionExampleScore,
    selectionExampleCascadeA, selectionExampleCascadeB, scoreA, scoreB, chosen,
    selectionCandidateOne, selectionCandidateTwo, selectionCandidateThree,
    normalize_initialC, R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass]

/-! Learned C changes the outer selection on the next click. -/

def learnedSelectionCascadeA : SelectionCascade :=
  [.gate (fun candidate => decide (candidate.target = 1))]

def learnedSelectionCascadeB : SelectionCascade :=
  [.gate (fun candidate => decide (candidate.target = 3))]

def learnedSelectionCandidateThree : Candidate := ⟨3, 1 / 2⟩

def learnedSelectionCascades : List SelectionCascade :=
  [learnedSelectionCascadeA, learnedSelectionCascadeB]

/-- κ = 1 makes one related ending visibly move learned C in this example. -/
noncomputable def learnedSelectionMakeup : Makeup ExamplePolicy :=
  { selectionExampleMakeup with
    kappa := 1
    kappa_pos := by norm_num
    cascades := learnedSelectionCascades
    cascades_nonempty := by simp [learnedSelectionCascades]
    relation := fun _ target => if target = 1 then .focus else
      if target = 3 then .associated else .other 0 }

noncomputable def learnedSelectionObservation : Observation ExamplePolicy :=
  { precisionExampleObservation .related 7 with
    field := [selectionCandidateOne, learnedSelectionCandidateThree]
    endingClass := .related }

def learnedSelectionC : CTauClassPreference.Distribution
  | .focused => 99 / 380
  | .related => 263 / 380
  | .unrelated => 9 / 380
  | .stopTheLine => 9 / 380
  | .notYetEvaluated => 0

theorem initial_focused_risk_lt_related :
    CTauClassPreference.classRisk
        (R15InjuryTier.candidatePrediction .focused (1 / 2)) kit <
      CTauClassPreference.classRisk
        (R15InjuryTier.candidatePrediction .related (1 / 2)) kit := by
  change CTauClassPreference.classRisk
        (R15InjuryTier.candidatePrediction .focused (1 / 2))
        CTauClassPreference.terminalPreference <
      CTauClassPreference.classRisk
        (R15InjuryTier.candidatePrediction .related (1 / 2))
        CTauClassPreference.terminalPreference
  rw [R15InjuryTier.classRisk_eq .focused (by simp [R15InjuryTier.ReachedClass]),
    R15InjuryTier.classRisk_eq .related (by simp [R15InjuryTier.ReachedClass])]
  simp only [EReal.coe_lt_coe_iff]
  rw [R15InjuryTier.value_focused, R15InjuryTier.value_related]
  have logs : Real.log 7 < Real.log 11 := Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  norm_num
  linarith

theorem learned_related_risk_lt_focused :
    CTauClassPreference.classRisk
        (R15InjuryTier.candidatePrediction .related (1 / 2)) learnedSelectionC <
      CTauClassPreference.classRisk
        (R15InjuryTier.candidatePrediction .focused (1 / 2)) learnedSelectionC := by
  have related_supported : ¬ CTauClassPreference.Unsupported
      (R15InjuryTier.candidatePrediction .related (1 / 2)) learnedSelectionC := by
    rintro ⟨ending, positive, zero⟩
    fin_cases ending <;> simp [R15InjuryTier.candidatePrediction, learnedSelectionC] at positive zero
  have focused_supported : ¬ CTauClassPreference.Unsupported
      (R15InjuryTier.candidatePrediction .focused (1 / 2)) learnedSelectionC := by
    rintro ⟨ending, positive, zero⟩
    fin_cases ending <;> simp [R15InjuryTier.candidatePrediction, learnedSelectionC] at positive zero
  simp only [CTauClassPreference.classRisk, related_supported, focused_supported, if_false,
    EReal.coe_lt_coe_iff]
  simp only [CTauClassPreference.finiteClassRisk, R15InjuryTier.sum_endingClass,
    R15InjuryTier.candidatePrediction, learnedSelectionC]
  simp only [reduceCtorEq, if_false, if_true, zero_add, add_zero]
  norm_num
  have ratio_pos : (0 : ℝ) < (1 / 2) / (263 / 380) := by norm_num
  have ratio_lt : (1 / 2 : ℝ) / (263 / 380) < (1 / 2) / (99 / 380) := by norm_num
  have logs := Real.strictMonoOn_log ratio_pos (by norm_num) ratio_lt
  linarith

noncomputable def learnedSelectionState0 : State ExamplePolicy :=
  init learnedSelectionMakeup

noncomputable def learnedSelectionClick0 : Click ExamplePolicy :=
  (step learnedSelectionMakeup learnedSelectionState0 learnedSelectionObservation).1

noncomputable def learnedSelectionState1 : State ExamplePolicy :=
  (step learnedSelectionMakeup learnedSelectionState0 learnedSelectionObservation).2

noncomputable def learnedSelectionClick1 : Click ExamplePolicy :=
  (step learnedSelectionMakeup learnedSelectionState1 learnedSelectionObservation).1

/-- After one related ending, forgetting and learning move C from the kit to
(99, 263, 9, 9) / 380. -/
theorem learned_selection_click_one_C :
    normalizeC learnedSelectionState1.c = learnedSelectionC := by
  change normalizeC (advanceC 1 (9 / 10) (fun ending => 1 * kit ending) .related) =
    learnedSelectionC
  funext ending
  fin_cases ending <;>
    simp only [advanceC, normalizeC, CTauClassPreference.totalMass,
      learnedSelectionC, kit] <;>
    simp [endingDelta, reduceCtorEq] <;>
    norm_num

/-- At click zero the kit prefers the focused pick strictly; menu order is
not needed to choose cascade A and target 1. -/
theorem learned_selection_click_zero :
    cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
        learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState0.c)
        learnedSelectionCascadeA <
      cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
        learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState0.c)
        learnedSelectionCascadeB ∧
    learnedSelectionClick0.cascadeIndex = 0 ∧
    learnedSelectionClick0.selection = some
      { candidates := learnedSelectionObservation.field, selected := selectionCandidateOne } := by
  have scoreA : cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
      learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState0.c)
      learnedSelectionCascadeA =
        CTauClassPreference.classRisk
          (R15InjuryTier.candidatePrediction .focused (1 / 2)) kit := by
    norm_num [cascadeScore, cascadePrediction, cascadePick, applySelectionCascade,
      applySelectionStep, learnedSelectionCascadeA, learnedSelectionMakeup,
      learnedSelectionObservation, selectionCandidateOne, learnedSelectionCandidateThree,
      learnedSelectionState0, init, normalize_initialC,
      R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass]
  have scoreB : cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
      learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState0.c)
      learnedSelectionCascadeB =
        CTauClassPreference.classRisk
          (R15InjuryTier.candidatePrediction .related (1 / 2)) kit := by
    norm_num [cascadeScore, cascadePrediction, cascadePick, applySelectionCascade,
      applySelectionStep, learnedSelectionCascadeB, learnedSelectionMakeup,
      learnedSelectionObservation, selectionCandidateOne, learnedSelectionCandidateThree,
      learnedSelectionState0, init, normalize_initialC,
      R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass]
  have strict : cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
      learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState0.c)
      learnedSelectionCascadeA <
        cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
          learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState0.c)
          learnedSelectionCascadeB := by
    rw [scoreA, scoreB]
    exact initial_focused_risk_lt_related
  have chosen : chosenCascadeEntry learnedSelectionMakeup learnedSelectionState0
      learnedSelectionObservation = (learnedSelectionCascadeA, 0) := by
    unfold chosenCascadeEntry
    change (([(learnedSelectionCascadeA, 0), (learnedSelectionCascadeB, 1)]).argmin
      (fun entry => cascadeScore learnedSelectionObservation.focus
        learnedSelectionMakeup.relation learnedSelectionObservation.facts learnedSelectionObservation.field
        (normalizeC learnedSelectionState0.c) entry.1)).get _ =
          (learnedSelectionCascadeA, 0)
    have not_reverse := not_lt_of_ge (le_of_lt strict)
    simp [List.argmin, List.argAux, not_reverse]
  refine ⟨strict, ?_, ?_⟩
  · simp [learnedSelectionClick0, step, chosen]
  · simp only [learnedSelectionClick0, step]
    rw [chosen]
    norm_num [cascadePick, applySelectionCascade, applySelectionStep,
      learnedSelectionCascadeA, learnedSelectionObservation,
      selectionCandidateOne, learnedSelectionCandidateThree]

/-- At click one learned C prefers the related pick strictly; cascade B and
target 3 therefore win independently of menu order. -/
theorem learned_selection_click_one :
    cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
        learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState1.c)
        learnedSelectionCascadeB <
      cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
        learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState1.c)
        learnedSelectionCascadeA ∧
    learnedSelectionClick1.cascadeIndex = 1 ∧
    learnedSelectionClick1.selection = some
      { candidates := learnedSelectionObservation.field, selected := learnedSelectionCandidateThree } := by
  have scoreA : cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
      learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState1.c)
      learnedSelectionCascadeA =
        CTauClassPreference.classRisk
          (R15InjuryTier.candidatePrediction .focused (1 / 2)) learnedSelectionC := by
    rw [learned_selection_click_one_C]
    norm_num [cascadeScore, cascadePrediction, cascadePick, applySelectionCascade,
      applySelectionStep, learnedSelectionCascadeA, learnedSelectionMakeup,
      learnedSelectionObservation, selectionCandidateOne, learnedSelectionCandidateThree,
      R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass]
  have scoreB : cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
      learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState1.c)
      learnedSelectionCascadeB =
        CTauClassPreference.classRisk
          (R15InjuryTier.candidatePrediction .related (1 / 2)) learnedSelectionC := by
    rw [learned_selection_click_one_C]
    norm_num [cascadeScore, cascadePrediction, cascadePick, applySelectionCascade,
      applySelectionStep, learnedSelectionCascadeB, learnedSelectionMakeup,
      learnedSelectionObservation, selectionCandidateOne, learnedSelectionCandidateThree,
      R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass]
  have strict : cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
      learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState1.c)
      learnedSelectionCascadeB <
        cascadeScore learnedSelectionObservation.focus learnedSelectionMakeup.relation
          learnedSelectionObservation.facts learnedSelectionObservation.field (normalizeC learnedSelectionState1.c)
          learnedSelectionCascadeA := by
    rw [scoreB, scoreA]
    exact learned_related_risk_lt_focused
  have chosen : chosenCascadeEntry learnedSelectionMakeup learnedSelectionState1
      learnedSelectionObservation = (learnedSelectionCascadeB, 1) := by
    unfold chosenCascadeEntry
    change (([(learnedSelectionCascadeA, 0), (learnedSelectionCascadeB, 1)]).argmin
      (fun entry => cascadeScore learnedSelectionObservation.focus
        learnedSelectionMakeup.relation learnedSelectionObservation.facts learnedSelectionObservation.field
        (normalizeC learnedSelectionState1.c) entry.1)).get _ =
          (learnedSelectionCascadeB, 1)
    simp [List.argmin, List.argAux, strict]
  refine ⟨strict, ?_, ?_⟩
  · simp [learnedSelectionClick1, step, chosen]
  · simp only [learnedSelectionClick1, step]
    rw [chosen]
    norm_num [cascadePick, applySelectionCascade, applySelectionStep,
      learnedSelectionCascadeB, learnedSelectionObservation,
      selectionCandidateOne, learnedSelectionCandidateThree]

-/

/-! Event K3.2 from `M-象-2000.md`: Giraffe readiness and unblock facts. -/

/-- Target 1 is P12 “core system working end to end”; target 2 is “edge
cases: provisional withdrawal”; target 3 is “countersigned voids”. -/
def k32Field : List Candidate := [⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩]

/-- Giraffe found P12 ready with two one-step unblocks; the other two tasks
were not ready. -/
def k32Facts : Target → GiraffeFacts
  | 1 => ⟨ReadinessStatus.ready, 2, 2⟩
  | 2 => ⟨ReadinessStatus.notReady, 0, 0⟩
  | 3 => ⟨ReadinessStatus.notReady, 0, 0⟩
  | _ => ⟨ReadinessStatus.notReady, 0, 0⟩

example : cascadePick whatOthersWaitOnFirst k32Facts k32Field = some ⟨1, 1⟩ := by
  rfl

/-! Explicit slice-3d outer-score examples, independent of `step`. -/

def outerExampleC : CTauClassPreference.Distribution := fun _ => 1 / 5

theorem outerExampleC_probability : CTauClassPreference.ProbabilityDistribution outerExampleC := by
  constructor
  · intro; norm_num [outerExampleC]
  · norm_num [outerExampleC, CTauClassPreference.totalMass]

def outerExampleStateCounts : ReadinessStatus → TaskState → ℚ := fun _ _ => 1
theorem outerExampleStateCounts_pos : ∀ status state, 0 < outerExampleStateCounts status state := by
  intros; norm_num [outerExampleStateCounts]

def outerExampleGainCounts : ReadyGain → ℚ := fun _ => 1
theorem outerExampleGainCounts_pos : ∀ gain, 0 < outerExampleGainCounts gain := by
  intro; norm_num [outerExampleGainCounts]

def outerExampleRelation : Target → Target → TargetRelation := fun _ _ => .focus
def outerCascadeOne : SelectionCascade := [.gate (fun candidate => decide (candidate.target = 1))]
def outerCascadeTwo : SelectionCascade := [.gate (fun candidate => decide (candidate.target = 2))]
def outerAmbiguityField : List Candidate := [⟨1, 1⟩, ⟨2, 1 / 2⟩]
def outerAmbiguityFacts : Target → GiraffeFacts := fun _ => ⟨.ready, 0, 0⟩

theorem outerCascadeOne_reach_valid : ∀ candidate : Candidate,
    cascadePick outerCascadeOne outerAmbiguityFacts outerAmbiguityField = some candidate →
      0 ≤ candidate.reach ∧ candidate.reach ≤ 1 := by
  intro candidate picked
  norm_num [cascadePick, applySelectionCascade, applySelectionStep, outerCascadeOne,
    outerAmbiguityField] at picked
  subst candidate
  norm_num

theorem outerCascadeTwo_reach_valid : ∀ candidate : Candidate,
    cascadePick outerCascadeTwo outerAmbiguityFacts outerAmbiguityField = some candidate →
      0 ≤ candidate.reach ∧ candidate.reach ≤ 1 := by
  intro candidate picked
  norm_num [cascadePick, applySelectionCascade, applySelectionStep, outerCascadeTwo,
    outerAmbiguityField] at picked
  subst candidate
  norm_num

theorem outerAmbiguityModelOne :
    outerModel 0 outerExampleRelation outerAmbiguityFacts outerAmbiguityField
      outerExampleStateCounts outerExampleStateCounts_pos outerCascadeOne =
    (outerCountKernel (outerExampleStateCounts .ready) (outerExampleStateCounts_pos .ready),
      pickedOuterKernel (.focused, .none) 1) := by
  have picked : cascadePick outerCascadeOne outerAmbiguityFacts outerAmbiguityField =
      some (⟨1, 1⟩ : Candidate) := by
    norm_num [cascadePick, applySelectionCascade, applySelectionStep, outerCascadeOne,
      outerAmbiguityField]
  norm_num [outerModel, outerCascadeOne, outerAmbiguityFacts, outerAmbiguityField,
    outerExampleRelation, cascadePick, applySelectionCascade, applySelectionStep,
    R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass, readyGain, picked]

theorem outerAmbiguityModelTwo :
    outerModel 0 outerExampleRelation outerAmbiguityFacts outerAmbiguityField
      outerExampleStateCounts outerExampleStateCounts_pos outerCascadeTwo =
    (outerCountKernel (outerExampleStateCounts .ready) (outerExampleStateCounts_pos .ready),
      pickedOuterKernel (.focused, .none) (1 / 2)) := by
  have picked : cascadePick outerCascadeTwo outerAmbiguityFacts outerAmbiguityField =
      some (⟨2, 1 / 2⟩ : Candidate) := by
    norm_num [cascadePick, applySelectionCascade, applySelectionStep, outerCascadeTwo,
      outerAmbiguityField]
  norm_num [outerModel, outerCascadeTwo, outerAmbiguityFacts, outerAmbiguityField,
    outerExampleRelation, cascadePick, applySelectionCascade, applySelectionStep,
    R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass, readyGain, picked]

theorem outer_ambiguity_matters :
    outerScore 0 outerExampleRelation outerAmbiguityFacts outerAmbiguityField
        outerExampleStateCounts outerExampleStateCounts_pos outerExampleC
        outerExampleC_probability outerExampleGainCounts outerExampleGainCounts_pos
        outerCascadeOne <
      outerScore 0 outerExampleRelation outerAmbiguityFacts outerAmbiguityField
        outerExampleStateCounts outerExampleStateCounts_pos outerExampleC
        outerExampleC_probability outerExampleGainCounts outerExampleGainCounts_pos
        outerCascadeTwo := by
  simp only [outerScore]
  rw [outerAmbiguityModelOne, outerAmbiguityModelTwo]
  have admitted (q : ProbabilityKernel Unit OuterOutcome) :
      PreferenceRiskSeparation.riskAdmissible q
        (outerPreferenceKernel outerExampleC outerExampleC_probability
          outerExampleGainCounts outerExampleGainCounts_pos) := by
    intro _ outcome _ _
    exact outerPreferenceKernel_mass_pos _ _ (by intro; norm_num [outerExampleC])
      _ outerExampleGainCounts_pos outcome
  split_ifs with h1 h2
  all_goals try { exact (h1 (admitted _)).elim }
  all_goals try { exact (h2 (admitted _)).elim }
  simp only [EReal.coe_lt_coe_iff]
  unfold CascadeEFE.stepG CascadeEFE.risk CascadeEFE.ambiguity CascadeEFE.entropy
    CascadeEFE.klTerm
  simp [outerPreferenceKernel, outerCountKernel,
    pickedOuterKernel, CascadeEFE.finiteKernel, CascadeEFE.push, CascadeEFE.stepG,
    CascadeEFE.risk, CascadeEFE.ambiguity, CascadeEFE.entropy, CascadeEFE.klTerm,
    PreferenceRiskSeparation.riskAdmissible, boundedReach,
    outerExampleRelation, outerAmbiguityFacts, outerAmbiguityField,
    outerExampleStateCounts, outerExampleGainCounts, outerExampleC,
    outerCascadeOne, outerCascadeTwo, cascadePick, applySelectionCascade,
    applySelectionStep, readyGain, R15StrategicTarget.outcomeClass,
    CTauClassPreference.scorerClass, R15InjuryTier.sum_endingClass,
    Fintype.sum_prod_type, sum_taskState, sum_readyGain, card_taskState, card_readyGain,
    reduceCtorEq]
  norm_num
  rw [Real.log_div (by norm_num : (15 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.log_div (by norm_num : (15 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
  rw [Real.log_div (by norm_num : (45 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  have log15 : Real.log 15 = Real.log 3 + Real.log 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have log45 : Real.log 45 = 2 * Real.log 3 + Real.log 5 := by
    rw [show (45 : ℝ) = 3 * (3 * 5) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have log4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [log15, log45, log4, Real.log_one]
  have log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have log_two_lt_three : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  linarith

def outerGainField : List Candidate := [⟨1, 1⟩, ⟨2, 1⟩]
def outerGainFacts : Target → GiraffeFacts
  | 1 => ⟨.ready, 0, 0⟩
  | 2 => ⟨.ready, 2, 0⟩
  | _ => ⟨.ready, 0, 0⟩
def outerFavoursGain : ReadyGain → ℚ
  | .none => 1
  | .one => 1
  | .several => 2
theorem outerFavoursGain_pos : ∀ gain, 0 < outerFavoursGain gain := by
  intro gain; cases gain <;> norm_num [outerFavoursGain]

theorem outerGainCascadeOne_reach_valid : ∀ candidate : Candidate,
    cascadePick outerCascadeOne outerGainFacts outerGainField = some candidate →
      0 ≤ candidate.reach ∧ candidate.reach ≤ 1 := by
  intro candidate picked
  norm_num [cascadePick, applySelectionCascade, applySelectionStep, outerCascadeOne,
    outerGainField] at picked
  subst candidate
  norm_num

theorem outerGainCascadeTwo_reach_valid : ∀ candidate : Candidate,
    cascadePick outerCascadeTwo outerGainFacts outerGainField = some candidate →
      0 ≤ candidate.reach ∧ candidate.reach ≤ 1 := by
  intro candidate picked
  norm_num [cascadePick, applySelectionCascade, applySelectionStep, outerCascadeTwo,
    outerGainField] at picked
  subst candidate
  norm_num

theorem outerGainModelOne :
    outerModel 0 outerExampleRelation outerGainFacts outerGainField outerExampleStateCounts
      outerExampleStateCounts_pos outerCascadeOne =
    (outerCountKernel (outerExampleStateCounts .ready) (outerExampleStateCounts_pos .ready),
      pickedOuterKernel (.focused, .none) 1) := by
  have picked : cascadePick outerCascadeOne outerGainFacts outerGainField =
      some (⟨1, 1⟩ : Candidate) := by
    norm_num [cascadePick, applySelectionCascade, applySelectionStep, outerCascadeOne,
      outerGainField]
  norm_num [outerModel, outerCascadeOne, outerGainFacts, outerGainField, outerExampleRelation,
    cascadePick, applySelectionCascade, applySelectionStep,
    R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass, readyGain, picked]

theorem outerGainModelTwo :
    outerModel 0 outerExampleRelation outerGainFacts outerGainField outerExampleStateCounts
      outerExampleStateCounts_pos outerCascadeTwo =
    (outerCountKernel (outerExampleStateCounts .ready) (outerExampleStateCounts_pos .ready),
      pickedOuterKernel (.focused, .several) 1) := by
  have picked : cascadePick outerCascadeTwo outerGainFacts outerGainField =
      some (⟨2, 1⟩ : Candidate) := by
    norm_num [cascadePick, applySelectionCascade, applySelectionStep, outerCascadeTwo,
      outerGainField]
  norm_num [outerModel, outerCascadeTwo, outerGainFacts, outerGainField, outerExampleRelation,
    cascadePick, applySelectionCascade, applySelectionStep,
    R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass, readyGain, picked]

theorem outer_ready_gain_matters :
    outerScore 0 outerExampleRelation outerGainFacts outerGainField
        outerExampleStateCounts outerExampleStateCounts_pos outerExampleC
        outerExampleC_probability outerFavoursGain outerFavoursGain_pos
        outerCascadeTwo <
      outerScore 0 outerExampleRelation outerGainFacts outerGainField
        outerExampleStateCounts outerExampleStateCounts_pos outerExampleC
        outerExampleC_probability outerFavoursGain outerFavoursGain_pos
        outerCascadeOne := by
  simp only [outerScore]
  rw [outerGainModelOne, outerGainModelTwo]
  have admitted (q : ProbabilityKernel Unit OuterOutcome) :
      PreferenceRiskSeparation.riskAdmissible q
        (outerPreferenceKernel outerExampleC outerExampleC_probability
          outerFavoursGain outerFavoursGain_pos) := by
    intro _ outcome _ _
    exact outerPreferenceKernel_mass_pos _ _ (by intro; norm_num [outerExampleC])
      _ outerFavoursGain_pos outcome
  split_ifs with h1 h2
  all_goals try { exact (h1 (admitted _)).elim }
  all_goals try { exact (h2 (admitted _)).elim }
  simp only [EReal.coe_lt_coe_iff]
  unfold CascadeEFE.stepG CascadeEFE.risk CascadeEFE.ambiguity CascadeEFE.entropy
    CascadeEFE.klTerm
  simp [outerPreferenceKernel, outerCountKernel,
    pickedOuterKernel, CascadeEFE.finiteKernel, CascadeEFE.push, CascadeEFE.stepG,
    CascadeEFE.risk, CascadeEFE.ambiguity, CascadeEFE.entropy, CascadeEFE.klTerm,
    PreferenceRiskSeparation.riskAdmissible, boundedReach,
    outerExampleRelation, outerGainFacts, outerGainField, outerFavoursGain,
    outerExampleStateCounts, outerExampleC, outerCascadeOne, outerCascadeTwo,
    cascadePick, applySelectionCascade, applySelectionStep, readyGain,
    R15StrategicTarget.outcomeClass, CTauClassPreference.scorerClass,
    R15InjuryTier.sum_endingClass, Fintype.sum_prod_type,
    sum_taskState, sum_readyGain, card_taskState, card_readyGain, reduceCtorEq]
  have log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have log_five_lt_ten : Real.log 5 < Real.log 10 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  linarith

#print axioms whatOthersWaitOnFirst_pick
#print axioms whatOthersWaitOnFirst_none_of_no_ready

#print axioms outerScore_eq_stepG_of_finite
#print axioms outer_ambiguity_matters
#print axioms outer_ready_gain_matters

#print axioms moving_click_one_betaPrior
#print axioms moving_click_one_betaPrior_moved
#print axioms chosenCascade_score_le
#print axioms step_selection_some
#print axioms stateAfter_outerStateInvariant
#print axioms click_cascadeScores_eq_outerScore

#print axioms step_betaPrior_next
#print axioms click_betaPrior_constant_of_flat
#print axioms iteratePrecision_constant_F

end DarkTower.WarMachine.R20Step
