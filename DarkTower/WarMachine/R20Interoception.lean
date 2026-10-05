import DarkTower.WarMachine.OutcomeRiskKL
import Mathlib.Tactic

/-!
# R20 interoception

The machine holds expectations about its own running, expressed as ranges its
internal readings should stay in. A reading outside its viable range is a
surprise. No special response rule is required: staying in range is a
preference like any other, so an ordinary policy expected to restore the
reading has lower risk than one expected to leave it out of range.

Parr et al. (2022), pp. 215–216 describes a generative model of the body's
inside and says viable physiological ranges can be specified as priors over
interoceptive observations. Interoceptive prediction errors may be corrected
by a reflex or by increasingly sophisticated, goal-directed policies. Its B.7
then places expected free energy in ordinary policy selection. This module
states the software analogue without importing the discarded tripwire
implementation or its records.

`OutcomeRiskKL.outcomeRisk` is the canonical extended-real KL risk, but its
carrier is a vertex-indexed `Holes.PredictiveOutcomeKernel`. A single finite
interoceptive modality has no graph vertex. `interoceptiveRisk` therefore gives
the identical finite-Fintype formula locally: `D_KL[P || C]`, with `⊤` exactly
when P puts positive mass where C is zero.

Not stated here: how an out-of-range observation changes policy precision
through the ordinary update (Friston 2017, section 2.6), or how strongly each
sensor channel is trusted (likelihood precision, Parr B.2.4). A source search
over `futon2/src/futon2/aif/wm/` and the observation/scoring namespaces required
by `wm/cascade_decision.clj` found class-emission, progress, and token outcome
models, but no model treating machine-internal state as an observation modality
with a viable-range preference.
-/

namespace DarkTower.WarMachine.R20Interoception

open scoped BigOperators

variable {Reading : Type*} [Fintype Reading] [DecidableEq Reading]

/-- A probability mass over one finite interoceptive reading modality. -/
abbrev Distribution (Reading : Type*) := Reading → ℝ

def Nonnegative (P : Distribution Reading) : Prop := ∀ i, 0 ≤ P i
def Normalized (P : Distribution Reading) : Prop := ∑ i, P i = 1

/-- Viable readings are strictly preferred to every non-viable reading. -/
def PrefersViable (C : Distribution Reading) (viable : Finset Reading) : Prop :=
  ∀ v ∈ viable, ∀ n ∉ viable, C n < C v

/-- A hard viable range assigns zero preference to every non-viable reading. -/
def HardRange (C : Distribution Reading) (viable : Finset Reading) : Prop :=
  ∀ n ∉ viable, C n = 0

def Unsupported (P C : Distribution Reading) : Prop :=
  ∃ i, 0 < P i ∧ C i = 0

noncomputable def finiteRisk (P C : Distribution Reading) : ℝ :=
  ∑ i, if P i = 0 then 0 else P i * Real.log (P i / C i)

/-- Interoceptive risk, identical in formula to
`OutcomeRiskKL.outcomeRisk` on this finite non-vertex carrier. -/
noncomputable def interoceptiveRisk (P C : Distribution Reading) : EReal := by
  classical
  exact if Unsupported P C then ⊤ else (finiteRisk P C : EReal)

def pointMass (reading : Reading) : Distribution Reading :=
  fun i => if i = reading then 1 else 0

theorem pointMass_risk_of_positive {C : Distribution Reading} {reading : Reading}
    (positive : 0 < C reading) :
    interoceptiveRisk (pointMass reading) C = ((-Real.log (C reading) : ℝ) : EReal) := by
  have supported : ¬ Unsupported (pointMass reading) C := by
    rintro ⟨i, pi, zero⟩
    by_cases same : i = reading
    · subst i; exact positive.ne' zero
    · simp [pointMass, same] at pi
  rw [interoceptiveRisk, if_neg supported]
  congr 1
  simp [finiteRisk, pointMass, Real.log_inv]

theorem pointMass_risk_of_zero {C : Distribution Reading} {reading : Reading}
    (zero : C reading = 0) :
    interoceptiveRisk (pointMass reading) C = ⊤ := by
  rw [interoceptiveRisk, if_pos]
  exact ⟨reading, by simp [pointMass], zero⟩

/-- Ordinary risk prefers certain restoration to a viable reading over a
certain non-viable outcome; no special repair rule is used. -/
theorem viable_point_has_lower_risk {C : Distribution Reading}
    {viable : Finset Reading} {restored outOfRange : Reading}
    (preference : PrefersViable C viable)
    (restoredViable : restored ∈ viable) (outside : outOfRange ∉ viable)
    (restoredPositive : 0 < C restored) (outsidePositive : 0 < C outOfRange) :
    interoceptiveRisk (pointMass restored) C <
      interoceptiveRisk (pointMass outOfRange) C := by
  rw [pointMass_risk_of_positive restoredPositive,
    pointMass_risk_of_positive outsidePositive, EReal.coe_lt_coe_iff]
  have masses := preference restored restoredViable outOfRange outside
  have logs := Real.strictMonoOn_log outsidePositive restoredPositive masses
  linarith

theorem hard_range_outside_is_infinite {C : Distribution Reading}
    {viable : Finset Reading} {outside : Reading}
    (hard : HardRange C viable) (notViable : outside ∉ viable) :
    interoceptiveRisk (pointMass outside) C = ⊤ :=
  pointMass_risk_of_zero (hard outside notViable)

/-! ## Surprise belongs to predictions, not preferences -/

/-- Surprisal of an observed reading under the model's predictive mass. -/
noncomputable def surprisal (P : Distribution Reading) (reading : Reading) : EReal :=
  if P reading = 0 then ⊤ else ((-Real.log (P reading) : ℝ) : EReal)

theorem zero_mass_surprisal_top {P : Distribution Reading} {reading : Reading}
    (zero : P reading = 0) : surprisal P reading = ⊤ := by
  simp [surprisal, zero]

/-- A per-reading consequence of expecting to remain in range: when an
out-of-range reading has predictive mass at most epsilon, its surprisal is at
least `-log epsilon`. The aggregate viable-mass premise implies this bound for
each outside reading by elementary probability accounting; the local theorem
keeps that accounting separate from the information quantity. -/
theorem outside_surprisal_lower_bound {P : Distribution Reading} {reading : Reading}
    {epsilon : ℝ} (epsilonPositive : 0 < epsilon)
    (massBound : P reading ≤ epsilon) (massNonnegative : 0 ≤ P reading) :
    ((-Real.log epsilon : ℝ) : EReal) ≤ surprisal P reading := by
  by_cases zero : P reading = 0
  · simp [surprisal, zero]
  · rw [surprisal, if_neg zero, EReal.coe_le_coe_iff]
    have readingPositive : 0 < P reading := lt_of_le_of_ne massNonnegative (Ne.symm zero)
    have logs := Real.strictMonoOn_log.monotoneOn
      (by exact readingPositive) (by exact epsilonPositive) massBound
    linarith

/-! Preference and expectation are independent objects. -/

inductive GaugeReading where | inRange | alarm deriving DecidableEq, Fintype, Repr

def viableGauge : Finset GaugeReading := {.inRange}
noncomputable def gaugePreference : Distribution GaugeReading
  | .inRange => 9 / 10
  | .alarm => 1 / 10
noncomputable def expectedAlarm : Distribution GaugeReading
  | .inRange => 1 / 10
  | .alarm => 9 / 10
noncomputable def surprisingRecovery : Distribution GaugeReading
  | .inRange => 1 / 10
  | .alarm => 9 / 10

/-- Alarm can be expected (low surprisal) and still unpreferred, so expectation
does not remove the ordinary preference pressure to repair it. Conversely an
in-range reading may be preferred yet surprising. -/
theorem expectation_and_preference_differ :
    expectedAlarm .alarm > expectedAlarm .inRange ∧
    gaugePreference .alarm < gaugePreference .inRange ∧
    surprisingRecovery .inRange < surprisingRecovery .alarm ∧
    gaugePreference .inRange > gaugePreference .alarm := by
  norm_num [expectedAlarm, surprisingRecovery, gaugePreference]

/-! ## Tick-record conformance -/

structure PolicyReceipt (Reading : Type*) where
  prediction : Distribution Reading
  reportedRisk : EReal

structure InteroceptiveTickRecord (Reading : Type*) where
  viable : Finset Reading
  preference : Distribution Reading
  candidates : List (PolicyReceipt Reading)

def InteroceptiveTickConforms (record : InteroceptiveTickRecord Reading) : Prop :=
  PrefersViable record.preference record.viable ∧
  ∀ candidate ∈ record.candidates,
    candidate.reportedRisk = interoceptiveRisk candidate.prediction record.preference

noncomputable def goodInteroceptiveTick : InteroceptiveTickRecord GaugeReading :=
  { viable := viableGauge, preference := gaugePreference
    candidates :=
      [⟨pointMass .inRange, interoceptiveRisk (pointMass .inRange) gaugePreference⟩,
       ⟨pointMass .alarm, interoceptiveRisk (pointMass .alarm) gaugePreference⟩] }

theorem goodInteroceptiveTick_conforms :
    InteroceptiveTickConforms goodInteroceptiveTick := by
  constructor
  · intro v hv n hn
    change v ∈ viableGauge at hv
    change n ∉ viableGauge at hn
    change gaugePreference n < gaugePreference v
    have hv' : v = .inRange := by simpa [viableGauge] using hv
    subst v
    cases n with
    | inRange => simp [viableGauge] at hn
    | alarm => norm_num [gaugePreference]
  · intro candidate member
    simp [goodInteroceptiveTick] at member
    rcases member with rfl | rfl <;> rfl

/-- Control: reversing viable/non-viable preference violates homeostatic C. -/
noncomputable def reversedPreference : Distribution GaugeReading
  | .inRange => 1 / 10
  | .alarm => 9 / 10

noncomputable def reversedPreferenceTick : InteroceptiveTickRecord GaugeReading :=
  { viable := viableGauge, preference := reversedPreference, candidates := [] }

theorem reversedPreferenceTick_rejected :
    ¬ InteroceptiveTickConforms reversedPreferenceTick := by
  intro conforms
  have wrong := conforms.1 .inRange (by simp [reversedPreferenceTick, viableGauge])
    .alarm (by simp [reversedPreferenceTick, viableGauge])
  norm_num [reversedPreferenceTick, reversedPreference, gaugePreference] at wrong

/-- Control: distinct certain predictions cannot both report the same finite
interoceptive risk under the 9/10 versus 1/10 preference. -/
noncomputable def equalRiskTick : InteroceptiveTickRecord GaugeReading :=
  { viable := viableGauge, preference := gaugePreference
    candidates := [⟨pointMass .inRange, 0⟩, ⟨pointMass .alarm, 0⟩] }

theorem equalRiskTick_rejected : ¬ InteroceptiveTickConforms equalRiskTick := by
  intro conforms
  have alarm := conforms.2 ⟨pointMass .alarm, 0⟩ (by simp [equalRiskTick])
  have risk := pointMass_risk_of_positive
    (C := gaugePreference) (reading := GaugeReading.alarm) (by norm_num [gaugePreference])
  simp [equalRiskTick] at alarm
  rw [risk] at alarm
  have logPositive : 0 < -Real.log ((1 : ℝ) / 10) := by
    have := Real.log_neg (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (1 : ℝ) / 10 < 1)
    linarith
  have coeNonzero : (((-Real.log ((1 : ℝ) / 10)) : ℝ) : EReal) ≠ 0 := by
    exact EReal.coe_ne_zero.mpr (ne_of_gt logPositive)
  exact coeNonzero alarm.symm

end DarkTower.WarMachine.R20Interoception
