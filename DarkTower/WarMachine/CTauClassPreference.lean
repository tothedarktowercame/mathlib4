import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic

/-!
# C_tau class preference schedule

This module states the class preference schedule built by
`class-preference-weights` and `class-observation-model` in
`futon2/src/futon2/aif/wm/cascade_decision.clj`, consumed directly by the
`:class-emission` path in
`futon2/src/futon2/aif/cascade_observation_scoring.clj`, and scored through
`cascade-model-manifest/outcome-risk`, read at Futon2 commit
`0f9587532031beb50a21091cc41cd10f4a16ff63`.

The four terminal weights are Joe's fixed ruling of 2026-09-22: focused 55/100,
related 35/100, unrelated 5/100, and stop-the-line 5/100. Before the horizon,
all preference mass is on `:ending/not-yet-evaluated`. Exact rationals model
the Clojure ratios; `classRisk` states the runtime Gibbs/KL formula in the
extended reals, with `⊤` where the runtime returns `:infinite`.

`classRisk` has the shape of `OutcomeRiskKL.outcomeRisk`, which the runtime
function's docstring names as its Lean counterpart, but it is a separate
definition over this module's five-class distributions. It is not proved equal
to `outcomeRisk`: that needs the class distributions presented as the `Holes`
predictive-kernel and preference carriers, which is not done here.

An unresolved target relation maps to unknown, not to one of the five scored
classes. At runtime `observation_model.clj` refuses it as
`:class-unknown-no-scalar-g` and retains possible terminal costs; it does not
assign stop-the-line, uniform, averaged, or worst-case scalar G.

This module leaves out CTAU-TOKEN and `preference-member`, production of a
target's relation by `classify-target`, joint-decision ranking, precision
carry, and deterministic class emission from token states. It records the
ruled 55/35/5/5 constant but does not establish that it is the right
preference.
-/

namespace DarkTower.WarMachine.CTauClassPreference

/-- Runtime `:class-universe`, in its declared order. -/
inductive EndingClass where
  | focused
  | related
  | unrelated
  | stopTheLine
  | notYetEvaluated
  deriving DecidableEq, Repr, Fintype

/-- A runtime per-tau `:class-preference` map represented as total exact mass
over the five class keys. -/
abbrev Distribution := EndingClass → ℚ

/-- Joe's terminal `class-preference-weights`. -/
def terminalPreference : Distribution
  | .focused => 55 / 100
  | .related => 35 / 100
  | .unrelated => 5 / 100
  | .stopTheLine => 5 / 100
  | .notYetEvaluated => 0

/-- Unit mass on runtime `:ending/not-yet-evaluated`. -/
def waitingPreference : Distribution
  | .notYetEvaluated => 1
  | _ => 0

/-- Runtime `:class-preference` at step `tau` for model `:horizon` H. The
runtime constructs only tau in `1 .. H`; the function is total so the domain
assumptions remain explicit in theorems. -/
def classPreference (horizon tau : Nat) : Distribution :=
  if tau = horizon then terminalPreference else waitingPreference

def totalMass (distribution : Distribution) : ℚ :=
  distribution .focused + distribution .related + distribution .unrelated +
    distribution .stopTheLine + distribution .notYetEvaluated

def Nonnegative (distribution : Distribution) : Prop :=
  ∀ ending, 0 ≤ distribution ending

def ProbabilityDistribution (distribution : Distribution) : Prop :=
  Nonnegative distribution ∧ totalMass distribution = 1

theorem terminalPreference_total : totalMass terminalPreference = 1 := by
  norm_num [totalMass, terminalPreference]

theorem waitingPreference_total : totalMass waitingPreference = 1 := by
  norm_num [totalMass, waitingPreference]

theorem classPreference_probability (horizon tau : Nat)
    (_positiveHorizon : 1 ≤ horizon) (_positiveTau : 1 ≤ tau)
    (_withinHorizon : tau ≤ horizon) :
    ProbabilityDistribution (classPreference horizon tau) := by
  by_cases terminal : tau = horizon
  · subst tau
    constructor
    · intro ending
      fin_cases ending <;> norm_num [classPreference, terminalPreference]
    · simpa [classPreference] using terminalPreference_total
  · constructor
    · intro ending
      fin_cases ending <;> simp [classPreference, terminal, waitingPreference]
    · simpa [classPreference, terminal] using waitingPreference_total

theorem before_horizon_all_mass_waiting (horizon tau : Nat) (before : tau < horizon) :
    classPreference horizon tau = waitingPreference := by
  simp [classPreference, Nat.ne_of_lt before]

theorem terminal_weights (horizon : Nat) :
    classPreference horizon horizon .focused = 55 / 100 ∧
    classPreference horizon horizon .related = 35 / 100 ∧
    classPreference horizon horizon .unrelated = 5 / 100 ∧
    classPreference horizon horizon .stopTheLine = 5 / 100 ∧
    classPreference horizon horizon .notYetEvaluated = 0 := by
  norm_num [classPreference, terminalPreference]

theorem terminal_order (horizon : Nat) :
    classPreference horizon horizon .focused > classPreference horizon horizon .related ∧
    classPreference horizon horizon .related > classPreference horizon horizon .unrelated ∧
    classPreference horizon horizon .unrelated =
      classPreference horizon horizon .stopTheLine := by
  norm_num [classPreference, terminalPreference]

inductive TargetRelation where
  | focus
  | associated
  | usefulElsewhere
  | other (code : Nat)
  deriving DecidableEq, Repr

/-- Runtime `scorer-class`. `none` represents runtime `:unknown`, which is not
a member of `:class-universe`. -/
def scorerClass : TargetRelation → Option EndingClass
  | .focus => some .focused
  | .associated => some .related
  | .usefulElsewhere => some .unrelated
  | .other _ => none

theorem scorerClass_named_relations :
    scorerClass .focus = some .focused ∧
    scorerClass .associated = some .related ∧
    scorerClass .usefulElsewhere = some .unrelated := by
  decide

theorem scorerClass_other_unknown (code : Nat) :
    scorerClass (.other code) = none := by
  simp [scorerClass]

/-- The finite branch of runtime `outcome-risk`: the Gibbs sum
`Σ q(o) · ln(q(o)/c(o))` over classes with predicted mass. The runtime sums
over `(pos? p)`; for the non-negative masses of a distribution that is the
same as leaving out `p = 0`. -/
noncomputable def finiteClassRisk (predicted preferred : Distribution) : ℝ :=
  ∑ ending : EndingClass,
    if predicted ending = 0 then 0
    else (predicted ending : ℝ) *
      Real.log ((predicted ending : ℝ) / (preferred ending : ℝ))

/-- The runtime's `:infinite` condition: some class has positive predicted
mass and zero preferred mass. -/
def Unsupported (predicted preferred : Distribution) : Prop :=
  ∃ ending, 0 < predicted ending ∧ preferred ending = 0

open Classical in
/-- Runtime `outcome-risk`: `D_KL(predicted || preference)` in the extended
reals. `⊤` stands for the runtime's `:infinite`, returned exactly when the
prediction is `Unsupported` by the preference; otherwise the Gibbs sum. A
real-valued definition would return a finite number in that case, because
`Real.log 0 = 0`. -/
noncomputable def classRisk (predicted preferred : Distribution) : EReal :=
  if Unsupported predicted preferred then ⊤
  else ((finiteClassRisk predicted preferred : ℝ) : EReal)

theorem classRisk_eq_top_iff (predicted preferred : Distribution) :
    classRisk predicted preferred = ⊤ ↔ Unsupported predicted preferred := by
  unfold classRisk
  split_ifs with unsupported
  · simp [unsupported]
  · simp [unsupported]

theorem waiting_is_supported : ¬ Unsupported waitingPreference waitingPreference := by
  rintro ⟨ending, positive, zero⟩
  cases ending <;> simp_all [waitingPreference]

/-- The runtime's exact pre-horizon claim: deterministic not-yet-evaluated
prediction against unit preference has zero risk. -/
theorem waiting_point_mass_risk_zero :
    classRisk waitingPreference waitingPreference = 0 := by
  have finite : finiteClassRisk waitingPreference waitingPreference = 0 := by
    simp [finiteClassRisk, waitingPreference]
  simp [classRisk, waiting_is_supported, finite]

/-- The case a real-valued risk would hide: a run-ending prediction scored
against the pre-horizon preference puts mass where the preference has none,
and its risk is `⊤`, not a number. -/
theorem terminal_against_waiting_risk_top :
    classRisk terminalPreference waitingPreference = ⊤ := by
  rw [classRisk_eq_top_iff]
  exact ⟨.focused, by norm_num [terminalPreference], by simp [waitingPreference]⟩

theorem pre_horizon_risk_zero (horizon tau : Nat) (before : tau < horizon) :
    classRisk waitingPreference (classPreference horizon tau) = 0 := by
  rw [before_horizon_all_mass_waiting horizon tau before]
  exact waiting_point_mass_risk_zero

/-- Control A: emitting terminal weights one step early is observably not the
schedule. Horizon 2, tau 1 exhibits the difference on focused mass. -/
def oneStepEarlyPreference (horizon tau : Nat) : Distribution :=
  if tau + 1 = horizon then terminalPreference else classPreference horizon tau

theorem oneStepEarly_differs_at_horizon_two :
    oneStepEarlyPreference 2 1 .focused ≠ classPreference 2 1 .focused := by
  norm_num [oneStepEarlyPreference, classPreference, terminalPreference, waitingPreference]

/-- Control B: 55/35/5/10 is nonnegative but is not normalized. -/
def badTerminalPreference : Distribution
  | .focused => 55 / 100
  | .related => 35 / 100
  | .unrelated => 5 / 100
  | .stopTheLine => 10 / 100
  | .notYetEvaluated => 0

theorem badTerminalPreference_total : totalMass badTerminalPreference = 105 / 100 := by
  norm_num [totalMass, badTerminalPreference]

theorem badTerminalPreference_not_probability :
    ¬ ProbabilityDistribution badTerminalPreference := by
  intro probability
  have normalized := probability.2
  rw [badTerminalPreference_total] at normalized
  norm_num at normalized

/-- Control C: an unrecognized relation cannot become a scored class. -/
theorem unrecognized_relation_has_no_scored_class :
    ∀ code, ¬ ∃ ending, scorerClass (.other code) = some ending := by
  intro code
  rintro ⟨ending, mapped⟩
  simp [scorerClass] at mapped

end DarkTower.WarMachine.CTauClassPreference
