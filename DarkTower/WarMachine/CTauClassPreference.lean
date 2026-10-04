import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
the Clojure ratios; `classRisk` states the runtime Gibbs/KL formula over reals.

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

/-- Runtime `outcome-risk`: `D_KL(predicted || preference)`. As in the runtime,
zero predicted masses contribute zero. The runtime separately returns
`:infinite` if a positive predicted mass has zero preferred mass; the theorem
below concerns the strictly supported pre-horizon case. -/
noncomputable def classRisk (predicted preferred : Distribution) : ℝ :=
  ∑ ending : EndingClass,
    if predicted ending = 0 then 0
    else (predicted ending : ℝ) *
      Real.log ((predicted ending : ℝ) / (preferred ending : ℝ))

/-- The runtime's exact pre-horizon claim: deterministic not-yet-evaluated
prediction against unit preference has zero risk. -/
theorem waiting_point_mass_risk_zero :
    classRisk waitingPreference waitingPreference = 0 := by
  simp [classRisk, waitingPreference]

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
