import DarkTower.WarMachine.CTauClassPreference
import DarkTower.WarMachine.R15TemporalHierarchy
import Mathlib.Tactic

/-!
# R15 strategic target as a lower-level preference

In plain terms: the higher level decides what the lower level has to achieve
and leaves it free to choose how. Source: Parr et al. (2022), p. 204: higher levels
control lower ones “by setting their reference points or set-points (i.e., what
they have to achieve) by leaving them free to select the means to achieve them
rather than by setting or biasing the actions that the lower levels have to
perform.” The same source says that goal selection (C) can depend on higher
levels (p. 102), while high-level expected observations can separately form
empirical priors E over lower-level policies (pp. 94, 148–149).

Our reading is therefore: the strategic focus sets the tactical preference C,
not the tactical action. At Futon2 commit
`0f9587532031beb50a21091cc41cd10f4a16ff63`, `focus_receipt.clj/classify-target`
classifies a target relative to the retained focus; `cascade_decision.clj`
lines 896–904 maps focus, associated, and useful-elsewhere relations to focused,
related, and unrelated classes; and `class-observation-model` lines 502–530
scores those classes against terminal C = 55/35/5/5. A failure to reach a
target emits stop-the-line. Unknown relations remain unscored; the runtime
refuses them rather than inventing a class.

Thus “fixes” is a preference, not a constraint: terminal related and unrelated
outcomes retain positive mass. This module says neither how the strategic focus
is inferred nor how its own inference is scored. The counts of what worked
are not an argument of `tacticalPreference`: they enter selection as the habit
prior E (`R15HabitPrior`), not through this C schedule.

The runtime decision retains `:focus-status` with focus and per-target
classifications (`cascade_decision.clj` lines 1139–1155), the terminal
`:preference-schedule` (`lines 1178–1182`), and the class observation model
used by scoring. It does not currently retain one compact independently
verified record containing, for every candidate and every tau, focus, relation,
scored class, and the full preference vector. `StrategicTickConforms` states
the contract such a record must satisfy; it does not claim that today's receipt
already satisfies it.
-/

namespace DarkTower.WarMachine.R15StrategicTarget

open DarkTower.WarMachine.CTauClassPreference

/-- A runtime mission/excursion/ticket target identity, abstracted from its
string representation. -/
abbrev Target := Nat

/-- A strategic selection is the current retained `:focus`. -/
structure StrategicSelection where
  focus : Target
  deriving DecidableEq, Repr

/-- A tactical terminal observation: `none` means no target was reached;
`some target` names the reached target. -/
abbrev TacticalOutcome := Option Target

/-- Classify a tactical outcome relative to strategic focus. `relation focus
target` stands for the result of runtime `classify-target`. No reached target
is stop-the-line; an unrecognised relation remains `none` rather than becoming
a scored class. -/
def outcomeClass (focus : Target) (relation : Target → Target → TargetRelation) :
    TacticalOutcome → Option EndingClass
  | none => some .stopTheLine
  | some target => scorerClass (relation focus target)

/-- The C mass against which the tactical outcome is scored. The strategic
focus affects this mass only by changing the outcome's terminal class. -/
def tacticalPreference (focus : Target)
    (relation : Target → Target → TargetRelation) (horizon tau : Nat)
    (outcome : TacticalOutcome) : Option ℚ :=
  (outcomeClass focus relation outcome).map (classPreference horizon tau)

/-- General factorisation: once two focus/relation combinations induce the
same outcome class, they induce the same tactical preference. -/
theorem preference_depends_on_focus_only_through_class
    (focus₁ focus₂ : Target) (relation₁ relation₂ : Target → Target → TargetRelation)
    (horizon tau : Nat) (outcome : TacticalOutcome)
    (sameClass : outcomeClass focus₁ relation₁ outcome =
      outcomeClass focus₂ relation₂ outcome) :
    tacticalPreference focus₁ relation₁ horizon tau outcome =
      tacticalPreference focus₂ relation₂ horizon tau outcome := by
  unfold tacticalPreference
  rw [sameClass]

/-- Example relation: the selected focus itself is focused; every other target
is useful elsewhere. -/
def focusOrElsewhere (focus target : Target) : TargetRelation :=
  if focus = target then .focus else .usefulElsewhere

/-- The same concrete outcome receives 55/100 under focus 7 and 5/100 under
focus 8. This witnesses higher-level selection changing lower-level C. -/
theorem changing_focus_changes_terminal_preference :
    tacticalPreference 7 focusOrElsewhere 2 2 (some 7) = some (55 / 100) ∧
    tacticalPreference 8 focusOrElsewhere 2 2 (some 7) = some (5 / 100) := by
  norm_num [tacticalPreference, outcomeClass, focusOrElsewhere, scorerClass,
    classPreference, terminalPreference]

/-- Induce a class distribution from a finite outcome support and a predicted
mass over concrete target outcomes. Unknown relations contribute to no scored
class, matching the runtime refusal rather than silently allocating mass. -/
def inducedClassDistribution (focus : Target)
    (relation : Target → Target → TargetRelation) (outcomes : List TacticalOutcome)
    (predicted : TacticalOutcome → ℚ) : Distribution :=
  fun ending => (outcomes.filterMap fun outcome =>
    if outcomeClass focus relation outcome = some ending
    then some (predicted outcome) else none).sum

/-- Policies with equal predicted outcome distributions induce equal class
distributions, whatever their internal means or action sequences. -/
theorem equal_outcomes_equal_class_distributions {Policy : Type*}
    (focus : Target) (relation : Target → Target → TargetRelation)
    (outcomes : List TacticalOutcome) (prediction : Policy → TacticalOutcome → ℚ)
    (first second : Policy)
    (sameOutcomes : ∀ outcome, prediction first outcome = prediction second outcome) :
    inducedClassDistribution focus relation outcomes (prediction first) =
      inducedClassDistribution focus relation outcomes (prediction second) := by
  funext ending
  simp only [inducedClassDistribution]
  congr 1
  apply List.filterMap_congr
  intro outcome _member
  split <;> simp_all

/-- Consequently, equal predicted outcomes have equal class risk against the
same strategic preference: C does not prescribe the policies' means. -/
theorem equal_outcomes_equal_risk {Policy : Type*}
    (focus : Target) (relation : Target → Target → TargetRelation)
    (outcomes : List TacticalOutcome) (prediction : Policy → TacticalOutcome → ℚ)
    (first second : Policy)
    (sameOutcomes : ∀ outcome, prediction first outcome = prediction second outcome)
    (preferred : Distribution) :
    classRisk (inducedClassDistribution focus relation outcomes (prediction first)) preferred =
      classRisk (inducedClassDistribution focus relation outcomes (prediction second)) preferred := by
  rw [equal_outcomes_equal_class_distributions focus relation outcomes prediction first second
    sameOutcomes]

/-- “Fixes” is not a hard constraint: related and unrelated terminal outcomes
both retain strictly positive preference mass. -/
theorem terminal_nonfocus_outcomes_remain_possible (horizon : Nat) :
    0 < classPreference horizon horizon .related ∧
    0 < classPreference horizon horizon .unrelated := by
  norm_num [classPreference, terminalPreference]

/-- Before the horizon, strategic focus contributes no preference mass to any
run-ending scored class. -/
theorem before_horizon_focus_has_no_terminal_mass
    (focus : Target) (relation : Target → Target → TargetRelation)
    (horizon tau target : Nat) (before : tau < horizon)
    (known : ∃ ending, outcomeClass focus relation (some target) = some ending) :
    tacticalPreference focus relation horizon tau (some target) = some 0 := by
  rcases known with ⟨ending, classified⟩
  have notWaiting : ending ≠ .notYetEvaluated := by
    intro waiting
    subst ending
    cases hrel : relation focus target <;>
      simp [outcomeClass, scorerClass, hrel] at classified
  simp [tacticalPreference, classified,
    before_horizon_all_mass_waiting horizon tau before, waitingPreference]

/-- One candidate's retained target relation and class used by scoring. -/
structure CandidateClassReceipt where
  target : Target
  recordedRelation : TargetRelation
  scoredClass : Option EndingClass
  deriving DecidableEq, Repr

/-- Proposed joined tick receipt. `preferenceAt` stands for the model's
per-tau `:class-preference`; the other fields stand for the retained focus,
horizon, target classifications, and classes consumed by scoring. -/
structure StrategicTickRecord where
  focus : Target
  horizon : Nat
  candidates : List CandidateClassReceipt
  preferenceAt : Nat → Distribution

/-- Every scored class is the class of its recorded relation to this focus,
and every in-horizon preference vector is the canonical C schedule. -/
def StrategicTickConforms (record : StrategicTickRecord) : Prop :=
  (∀ candidate ∈ record.candidates,
    candidate.scoredClass = outcomeClass record.focus
      (fun _ _ => candidate.recordedRelation) (some candidate.target)) ∧
  (∀ tau, 1 ≤ tau → tau ≤ record.horizon →
    record.preferenceAt tau = classPreference record.horizon tau)

def goodCandidate : CandidateClassReceipt :=
  ⟨7, .focus, some .focused⟩

def conformingTick : StrategicTickRecord :=
  ⟨7, 2, [goodCandidate], classPreference 2⟩

theorem conformingTick_accepts : StrategicTickConforms conformingTick := by
  constructor
  · intro candidate member
    simp [conformingTick, goodCandidate] at member
    subst candidate
    simp [outcomeClass, scorerClass]
  · intro tau _positive _within
    rfl

/-- Control: useful-elsewhere cannot be scored as focused. -/
def wrongClassTick : StrategicTickRecord :=
  ⟨7, 2, [⟨9, .usefulElsewhere, some .focused⟩], classPreference 2⟩

theorem wrongClassTick_rejected : ¬ StrategicTickConforms wrongClassTick := by
  intro conforms
  have classified := conforms.1
    (⟨9, .usefulElsewhere, some .focused⟩ : CandidateClassReceipt)
    (by simp [wrongClassTick])
  simp [outcomeClass, scorerClass] at classified

/-- Control: terminal weights used at tau 1 of horizon 2 violate the schedule. -/
def earlyTerminalTick : StrategicTickRecord :=
  ⟨7, 2, [goodCandidate], fun _ => terminalPreference⟩

theorem earlyTerminalTick_rejected : ¬ StrategicTickConforms earlyTerminalTick := by
  intro conforms
  have schedule := conforms.2 1 (by norm_num) (by norm_num [earlyTerminalTick])
  have focused := congrFun schedule EndingClass.focused
  norm_num [earlyTerminalTick, classPreference, terminalPreference, waitingPreference] at focused

end DarkTower.WarMachine.R15StrategicTarget
