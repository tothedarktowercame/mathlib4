import DarkTower.WarMachine.R20Step
import DarkTower.WarMachine.GOverCascades

/-!
# Selection G over cascades

SPECIFICATION DIRECTION (Joe, 2026-11-13; proposal
`futon2/holes/labs/P-selection-g-over-cascades-2026-11-13.md`, class route).

A selection run's G is the canonical cascade G, `GOverCascades.cascadeGrainG`, not
the pick-only `R20Step.outerModel`. Joe: "it is G over policies, so a different
cascade (including a different pattern) should have a different G even if it
chooses the same ticket". `outerModel` reads only whole-task facts of the pick, so
two cascades with one pick had one G whatever their patterns; that is the
composition blindness `GOverCascades.compositionBlind_cannot_separate` rules out.

A selection policy keeps both its executable steps (which ticket it picks,
unchanged from `R20Step.cascadePick`) and the task-selection patterns it enacts
(`futon3/library/task-selection/executable-steps.edn`, `:patterns`). Each pattern
is interpreted from its own `@guard` (consumes / forbids) and `@predicts`
(produces); θ = 1 and Beta(1, 1) counts are documented defaults, fixed
(Joe: "We don't need it to self-improve").

Class route: the observation keeps today's ending classes. The selected task's
relation class to focus is observed once the selection has established that the
task can begin (`canBegin`); before that the ending is `notYetEvaluated`; with no
pick it is `stopTheLine`. A cascade therefore enters G through the token
trajectory its patterns produce and through the novelty of the patterns that can
fire, which `cascadeGrainG` sums over one horizon (da Costa et al. 2020 eq. 42).
-/

namespace DarkTower.WarMachine.SelectionGOverCascades

open DarkTower.WarMachine
open CascadeEFE CascadeTransition CascadeCoApplyGNovelty Holes
open R20Step

noncomputable section

/-- The executable task-selection patterns (`executable-steps.edn` v3). -/
inductive SelectionPattern where
  | onlyWhatCanStartNow
  | prepareTheGround
  | whatOthersWaitOnFirst
  | findOutBeforeBuilding
  | servesAWay
  deriving DecidableEq, Repr, Fintype

/-- Facts about a selected task (guards) and what a pattern establishes
(`@predicts`). -/
inductive SelectionToken where
  | ready | undetermined | unblocks | cone | placedWork | unmetNeed
  | namedLaterItem | nonWorkPlacement
  | canBegin | readyCountRises | laterItemReshaped | designDecided | reasonNamesWay
  deriving DecidableEq, Repr, Fintype

open SelectionToken

/-- A task-selection pattern interpretation with θ = 1 (documented default). -/
def mkPattern (consumes forbids produces : Finset SelectionToken) :
    InterpretedPattern SelectionToken where
  consumes := consumes
  produces := produces
  forbids := forbids
  theta := 1
  theta_nonneg := by norm_num
  theta_le_one := le_refl _

/-- Each pattern from its `@guard` and `@predicts`:
- only-what-can-start-now: "every selected task can begin when it is dispatched";
- what-others-wait-on-first: "the number of ready items rises by the predicted count";
- prepare-the-ground: "the later item … uses or is reshaped by this work";
- find-out-before-building: "the answer changes or confirms the build's design";
- serves-a-way: "the selected task's reason names the way it serves". -/
def interpret : SelectionPattern → InterpretedPattern SelectionToken
  | .onlyWhatCanStartNow => mkPattern {ready} {unmetNeed} {canBegin}
  | .whatOthersWaitOnFirst => mkPattern {ready, unblocks} ∅ {readyCountRises}
  | .prepareTheGround => mkPattern {cone, namedLaterItem} ∅ {laterItemReshaped}
  | .findOutBeforeBuilding => mkPattern {undetermined} ∅ {designDecided}
  | .servesAWay => mkPattern {ready, placedWork} {nonWorkPlacement} {reasonNamesWay}

/-- Whole-task facts a selection pattern's guard reads. -/
structure SelectionFacts where
  giraffe : GiraffeFacts
  placedWork : Bool
  unmetNeed : Bool
  namedLaterItem : Bool
  nonWorkPlacement : Bool

/-- The selected task's facts as tokens. -/
def initialTokens (f : SelectionFacts) : Finset SelectionToken :=
  (if f.giraffe.status = .ready then {ready} else ∅) ∪
  (if f.giraffe.status = .undetermined then {undetermined} else ∅) ∪
  (if 0 < f.giraffe.unblocks then {unblocks} else ∅) ∪
  (if 0 < f.giraffe.cone then {cone} else ∅) ∪
  (if f.placedWork then {placedWork} else ∅) ∪
  (if f.unmetNeed then {unmetNeed} else ∅) ∪
  (if f.namedLaterItem then {namedLaterItem} else ∅) ∪
  (if f.nonWorkPlacement then {nonWorkPlacement} else ∅)

/-- A selection policy: the patterns it enacts and the steps that pick. -/
structure SelectionPolicy where
  patterns : List SelectionPattern
  steps : SelectionCascade

/-- The ending class observed for the pick (class route). -/
def pickEnding (focus : Target) (relation : Target → Target → R20Step.TargetRelation) :
    Option Candidate → CTauClassPreference.EndingClass
  | none => .stopTheLine
  | some c => (R15StrategicTarget.outcomeClass focus relation (some c.target)).getD .notYetEvaluated

/-- Deterministic observation: the pick's class once it can begin. -/
def observedClass (ending : CTauClassPreference.EndingClass) (s : Finset SelectionToken) : CTauClassPreference.EndingClass :=
  if canBegin ∈ s then ending else .notYetEvaluated

def observationKernel (ending : CTauClassPreference.EndingClass) :
    ProbabilityKernel (Finset SelectionToken) CTauClassPreference.EndingClass :=
  finiteKernel (fun s e => if observedClass ending s = e then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro s; simp)

/-- The canonical candidate for one selection policy on one field. -/
def selectionCandidate (policy : SelectionPolicy) (facts : Target → SelectionFacts)
    (focus : Target) (relation : Target → Target → R20Step.TargetRelation)
    (field : List Candidate) : CandidateN (Fin policy.patterns.length) SelectionToken :=
  let pick := cascadePick policy.steps (fun t => (facts t).giraffe) field
  { patterns := some (fun i => interpret (policy.patterns.get i))
    initial := point (match pick with
      | none => ∅
      | some c => initialTokens (facts c.target))
    observation := observationKernel (pickEnding focus relation pick)
    counts := fun _ => (1, 1)
    counts_pos := fun _ => ⟨by norm_num, by norm_num⟩ }

/-- Selection-run G: the canonical cascade G of the policy's candidate. -/
def selectionG (policy : SelectionPolicy) (facts : Target → SelectionFacts)
    (focus : Target) (relation : Target → Target → R20Step.TargetRelation)
    (field : List Candidate) (H : ℕ) (c : Fin H → ProbabilityKernel Unit CTauClassPreference.EndingClass) :
    Except CascadeCoApplyG.Refusal ℝ :=
  GOverCascades.cascadeGrainG (selectionCandidate policy facts focus relation field) H c

/-! ## The ladder case (Lucy, 2026-11-13)

Tickets 08 and 09 had equal Giraffe facts (ready, no unblocks, no cone); 09 alone
carried an A1 work placement. `serves-a-way` fires on 09's tokens and not on 08's,
so a cascade enacting it has a different enabled frontier, trajectory and novelty
from one that does not, even where the picks' Giraffe facts coincide. -/

theorem servesAWay_fires_on_placed_work :
    CascadeTransition.guard (interpret .servesAWay) {ready, placedWork} := by
  unfold CascadeTransition.guard interpret mkPattern
  decide

theorem servesAWay_idle_without_placement :
    ¬ CascadeTransition.guard (interpret .servesAWay) {ready} := by
  unfold CascadeTransition.guard interpret mkPattern
  decide

theorem onlyWhatCanStartNow_fires_on_ready :
    CascadeTransition.guard (interpret .onlyWhatCanStartNow) {ready} := by
  unfold CascadeTransition.guard interpret mkPattern
  decide

end
end DarkTower.WarMachine.SelectionGOverCascades
