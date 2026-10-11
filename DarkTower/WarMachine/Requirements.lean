import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs
import Mathlib.Tactic
import DarkTower.WarMachine.IncrementalTaskFrontier

/-!
# Countable requirements for one War Machine run

Every field below denotes a finite population in the world or in one run
record.  This file states requirements over those facts; it does not claim
that today's runner exports them faithfully.
-/

namespace DarkTower.WarMachine.Requirements

open DarkTower.WarMachine.IncrementalTaskFrontier

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev Id := Nat

structure TargetConstruction where
  /-- Stable target ids sharing this exact slice/pool construction fact. The
  exporter may group targets only when all remaining fields are identical. -/
  targets : Finset Id
  /-- Pattern ids returned by query-time retrieval from the pinned library. -/
  slice : Finset Id
  /-- Pattern ids the constructor was actually permitted to use. -/
  pool : Finset Id
  /-- True exactly when the recorded slice was queried over the whole pinned library. -/
  sliceFromWholeLibrary : Bool
  /-- Number of extensionally distinct policies constructed for this target. -/
  policyCount : Nat
  deriving DecidableEq

structure Choice where
  /-- Stable id of the chosen open task. -/
  target : Id
  /-- Stable id/hash of the chosen arranged cascade. -/
  cascade : Id
  deriving DecidableEq

inductive RunOutcome where
  | changed | alreadySatisfied | question | refused | invalid | timedOut
  deriving DecidableEq, Repr

inductive InterpretationOrder where
  | selectionBeforeInterpretation
  | interpretationBeforeSelection
  deriving DecidableEq, Repr

structure GTerms where
  /-- Whether outcome risk contributed to every reported G. -/
  risk : Bool
  /-- Whether expected ambiguity contributed to every reported G. -/
  ambiguity : Bool
  /-- Whether expected information gain contributed to every reported G. -/
  informationGain : Bool
  deriving DecidableEq, Repr

/-- Explicitly declared policy-family preference semantics. There is no
`undeclared` constructor: absent or unknown runtime declarations are not
recomputable `RunFacts`. -/
inductive PreferenceSemantics where
  | terminalOnly | constant | progressive
  deriving DecidableEq, Repr

structure RunFacts where
  /-- Canonical ids of open missions; counted from the pinned mission registry. -/
  openMissions : Finset Id
  /-- Canonical ids of open excursions; counted from the pinned excursion registry. -/
  openExcursions : Finset Id
  /-- Canonical ids of open tickets; counted from the pinned ticket registry. -/
  openTickets : Finset Id
  /-- Task ids emitted by the decision enumerator in the selection certificate. -/
  enumeratedTasks : Finset Id
  /-- Enumerated target ids admitted to the scoring boundary. -/
  targetsReachingScoring : Finset Id
  /-- Target ids for which the run record carries a numeric G. -/
  targetsWithG : Finset Id
  /-- Number of pattern files in the pinned pattern-library manifest. -/
  libraryPatternCount : Nat
  /-- Per-target retrieval slice, constructor pool and policy coverage. -/
  targetConstruction : List TargetConstruction
  /-- Number of distinct patterns across pools the constructor could draw on. -/
  constructorPatternCount : Nat
  /-- Stable ids/hashes of all arranged cascades the constructor emitted. -/
  constructedCascades : Finset Id
  /-- Stable ids/hashes of the policies actually compared by the posterior. -/
  comparedPolicies : Finset Id
  /-- Constructed cascade ids for which the record has no numeric G. -/
  cascadesWithoutG : Finset Id
  /-- Number of future steps scored, read from the observation-model horizon. -/
  horizonLength : Nat
  /-- Zero-based horizon steps whose C-tau row states a real preference. -/
  preferenceSteps : Finset Nat
  /-- Horizon steps whose C-tau is graded by completed-progress count. -/
  gradedPreferenceSteps : Finset Nat
  /-- Whether this policy family declares progressive, rather than constant or
  terminal-only, preference semantics. -/
  preferenceSemantics : PreferenceSemantics
  /-- Terms that contributed to every reported policy G. -/
  gTerms : GTerms
  /-- Compared policies carrying a separately recorded risk term. -/
  policiesWithRiskTerm : Nat
  /-- Compared policies carrying a separately recorded ambiguity term. -/
  policiesWithAmbiguityTerm : Nat
  /-- Compared policies carrying a separately recorded expected-information term. -/
  policiesWithInformationTerm : Nat
  /-- Temporal order recorded for selection and target-specific interpretation. -/
  interpretationOrder : InterpretationOrder
  /-- Count of all `absent`, `not-supplied`, `status missing`, and typed-refusal
  values on the selection-to-terminal-receipt path. -/
  pathAbsenceCount : Nat
  /-- Previous run's selected target and arranged cascade. -/
  previousChoice : Choice
  /-- Previous run's typed terminal outcome. -/
  previousOutcome : RunOutcome
  /-- Digest of all inputs on which the previous choice depended. -/
  previousInputDigest : Id
  /-- Current run's selected target and arranged cascade. -/
  currentChoice : Choice
  /-- Digest of all inputs on which the current choice depended. -/
  currentInputDigest : Id
  /-- Stable ids of seats registered when selection ran. -/
  seatsAvailable : Finset Id
  /-- Stable ids of seats included in dispatch or behavior counts for the run. -/
  seatsUsed : Finset Id
  /-- Number of reachable pairs `(closed criterion, non-closing outcome)` in C. -/
  completionPreferencePairs : Nat
  /-- Number of those pairs on which C strictly prefers the criterion-closing outcome. -/
  completionPairsStrictlyPreferred : Nat
  /-- Trace pairs with equal terminal belief and pointwise earlier progress. -/
  earlierProgressPairs : Nat
  /-- Those pairs whose earlier trace has no greater cumulative normalized risk. -/
  earlierProgressNoGreaterRisk : Nat
  /-- Number of compared cascade pairs with the same pattern set and different arrangements. -/
  differentArrangementPairs : Nat
  /-- Number of those pairs represented as distinct policies, each with its own numeric G. -/
  arrangementPairsDistinguishedByG : Nat
  /-- Exact incremental refresh certificate for the current open-task frontier. -/
  frontierRefresh : RefreshCertificate
  /-- Winner certificate over the refreshed frontier and current tie law. -/
  frontierSelection : SelectionCertificate
  /-- Identity correspondence for cascades of the selected task only. -/
  selectedCascade : TargetCascadeCertificate
  deriving DecidableEq

def RunFacts.openTasks (r : RunFacts) : Finset Id :=
  r.openMissions ∪ r.openExcursions ∪ r.openTickets

def RunFacts.totalPolicies (r : RunFacts) : Nat :=
  (r.targetConstruction.map (fun tc => tc.targets.card * tc.policyCount)).sum

def RunFacts.maxSliceSize (r : RunFacts) : Nat :=
  (r.targetConstruction.map (·.slice.card)).foldl max 0

/-! Joe: "Every open mission, excursion or ticket is wanted." -/
def Q1 (r : RunFacts) : Bool := decide (r.enumeratedTasks = r.openTasks)

/-! Joe: cascades are derived per problem from the pattern library; the pool is
the query-time slice, and every open target has an action from the start. -/
def Q2 (r : RunFacts) : Bool := decide (
  (∀ tc ∈ r.targetConstruction,
    tc.targets ⊆ r.openTasks ∧ tc.pool = tc.slice ∧ tc.sliceFromWholeLibrary = true ∧
      tc.slice.card ≤ r.libraryPatternCount ∧ 0 < tc.policyCount) ∧
  (r.targetConstruction.map (fun tc : TargetConstruction => tc.targets)).foldl (· ∪ ·) ∅ =
    r.openTasks ∧
  r.constructorPatternCount =
    ((r.targetConstruction.map (fun tc : TargetConstruction => tc.pool)).foldl (· ∪ ·) ∅).card)

/-! Joe: "G is defined over policies, and policies are cascades ... full stop." -/
def Q3 (r : RunFacts) : Bool := decide (r.cascadesWithoutG = ∅)

/-! Joe: G must not be risk-only, and C-tau states a preference at every
step of the horizon. Zero-valued ambiguity/information terms still count when
their canonical carriers were evaluated. Grading at every step is required
only for policy families that declare progressive preference semantics. -/
def Q4 (r : RunFacts) : Bool := decide (
  r.gTerms.risk = true ∧ r.gTerms.ambiguity = true ∧
  r.gTerms.informationGain = true ∧ 0 < r.horizonLength ∧
  r.preferenceSteps = Finset.range r.horizonLength ∧
  (r.preferenceSemantics = .progressive →
    r.gradedPreferenceSteps = Finset.range r.horizonLength) ∧
  r.policiesWithRiskTerm = r.comparedPolicies.card ∧
  r.policiesWithAmbiguityTerm = r.comparedPolicies.card ∧
  r.policiesWithInformationTerm = r.comparedPolicies.card)

/-! Joe: "Go ahead and interpret a pattern, after you select it." -/
def Q5 (r : RunFacts) : Bool :=
  decide (r.interpretationOrder = .selectionBeforeInterpretation)

/-! Joe: a failure is a critical incident, never a non-event to be repeated.
An unchanged refusal may not choose the same target/cascade pair again. -/
def Q6 (r : RunFacts) : Bool := decide (
  r.previousOutcome = .refused ∧ r.previousInputDigest = r.currentInputDigest →
    r.previousChoice ≠ r.currentChoice)

/-! Joe: an absence, refusal, or "not supplied" on the one selected/enacted
certificate path is a failure; the working path contains none.  This is not a
completeness claim about rejected alternatives or population-wide scorer
diagnostics.  With no selection, the explicit abstention carrier is the path. -/
def Q7 (r : RunFacts) : Bool := decide (r.pathAbsenceCount = 0)

/-! Q8 certifies the current task frontier rather than sampling historical
population breadth.  Refresh is exact and incremental; selection is over
stable comparison keys and refuses an eligible stale contender; cascade
identity correspondence is local to the selected task.  Multiple policies
are required only when that task has multiple admissible cascades.  Q1 keeps
the independent responsibility for enumerating every open task. -/
def Q8 (r : RunFacts) : Bool := decide (
  r.frontierRefresh.Valid ∧
  r.frontierRefresh.currentOpenTasks = r.openTasks ∧
  r.frontierSelection.Valid r.frontierRefresh.current r.openTasks ∧
  r.selectedCascade.selectedTask = r.frontierSelection.selected.task ∧
  r.selectedCascade.Valid)

/-! Joe: C must prefer an outcome that closes a criterion to one that does
not. Every reachable comparison is strict, and at least one is represented. -/
def Q9 (r : RunFacts) : Bool := decide (
  0 < r.completionPreferencePairs ∧
  r.completionPairsStrictlyPreferred = r.completionPreferencePairs ∧
  0 < r.earlierProgressPairs ∧
  r.earlierProgressNoGreaterRisk = r.earlierProgressPairs)

/-! Joe: policies are cascades in a specific geometric arrangement. Whenever
the same patterns occur in two compared arrangements, both arrangements are
distinct policies with their own G, and at least one such control is present. -/
def Q10 (r : RunFacts) : Bool := decide (
  0 < r.differentArrangementPairs ∧
  r.arrangementPairsDistinguishedByG = r.differentArrangementPairs)

inductive Requirement where | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  deriving DecidableEq, Repr

def violations (r : RunFacts) : List Requirement :=
  [(.q1, Q1 r), (.q2, Q2 r), (.q3, Q3 r),
   (.q4, Q4 r), (.q5, Q5 r), (.q6, Q6 r),
   (.q7, Q7 r), (.q8, Q8 r), (.q9, Q9 r), (.q10, Q10 r)].filterMap
    (fun (q, ok) => if ok then none else some q)

def conforms (r : RunFacts) : Bool := violations r = []

private def ids (start count : Nat) : Finset Id :=
  Finset.Ico start (start + count)

/-! Click 20 provenance. The selection certificate/exporter supplies reaching
scoring, with-G, constructed/compared singleton counts, horizon/preference
rows, risk-only terms, and 62 path-scoped absences. The 221/373/43 historical
task census, two-pattern incident reconstruction, interpretation ordering,
repeat-refusal identity/digest, and 56/3 seat census come from the incident;
the record cannot recompute them and the reader therefore marks the
corresponding real-run requirements `unverifiable`. This closed witness keeps
them only to exhibit the incident described by the combined sources. -/
def click20 : RunFacts where
  openMissions := ids 0 221
  openExcursions := ids 221 373
  openTickets := ids 594 43
  enumeratedTasks := ids 0 195
  targetsReachingScoring := {0, 1, 2}
  targetsWithG := {0}
  libraryPatternCount := 1431
  targetConstruction :=
    [{ targets := {0}, slice := {10, 11}, pool := {10, 11},
       sliceFromWholeLibrary := false, policyCount := 1 }]
  constructorPatternCount := 2
  constructedCascades := {20}
  comparedPolicies := {30}
  cascadesWithoutG := ∅
  horizonLength := 4
  preferenceSteps := {3}
  gradedPreferenceSteps := ∅
  preferenceSemantics := .terminalOnly
  gTerms := ⟨true, false, false⟩
  policiesWithRiskTerm := 1
  policiesWithAmbiguityTerm := 0
  policiesWithInformationTerm := 0
  interpretationOrder := .interpretationBeforeSelection
  pathAbsenceCount := 62
  previousChoice := ⟨0, 20⟩
  previousOutcome := .refused
  previousInputDigest := 99
  currentChoice := ⟨0, 20⟩
  currentInputDigest := 99
  seatsAvailable := ids 0 56
  seatsUsed := {1, 2, 3}
  completionPreferencePairs := 1
  completionPairsStrictlyPreferred := 0
  earlierProgressPairs := 1
  earlierProgressNoGreaterRisk := 0
  differentArrangementPairs := 1
  arrangementPairsDistinguishedByG := 0
  frontierRefresh := positiveRefresh
  frontierSelection := positiveSelection
  selectedCascade := mismatchedCascade

def missingG : RunFacts :=
  { click20 with
    enumeratedTasks := click20.openTasks
    targetsReachingScoring := click20.openTasks
    targetsWithG := click20.openTasks
    cascadesWithoutG := {21} }

def good : RunFacts where
  openMissions := {1, 2, 3}
  openExcursions := ∅
  openTickets := ∅
  enumeratedTasks := {1, 2, 3}
  targetsReachingScoring := {1, 2, 3}
  targetsWithG := {1, 2, 3}
  libraryPatternCount := 1431
  targetConstruction :=
    [{ targets := {1, 2, 3}, slice := ids 3000 30,
       pool := ids 3000 30, sliceFromWholeLibrary := true,
       policyCount := 3 }]
  constructorPatternCount := 30
  constructedCascades := ids 50000 (3 * 637)
  comparedPolicies := ids 60000 (3 * 637)
  cascadesWithoutG := ∅
  horizonLength := 4
  preferenceSteps := Finset.range 4
  gradedPreferenceSteps := Finset.range 4
  preferenceSemantics := .progressive
  gTerms := ⟨true, true, true⟩
  policiesWithRiskTerm := 1911
  policiesWithAmbiguityTerm := 1911
  policiesWithInformationTerm := 1911
  interpretationOrder := .selectionBeforeInterpretation
  pathAbsenceCount := 0
  previousChoice := ⟨0, 50000⟩
  previousOutcome := .refused
  previousInputDigest := 7
  currentChoice := ⟨1, 50001⟩
  currentInputDigest := 7
  seatsAvailable := ids 0 56
  seatsUsed := ids 0 10
  completionPreferencePairs := 12
  completionPairsStrictlyPreferred := 12
  earlierProgressPairs := 20
  earlierProgressNoGreaterRisk := 20
  differentArrangementPairs := 20
  arrangementPairsDistinguishedByG := 20
  frontierRefresh := positiveRefresh
  frontierSelection := positiveSelection
  selectedCascade := positiveCascade

/-- Deterministic likelihoods and terminal-only preferences may yield numeric
zero epistemic terms while still carrying every term and total C-tau. -/
def deterministicTerminal : RunFacts :=
  { good with preferenceSemantics := .terminalOnly, gradedPreferenceSteps := ∅ }

/-- An asserted progressive schedule does not receive that exemption. -/
def progressiveRowsMissing : RunFacts :=
  { good with preferenceSemantics := .progressive, gradedPreferenceSteps := ∅ }

/-- Adversarial Q8 witnesses isolate stale-winner and identity-correspondence
failures without changing the historical breadth fields. -/
def staleFrontier : RunFacts :=
  { good with frontierSelection := staleSelection }

def cascadeMismatch : RunFacts :=
  { good with selectedCascade := mismatchedCascade }

theorem deterministic_terminal_Q4 : Q4 deterministicTerminal = true := by decide
theorem progressive_rows_missing_not_Q4 : Q4 progressiveRowsMissing = false := by decide
theorem good_Q8 : Q8 good = true := by decide
theorem stale_frontier_not_Q8 : Q8 staleFrontier = false := by decide
theorem cascade_mismatch_not_Q8 : Q8 cascadeMismatch = false := by decide

theorem click20_not_Q1 : Q1 click20 = false := by decide
theorem click20_not_Q2 : Q2 click20 = false := by decide
theorem click20_not_Q4 : Q4 click20 = false := by decide
theorem click20_not_Q5 : Q5 click20 = false := by decide
theorem click20_not_Q6 : Q6 click20 = false := by decide
theorem click20_not_Q7 : Q7 click20 = false := by decide
theorem click20_not_Q8 : Q8 click20 = false := by decide
theorem click20_not_Q9 : Q9 click20 = false := by decide
theorem click20_not_Q10 : Q10 click20 = false := by decide
theorem click20_violations :
    violations click20 = [.q1, .q2, .q4, .q5, .q6, .q7, .q8, .q9, .q10] := by decide
theorem click20_not_conformant : conforms click20 = false := by decide
theorem missingG_not_Q3 : Q3 missingG = false := by decide
theorem good_conforms : conforms good = true := by decide
theorem good_has_no_violations : violations good = [] := by decide

/--
error: Tactic `decide` proved that the proposition
  Q1 click20 = true
is false
-/
#guard_msgs in
example : Q1 click20 = true := by decide
/--
error: Tactic `decide` proved that the proposition
  Q2 click20 = true
is false
-/
#guard_msgs in
example : Q2 click20 = true := by decide
/--
error: Tactic `decide` proved that the proposition
  Q3 missingG = true
is false
-/
#guard_msgs in
example : Q3 missingG = true := by decide
/--
error: Tactic `decide` proved that the proposition
  Q4 click20 = true
is false
-/
#guard_msgs in
example : Q4 click20 = true := by decide
/--
error: Tactic `decide` proved that the proposition
  Q5 click20 = true
is false
-/
#guard_msgs in
example : Q5 click20 = true := by decide
/--
error: Tactic `decide` proved that the proposition
  Q6 click20 = true
is false
-/
#guard_msgs in
example : Q6 click20 = true := by decide
/--
error: Tactic `decide` proved that the proposition
  Q7 click20 = true
is false
-/
#guard_msgs in
example : Q7 click20 = true := by decide
/--
error: Tactic `decide` proved that the proposition
  Q8 click20 = true
is false
-/
#guard_msgs in
example : Q8 click20 = true := by decide
/--
error: Tactic `decide` proved that the proposition
  Q9 click20 = true
is false
-/
#guard_msgs in
example : Q9 click20 = true := by decide
/--
error: Tactic `decide` proved that the proposition
  Q10 click20 = true
is false
-/
#guard_msgs in
example : Q10 click20 = true := by decide

#print axioms click20_not_Q1
#print axioms click20_not_Q2
#print axioms click20_not_Q4
#print axioms click20_not_Q5
#print axioms click20_not_Q6
#print axioms click20_not_Q7
#print axioms click20_not_Q8
#print axioms click20_not_Q9
#print axioms click20_not_Q10
#print axioms click20_violations
#print axioms click20_not_conformant
#print axioms missingG_not_Q3
#print axioms good_conforms
#print axioms deterministic_terminal_Q4
#print axioms progressive_rows_missing_not_Q4
#print axioms good_Q8
#print axioms stale_frontier_not_Q8
#print axioms cascade_mismatch_not_Q8

end DarkTower.WarMachine.Requirements
