import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs
import Mathlib.Tactic
import DarkTower.WarMachine.IncrementalTaskFrontier
import DarkTower.WarMachine.FactorizedPreferenceSemantics

/-!
# Countable requirements for one War Machine run

Every field below denotes a finite population in the world or in one run
record.  This file states requirements over those facts; it does not claim
that today's runner exports them faithfully.
-/

namespace DarkTower.WarMachine.Requirements

open DarkTower.WarMachine.IncrementalTaskFrontier
open DarkTower.WarMachine.FactorizedPreferenceSemantics

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

/-- Declared normalization of a compared policy's G terms.  Under
`perStepCapacityAndPattern` risk is divided by `H · log |outcomes|`,
ambiguity by `H`, and information gain by the policy's distinct-pattern
count: G is a controller objective over per-step rates, not raw cumulative
EFE, so policies with different horizons are comparable.  `rawCumulative` is
the unnormalized horizon sum, comparable only at equal horizons.  There is no
`undeclared` constructor: an absent, unrecognized or unbound declaration is
not recomputable. -/
inductive GNormalization where
  | perStepCapacityAndPattern | rawCumulative
  deriving DecidableEq, Repr

/-- One compared policy's horizon and preference facts, over its own horizon. -/
structure PolicyPreference where
  /-- Stable id of the compared policy. -/
  policy : Id
  /-- Number of future steps scored for this policy, from its observation model. -/
  horizon : Nat
  /-- Zero-based steps whose C-tau row states a real preference. -/
  preferenceSteps : Finset Nat
  /-- Steps whose C-tau is graded by completed-progress count. -/
  gradedPreferenceSteps : Finset Nat
  /-- The policy's declared preference semantics. -/
  semantics : PreferenceSemantics
  /-- The normalization under which this policy's G was compared. -/
  normalization : GNormalization
  /-- Terms recorded and evaluated for this policy's G. -/
  terms : GTerms
  deriving DecidableEq

/-- Every term evaluated, a positive horizon, a preference at every step, and
grading at every step under progressive semantics. -/
def PolicyPreference.Valid (p : PolicyPreference) : Prop :=
  p.terms = ⟨true, true, true⟩ ∧ 0 < p.horizon ∧
  p.preferenceSteps = Finset.range p.horizon ∧
  (p.semantics = .progressive → p.gradedPreferenceSteps = Finset.range p.horizon)

instance (p : PolicyPreference) : Decidable p.Valid := by
  unfold PolicyPreference.Valid
  infer_instance

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
  /-- One record per compared policy, each over its own horizon. -/
  policyPreferences : List PolicyPreference
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
  /-- Authorized factorization of completion from conditional relevance.
  `none` means flat class weights cannot establish Q9. -/
  factorizedPreference : Option DarkTower.WarMachine.FactorizedPreferenceSemantics.Certificate
  /-- Exact retained registry authorizing the certificate's calibration. -/
  calibrationAuthorizations :
    List DarkTower.WarMachine.FactorizedPreferenceSemantics.CalibrationAuthorization
  /-- Exact retained registry authorizing the certificate's factorization law. -/
  factorizationAuthorizations :
    List DarkTower.WarMachine.FactorizedPreferenceSemantics.FactorizationAuthorization
  /-- Number of compared cascade pairs with the same pattern set and different arrangements. -/
  differentArrangementPairs : Nat
  /-- Number of those pairs represented as distinct policies, each with its own numeric G. -/
  arrangementPairsDistinguishedByG : Nat
  /-- Every open task, each either eligible for ranking or excluded with its
  recorded typed reason. -/
  frontierCensus : EligibilityCensus
  /-- Exact refresh certificate for the eligible frontier (an audit of a full
  recomputation against the persisted prior frontier). -/
  frontierRefresh : RefreshCertificate
  /-- Winner certificate over the refreshed eligible frontier and current tie law. -/
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
only for policy families that declare progressive preference semantics.

Ruling (codex-68, 2026-10-16): each compared policy has its own horizon.
Policies with different horizons are comparable only because their G terms
share the per-step capacity-and-pattern normalization, so every compared
policy records one common law, and a law other than that one requires equal
horizons. The policy records are exactly the compared policies, one each:
every record is of a compared policy, every compared policy has a record,
and there are as many records as compared policies. -/
def Q4 (r : RunFacts) : Bool := decide (
  r.gTerms.risk = true ∧ r.gTerms.ambiguity = true ∧
  r.gTerms.informationGain = true ∧
  r.comparedPolicies.Nonempty ∧
  (∀ p ∈ r.policyPreferences, p.policy ∈ r.comparedPolicies) ∧
  (∀ c ∈ r.comparedPolicies, ∃ p ∈ r.policyPreferences, p.policy = c) ∧
  r.policyPreferences.length = r.comparedPolicies.card ∧
  (∀ p ∈ r.policyPreferences, p.Valid) ∧
  (∀ p ∈ r.policyPreferences, ∀ q ∈ r.policyPreferences,
    p.normalization = q.normalization ∧
    (p.normalization = .perStepCapacityAndPattern ∨ p.horizon = q.horizon)) ∧
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
stable comparison keys only after every affected/additional entry has been
recomputed; cascade
identity correspondence is local to the selected task.  Multiple policies
are required only when that task has multiple admissible cascades.  Q1 keeps
the independent responsibility for enumerating every open task. -/
def q6Excludable (r : RunFacts) : Finset Id :=
  if r.previousOutcome = .refused ∧ r.previousInputDigest = r.currentInputDigest
  then {r.previousChoice.cascade} else ∅

/-! Ruling 2b (codex-68, 2026-10-15): selection ranges over the certified
eligible frontier; the complete open-task census is kept beside it, each
excluded task with its typed reason and no comparison key.  Ruling 1a: a
policy removed before the one comparison is justified only by Q6 (the
previous run refused it on the same selection inputs). -/
def Q8 (r : RunFacts) : Bool := decide (
  r.frontierCensus.Valid r.openTasks ∧
  r.frontierRefresh.Valid ∧
  r.frontierRefresh.currentOpenTasks = r.frontierCensus.eligible ∧
  r.frontierSelection.Valid r.frontierRefresh.current r.frontierCensus.eligible ∧
  r.selectedCascade.selectedTask = r.frontierSelection.selected.task ∧
  r.selectedCascade.Valid ∧
  r.selectedCascade.requirementExcluded ⊆ q6Excludable r)

private instance calibrationAuthorizedDecidable
    (registry : List FactorizedPreferenceSemantics.CalibrationAuthorization)
    (receipt : FactorizedPreferenceSemantics.Id)
    (calibration : FactorizedPreferenceSemantics.RelevanceCalibration) :
    Decidable (FactorizedPreferenceSemantics.CalibrationAuthorized
      registry receipt calibration) := by
  unfold FactorizedPreferenceSemantics.CalibrationAuthorized
  infer_instance

private instance factorizationAuthorizedDecidable
    (registry : List FactorizedPreferenceSemantics.FactorizationAuthorization)
    (selectorAuthority identity : FactorizedPreferenceSemantics.Id)
    (version : Nat) (authority receipt : FactorizedPreferenceSemantics.Id) :
    Decidable (FactorizedPreferenceSemantics.FactorizationAuthorized registry
      selectorAuthority identity version authority receipt) := by
  unfold FactorizedPreferenceSemantics.FactorizationAuthorized
  infer_instance

private instance factorizedCertificateValidDecidable
    (calibrationRegistry : List FactorizedPreferenceSemantics.CalibrationAuthorization)
    (factorizationRegistry : List FactorizedPreferenceSemantics.FactorizationAuthorization)
    (certificate : FactorizedPreferenceSemantics.Certificate) :
    Decidable (FactorizedPreferenceSemantics.Certificate.Valid calibrationRegistry
      factorizationRegistry certificate) := by
  unfold FactorizedPreferenceSemantics.Certificate.Valid
  infer_instance

/-! Joe: completion is structurally prior to conditional relevance.  A flat
four-way probability table is not a Q9 witness. -/
def Q9 (r : RunFacts) : Bool := decide (
  ∃ certificate, r.factorizedPreference = some certificate ∧
    DarkTower.WarMachine.FactorizedPreferenceSemantics.Certificate.Valid
      r.calibrationAuthorizations r.factorizationAuthorizations certificate)

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

def goodCalibration : DarkTower.WarMachine.FactorizedPreferenceSemantics.RelevanceCalibration :=
  ⟨101, 1, 102, 103, 0, 1, 2⟩

def goodCalibrationAuthorization :
    DarkTower.WarMachine.FactorizedPreferenceSemantics.CalibrationAuthorization :=
  ⟨104, goodCalibration, 102⟩

def goodFactorizationAuthorization :
    DarkTower.WarMachine.FactorizedPreferenceSemantics.FactorizationAuthorization :=
  ⟨105, 106, 1, 107, .completionThenConditionalRelevance⟩

def goodPreferenceCertificate :
    DarkTower.WarMachine.FactorizedPreferenceSemantics.Certificate :=
  ⟨goodCalibration, 108, 106, 1, 107, 104, 105⟩

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
  policyPreferences :=
    [{ policy := 30, horizon := 4, preferenceSteps := {3}, gradedPreferenceSteps := ∅,
       semantics := .terminalOnly, normalization := .rawCumulative,
       terms := ⟨true, false, false⟩ }]
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
  factorizedPreference := none
  calibrationAuthorizations := []
  factorizationAuthorizations := []
  differentArrangementPairs := 1
  arrangementPairsDistinguishedByG := 0
  frontierCensus := ⟨{1, 2, 3}, []⟩
  frontierRefresh := positiveRefresh
  frontierSelection := positiveSelection
  selectedCascade := mismatchedCascade

def missingG : RunFacts :=
  { click20 with
    enumeratedTasks := click20.openTasks
    targetsReachingScoring := click20.openTasks
    targetsWithG := click20.openTasks
    cascadesWithoutG := {21} }

/-- A compared policy with every term, preference and grading over its own
horizon, under the per-step normalization. -/
def goodPolicy (policy horizon : Nat)
    (normalization : GNormalization := .perStepCapacityAndPattern)
    (terms : GTerms := ⟨true, true, true⟩) : PolicyPreference where
  policy := policy
  horizon := horizon
  preferenceSteps := Finset.range horizon
  gradedPreferenceSteps := Finset.range horizon
  semantics := .progressive
  normalization := normalization
  terms := terms

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
  comparedPolicies := {60000, 60001}
  cascadesWithoutG := ∅
  policyPreferences := [goodPolicy 60000 4, goodPolicy 60001 2]
  gTerms := ⟨true, true, true⟩
  policiesWithRiskTerm := 2
  policiesWithAmbiguityTerm := 2
  policiesWithInformationTerm := 2
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
  factorizedPreference := some goodPreferenceCertificate
  calibrationAuthorizations := [goodCalibrationAuthorization]
  factorizationAuthorizations := [goodFactorizationAuthorization]
  differentArrangementPairs := 20
  arrangementPairsDistinguishedByG := 20
  frontierCensus := ⟨{1, 2, 3}, []⟩
  frontierRefresh := positiveRefresh
  frontierSelection := positiveSelection
  selectedCascade := positiveCascade

/-- Deterministic likelihoods and terminal-only preferences may yield numeric
zero epistemic terms while still carrying every term and total C-tau. -/
def deterministicTerminal : RunFacts :=
  { good with policyPreferences := good.policyPreferences.map (fun p => { p with semantics := .terminalOnly, gradedPreferenceSteps := ∅ }) }

/-- An asserted progressive schedule does not receive that exemption. -/
def progressiveRowsMissing : RunFacts :=
  { good with policyPreferences := good.policyPreferences.map (fun p => { p with gradedPreferenceSteps := ∅ }) }

/-- `good` compares horizons 4 and 2 under the per-step normalization.  The
same horizons as raw cumulative sums are not comparable. -/
def mixedHorizonsRaw : RunFacts :=
  { good with policyPreferences := good.policyPreferences.map (fun p => { p with normalization := .rawCumulative }) }

/-- Equal horizons as raw cumulative sums are comparable. -/
def equalHorizonsRaw : RunFacts :=
  { good with policyPreferences :=
      [goodPolicy 60000 4 .rawCumulative,
       goodPolicy 60001 4 .rawCumulative] }

/-- Two compared policies under different laws share no comparison scale. -/
def mixedNormalization : RunFacts :=
  { good with policyPreferences :=
      [goodPolicy 60000 4, goodPolicy 60001 4 .rawCumulative] }

/-- A compared policy without its record, and a record for a policy that was
not compared. -/
def omittedPolicyRecord : RunFacts :=
  { good with policyPreferences := [goodPolicy 60000 4] }

def foreignPolicyRecord : RunFacts :=
  { good with policyPreferences := [goodPolicy 60000 4, goodPolicy 60002 2] }

def duplicatePolicyRecord : RunFacts :=
  { good with policyPreferences := [goodPolicy 60000 4, goodPolicy 60001 2, goodPolicy 60001 3] }

/-- Information gain evaluated for one compared policy only. -/
def policyTermMissing : RunFacts :=
  { good with policyPreferences :=
      [goodPolicy 60000 4, goodPolicy 60001 2 .perStepCapacityAndPattern ⟨true, true, false⟩] }

/-- Q4 certifies an actual comparison, not a vacuous empty menu. -/
def noComparedPolicies : RunFacts :=
  { good with
      comparedPolicies := ∅
      policyPreferences := []
      policiesWithRiskTerm := 0
      policiesWithAmbiguityTerm := 0
      policiesWithInformationTerm := 0 }

/-- Adversarial Q8 witnesses isolate incomplete refresh and identity-correspondence
failures without changing the historical breadth fields. -/
def omittedAffectedFrontier : RunFacts :=
  { good with frontierRefresh := omittedRefresh }

def cascadeMismatch : RunFacts :=
  { good with selectedCascade := mismatchedCascade }

def insufficientPosteriorMultiplicity : RunFacts :=
  { good with selectedCascade := twoAdmissibleOnePosterior }

/-- Census witnesses (ruling 2b).  Task 4 is open and excluded with a reason;
it carries no comparison key and is outside the ranked frontier. -/
def excludedWithReason : RunFacts :=
  { good with openTickets := {4}, frontierCensus := ⟨{1, 2, 3}, [⟨4, 77⟩]⟩ }

def omittedOpenTask : RunFacts :=
  { good with openTickets := {4} }

def inventedEligibleTask : RunFacts :=
  { good with frontierCensus := ⟨{1, 2, 3, 4}, []⟩ }

def unreasonedExclusion : RunFacts :=
  { good with openTickets := {4}, frontierCensus := ⟨{1, 2, 3}, [⟨4, 0⟩]⟩ }

/-- Exclusion witnesses (ruling 1a).  `good`'s previous run chose cascade
50000, was refused, and had the same input digest. -/
def q6ExcludedCascade : TargetCascadeCertificate :=
  ⟨1, {40, 50000}, {40, 50000}, {40, 50000}, {40, 50000}, {50000}, {40}⟩

def q6Excluded : RunFacts :=
  { good with selectedCascade := q6ExcludedCascade }

def exclusionWithoutQ6 : RunFacts :=
  { good with selectedCascade := q6ExcludedCascade, currentInputDigest := 8 }

def exclusionOfAnotherPolicy : RunFacts :=
  { good with selectedCascade :=
      ⟨1, {40, 50000}, {40, 50000}, {40, 50000}, {40, 50000}, {40}, {50000}⟩ }

/-- Every unrelated Q9 carrier is populated, but the certificate substitutes
the factorization identity without a matching retained authorization. -/
def substitutedFactorization : RunFacts :=
  { good with
    factorizedPreference := some
      { goodPreferenceCertificate with factorizationIdentity := 109 } }

theorem deterministic_terminal_Q4 : Q4 deterministicTerminal = true := by decide
theorem progressive_rows_missing_not_Q4 : Q4 progressiveRowsMissing = false := by decide
theorem good_Q4_mixed_horizons : Q4 good = true := by decide
theorem mixed_horizons_raw_not_Q4 : Q4 mixedHorizonsRaw = false := by decide
theorem equal_horizons_raw_Q4 : Q4 equalHorizonsRaw = true := by decide
theorem mixed_normalization_not_Q4 : Q4 mixedNormalization = false := by decide
theorem omitted_policy_record_not_Q4 : Q4 omittedPolicyRecord = false := by decide
theorem foreign_policy_record_not_Q4 : Q4 foreignPolicyRecord = false := by decide
theorem duplicate_policy_record_not_Q4 : Q4 duplicatePolicyRecord = false := by decide
theorem policy_term_missing_not_Q4 : Q4 policyTermMissing = false := by decide
theorem no_compared_policies_not_Q4 : Q4 noComparedPolicies = false := by decide
theorem good_Q8 : Q8 good = true := by decide
theorem omitted_affected_frontier_not_Q8 : Q8 omittedAffectedFrontier = false := by decide
theorem cascade_mismatch_not_Q8 : Q8 cascadeMismatch = false := by decide
theorem insufficient_posterior_multiplicity_not_Q8 :
    Q8 insufficientPosteriorMultiplicity = false := by decide
theorem excluded_with_reason_Q8 : Q8 excludedWithReason = true := by decide
theorem omitted_open_task_not_Q8 : Q8 omittedOpenTask = false := by decide
theorem invented_eligible_task_not_Q8 : Q8 inventedEligibleTask = false := by decide
theorem unreasoned_exclusion_not_Q8 : Q8 unreasonedExclusion = false := by decide
theorem q6_excluded_Q8 : Q8 q6Excluded = true := by decide
theorem exclusion_without_q6_not_Q8 : Q8 exclusionWithoutQ6 = false := by decide
theorem exclusion_of_another_policy_not_Q8 : Q8 exclusionOfAnotherPolicy = false := by decide
theorem good_Q9 : Q9 good = true := by decide
theorem substituted_factorization_not_Q9 : Q9 substitutedFactorization = false := by decide

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
#print axioms good_Q4_mixed_horizons
#print axioms mixed_horizons_raw_not_Q4
#print axioms equal_horizons_raw_Q4
#print axioms mixed_normalization_not_Q4
#print axioms omitted_policy_record_not_Q4
#print axioms foreign_policy_record_not_Q4
#print axioms duplicate_policy_record_not_Q4
#print axioms policy_term_missing_not_Q4
#print axioms no_compared_policies_not_Q4
#print axioms good_Q8
#print axioms omitted_affected_frontier_not_Q8
#print axioms cascade_mismatch_not_Q8
#print axioms insufficient_posterior_multiplicity_not_Q8
#print axioms excluded_with_reason_Q8
#print axioms omitted_open_task_not_Q8
#print axioms invented_eligible_task_not_Q8
#print axioms unreasoned_exclusion_not_Q8
#print axioms q6_excluded_Q8
#print axioms exclusion_without_q6_not_Q8
#print axioms exclusion_of_another_policy_not_Q8

end DarkTower.WarMachine.Requirements
