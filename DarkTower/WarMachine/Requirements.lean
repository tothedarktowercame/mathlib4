import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs
import Mathlib.Tactic
import DarkTower.WarMachine.FactorizedPreferenceSemantics

/-!
# Countable requirements for one War Machine run

Every field below denotes a finite population in the world or in one run
record.  This file states requirements over those facts; it does not claim
that today's runner exports them faithfully.
-/

namespace DarkTower.WarMachine.Requirements

open DarkTower.WarMachine.FactorizedPreferenceSemantics

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev Id := Nat

/-- The inner construction census of one task, made after the outer choice.
A pin or digest of `0` is a recorded absence. -/
structure TargetConstruction where
  /-- Stable ids of the tasks this construction serves. -/
  targets : Finset Id
  /-- Stable identity of the outer action the construction serves. -/
  action : Id
  /-- Digest of the current reading (excerpt and analysis) the family was built from. -/
  reading : Id
  /-- Pin of the whole pattern-library manifest the slice was checked against. -/
  library : Id
  /-- Pin of the pattern graph the constructor read. -/
  graph : Id
  /-- Digest of the retraction and transition-kernel parameters. -/
  kernel : Id
  /-- Pattern ids returned by query-time retrieval from the pinned library. -/
  slice : Finset Id
  /-- Pattern ids the constructed policies actually arrange. -/
  pool : Finset Id
  /-- True exactly when every slice pattern is in the pinned whole-library
  manifest with the bytes the reading cited. -/
  sliceFromWholeLibrary : Bool
  /-- Number of extensionally distinct valid policies constructed. -/
  policyCount : Nat
  /-- Stable identities of those policies (arranged structural keys). -/
  policies : Finset Id
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
  /-- Inner construction census: slice, pool, pins and policies, per
  constructed task. -/
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
  deriving DecidableEq

def RunFacts.openTasks (r : RunFacts) : Finset Id :=
  r.openMissions ∪ r.openExcursions ∪ r.openTickets

def RunFacts.totalPolicies (r : RunFacts) : Nat :=
  (r.targetConstruction.map (fun tc => tc.targets.card * tc.policyCount)).sum

def RunFacts.maxSliceSize (r : RunFacts) : Nat :=
  (r.targetConstruction.map (·.slice.card)).foldl max 0

/-! Joe: "Every open mission, excursion or ticket is wanted." -/
def Q1 (r : RunFacts) : Bool := decide (r.enumeratedTasks = r.openTasks)

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

inductive Requirement where | q1 | q3 | q4 | q5 | q6 | q7 | q9
  deriving DecidableEq, Repr

def violations (r : RunFacts) : List Requirement :=
  [(.q1, Q1 r), (.q3, Q3 r),
   (.q4, Q4 r), (.q5, Q5 r), (.q6, Q6 r),
   (.q7, Q7 r), (.q9, Q9 r)].filterMap
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
    [{ targets := {0}, action := 0, reading := 0, library := 0, graph := 0, kernel := 0,
       slice := {10, 11}, pool := {10, 11},
       sliceFromWholeLibrary := false, policyCount := 1, policies := {20} }]
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

/-- Task 1's inner construction and its two compared policies. -/
def goodConstruction : TargetConstruction where
  targets := {1}
  action := 71
  reading := 81
  library := 82
  graph := 83
  kernel := 84
  slice := ids 3000 30
  pool := ids 3000 30
  sliceFromWholeLibrary := true
  policyCount := 2
  policies := {60000, 60001}

def good : RunFacts where
  openMissions := {1, 2, 3}
  openExcursions := ∅
  openTickets := ∅
  enumeratedTasks := {1, 2, 3}
  targetsReachingScoring := {1, 2, 3}
  targetsWithG := {1, 2, 3}
  libraryPatternCount := 1431
  targetConstruction := [goodConstruction]
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

/-- Every unrelated Q9 carrier is populated, but the certificate substitutes
the factorization identity without a matching retained authorization. -/
def substitutedFactorization : RunFacts :=
  { good with
    factorizedPreference := some
      { goodPreferenceCertificate with factorizationIdentity := 109 } }

theorem deterministic_terminal_Q4 : Q4 deterministicTerminal = true := by native_decide
theorem progressive_rows_missing_not_Q4 : Q4 progressiveRowsMissing = false := by native_decide
theorem good_Q4_mixed_horizons : Q4 good = true := by native_decide
theorem mixed_horizons_raw_not_Q4 : Q4 mixedHorizonsRaw = false := by native_decide
theorem equal_horizons_raw_Q4 : Q4 equalHorizonsRaw = true := by native_decide
theorem mixed_normalization_not_Q4 : Q4 mixedNormalization = false := by native_decide
theorem omitted_policy_record_not_Q4 : Q4 omittedPolicyRecord = false := by native_decide
theorem foreign_policy_record_not_Q4 : Q4 foreignPolicyRecord = false := by native_decide
theorem duplicate_policy_record_not_Q4 : Q4 duplicatePolicyRecord = false := by native_decide
theorem policy_term_missing_not_Q4 : Q4 policyTermMissing = false := by native_decide
theorem no_compared_policies_not_Q4 : Q4 noComparedPolicies = false := by native_decide
theorem good_Q9 : Q9 good = true := by native_decide
theorem substituted_factorization_not_Q9 : Q9 substitutedFactorization = false := by native_decide

theorem click20_not_Q1 : Q1 click20 = false := by native_decide
theorem click20_not_Q4 : Q4 click20 = false := by native_decide
theorem click20_not_Q5 : Q5 click20 = false := by native_decide
theorem click20_not_Q6 : Q6 click20 = false := by native_decide
theorem click20_not_Q7 : Q7 click20 = false := by native_decide
theorem click20_not_Q9 : Q9 click20 = false := by native_decide
theorem click20_violations :
    violations click20 = [.q1, .q4, .q5, .q6, .q7, .q9] := by native_decide
theorem click20_not_conformant : conforms click20 = false := by native_decide
theorem missingG_not_Q3 : Q3 missingG = false := by native_decide
theorem good_conforms : conforms good = true := by native_decide
theorem good_has_no_violations : violations good = [] := by native_decide

/--
error: Tactic `decide` proved that the proposition
  Q1 click20 = true
is false
-/
#guard_msgs in
example : Q1 click20 = true := by decide
/--
error: Tactic `decide` proved that the proposition
  Q3 missingG = true
is false
-/
#guard_msgs in
example : Q3 missingG = true := by decide
/--
error: Tactic `native_decide` evaluated that the proposition
  Q4 click20 = true
is false
-/
#guard_msgs in
example : Q4 click20 = true := by native_decide
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
  Q9 click20 = true
is false
-/
#guard_msgs in
example : Q9 click20 = true := by decide

#print axioms click20_not_Q1
#print axioms click20_not_Q4
#print axioms click20_not_Q5
#print axioms click20_not_Q6
#print axioms click20_not_Q7
#print axioms click20_not_Q9
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

end DarkTower.WarMachine.Requirements
