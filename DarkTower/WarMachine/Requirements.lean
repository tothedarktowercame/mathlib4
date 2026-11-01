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

/-- Which of a click's two runs a `RunFacts` describes.  One loop, one set of
requirements: a `selection` run's policies are task-selection cascades and its
field is the open tasks; a `work` run's policies are tactical cascades for the
task the selection run chose.  The kind fixes what the construction serves and
how many policies a comparison needs (`Q2`); it exempts a run from nothing else. -/
inductive RunKind where
  | selection | work
  deriving DecidableEq, Repr

/-- The construction census of one run: the slice, pool, pins and policies the
run compared.  A selection run has one, for its whole field; a work run has one,
for the task selected.  A pin or digest of `0` is a recorded absence. -/
structure TargetConstruction where
  /-- Stable ids of the tasks this construction serves. -/
  targets : Finset Id
  /-- Stable identity of the action the construction serves. -/
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

/-- What a run decided.  Joe, 2026-11-01: abstention applies "when there is nothing
left to do (outer) or when no action is available that progresses the work
(inner). Both are appropriate stops."  A run picking nothing in any other
circumstance fails `Q11`. -/
inductive Decision where
  /-- A task and an arranged cascade over it. -/
  | pick (target cascade : Id)
  /-- Work run: cascades over `target` were compared and none progresses it. -/
  | abstainOnTask (target : Id)
  /-- Selection run: no open task exists. -/
  | abstainEmptyField
  deriving DecidableEq, Repr

inductive RunOutcome where
  | changed | alreadySatisfied | question | refused | invalid | timedOut | abstained
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

/-- Where a value on the selection path came from.  `observed` carries the digest
of the receipt that measured it this run; a digest of `0` is an absence. -/
inductive Provenance where
  | observed (digest : Id)
  /-- Supplied by a parameter file, e.g. outer-makeup `:default-reach`. -/
  | defaulted
  /-- Not supplied, status absent, or unknown. -/
  | absent
  deriving DecidableEq, Repr

def Provenance.isObserved : Provenance → Bool
  | .observed d => d ≠ 0
  | _ => false

/-- The selection run's path from field to chosen task. -/
structure SelectionPath where
  /-- The retained `:outer/selection` section, by digest.  The separate
  `:outer-task-selection` key is the deleted selector's stub and is not this. -/
  receipt : Provenance
  /-- Relation of the chosen target to the retained focus: a classify-target
  receipt whose class is measured (not `:unknown`). -/
  pickRelation : Provenance
  /-- Reach of the chosen target over the field, computed this run from pinned
  retained records (Giraffe cones and unblocks, graph coverage, prior clicks). -/
  pickReach : Provenance
  /-- The previous run found awaiting classification at the start of this run,
  with its ending-class receipt; `none` on a first click. -/
  pendingRun : Option (Id × Provenance)
  /-- Runs consumed for learning, each with its classification receipt. -/
  consumedRuns : List (Id × Provenance)
  /-- `:outer/learning {:status :applied}`. -/
  learningApplied : Bool
  deriving DecidableEq, Repr

structure RunFacts where
  /-- Which of the click's two runs these facts describe. -/
  kind : RunKind
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
  /-- Construction census: slice, pool, pins and policies. -/
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
  /-- One G per compared policy.  Exact rationals, projected from the record. -/
  policyG : List (Id × ℚ)
  /-- G of choosing nothing: the stopped kernel, scored like any policy. -/
  abstentionG : ℚ
  /-- One digest of predicted outcome distribution per compared policy.  A
  digest of `0` is a recorded absence. -/
  policyPrediction : List (Id × Id)
  /-- Digest of the stopped distribution.  `0` is a recorded absence. -/
  abstentionPrediction : Id
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
  /-- The typed selection path: present exactly on a selection run. -/
  selectionPath : Option SelectionPath
  /-- Previous run's decision. -/
  previousDecision : Decision
  /-- Previous run's typed terminal outcome. -/
  previousOutcome : RunOutcome
  /-- Digest of all inputs on which the previous choice depended. -/
  previousInputDigest : Id
  /-- Current run's decision. -/
  currentDecision : Decision
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

/-- The tasks a run's construction must serve: the whole enumerated field for a
selection run, the selected task for a work run. -/
def RunFacts.constructionTargets (r : RunFacts) : Finset Id :=
  match r.kind, r.currentDecision with
  | .selection, _ => r.enumeratedTasks
  | .work, .pick target _ => {target}
  | .work, .abstainOnTask target => {target}
  | .work, .abstainEmptyField => ∅

/-- The fewest compared policies that make a run's comparison a comparison.  A
selection between one cascade and nothing else chooses nothing.  A work run may
have one admissible cascade for its task. -/
def RunFacts.comparisonFloor (r : RunFacts) : Nat :=
  match r.kind with
  | .selection => 2
  | .work => 1

/-- A selection run over an empty field: nothing to construct cascades over, so
nothing is constructed or compared. -/
def RunFacts.emptyField (r : RunFacts) : Bool :=
  decide (r.kind = .selection ∧ r.enumeratedTasks = ∅)

/-! Joe: "Every open mission, excursion or ticket is wanted." -/
def Q1 (r : RunFacts) : Bool := decide (r.enumeratedTasks = r.openTasks)

/-! Joe: cascades are derived per problem from the pattern library; the pool is
the query-time slice.  Joe, 2026-11-01: task selection is the same loop and meets
the same requirements.

A run has exactly one construction, with a recorded reading, library, graph and
kernel, the pool equal to a non-empty slice drawn from the whole pinned library,
a positive count of distinct policies, and every compared policy among them.  A
selection run's construction serves the whole field and compares at least two
cascades; a work run's serves the selected task.  A menu listed by hand has no
library pin and no slice, so it fails here however its G values come out.

A selection run over an empty field has no construction, and a construction
there is a fixture, not a run. -/
def Q2 (r : RunFacts) : Bool :=
  if r.emptyField then
    decide (r.targetConstruction = [] ∧ r.comparedPolicies = ∅ ∧ r.constructedCascades = ∅)
  else decide (
  r.targetConstruction.length = 1 ∧
  (∀ tc ∈ r.targetConstruction,
    tc.targets = r.constructionTargets ∧
    tc.reading ≠ 0 ∧ tc.library ≠ 0 ∧ tc.graph ≠ 0 ∧ tc.kernel ≠ 0 ∧
    tc.pool = tc.slice ∧ tc.pool.Nonempty ∧ tc.sliceFromWholeLibrary = true ∧
    tc.slice.card ≤ r.libraryPatternCount ∧
    0 < tc.policyCount ∧ tc.policies.card = tc.policyCount ∧
    r.comparedPolicies ⊆ tc.policies ∧
    r.constructorPatternCount = tc.pool.card) ∧
  r.comparisonFloor ≤ r.comparedPolicies.card)

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
  (r.comparedPolicies.Nonempty ∨ r.emptyField = true) ∧
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
    r.previousDecision ≠ r.currentDecision)

/-! Joe: an absence, refusal, or "not supplied" on the one selected/enacted
certificate path is a failure; the working path contains none.  This is not a
completeness claim about rejected alternatives or population-wide scorer
diagnostics.  With no selection, the explicit abstention carrier is the path.

On a selection run the path is typed, not counted.  The receipt, the chosen
target's relation and its reach are each observed: a value read from a file is
`defaulted`, and no constructor tolerates that.  A run found pending and every
run consumed has a classification receipt: a deferral on
`:terminal-ending-class-absent` (15 of 27 era-2 records) is an absence on the
path, not a status.  Learning is applied exactly when something was consumed:
applied with nothing consumed is learning from nothing, and not applied with
consumptions is a refusal to learn. -/
def Q7 (r : RunFacts) : Bool := decide (
  r.pathAbsenceCount = 0 ∧
  (r.kind = .selection ↔ r.selectionPath.isSome) ∧
  (∀ p ∈ r.selectionPath,
    p.receipt.isObserved ∧ p.pickRelation.isObserved ∧ p.pickReach.isObserved ∧
    (∀ pr ∈ p.pendingRun, pr.2.isObserved) ∧
    (p.consumedRuns.map Prod.fst).Nodup ∧
    (∀ c ∈ p.consumedRuns, c.2.isObserved) ∧
    (p.learningApplied ↔ p.consumedRuns ≠ [])))

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

/-- A comparison took place and its record is whole: at least one compared
policy, one G and one present prediction digest for each, and the compared
policies exactly the constructed cascades and the construction's policies. -/
def RunFacts.comparisonRecorded (r : RunFacts) : Bool := decide (
  r.comparedPolicies.Nonempty ∧
  (r.policyG.map Prod.fst).Nodup ∧
  (r.policyG.map Prod.fst).toFinset = r.comparedPolicies ∧
  (r.policyPrediction.map Prod.fst).Nodup ∧
  (r.policyPrediction.map Prod.fst).toFinset = r.comparedPolicies ∧
  (∀ p ∈ r.policyPrediction, p.2 ≠ 0) ∧
  r.targetConstruction.map (·.policies) = [r.constructedCascades] ∧
  r.comparedPolicies = r.constructedCascades)

/-- Stopping's prediction is present and no compared policy's prediction is it. -/
def RunFacts.predictsOtherThanStopping (r : RunFacts) : Bool := decide (
  r.abstentionPrediction ≠ 0 ∧ ∀ p ∈ r.policyPrediction, p.2 ≠ r.abstentionPrediction)

/-! Joe, 2026-11-01: the outer loop should be able to say what was selected and
why, with reference to the minimising cascade; ties are a tripwire.  A G value
for every policy says nothing if the choice did not come from them, so this
states that it did, for both kinds of run.

The chosen cascade is a compared policy, and a selection run's chosen task is in
its field.  Every compared policy has exactly one G and one present prediction
digest, and nothing else has.  The chosen G is strictly below every other
compared policy's G and strictly below abstention's: a tie at the minimum means
G did not choose, whatever broke it.  Ties among the policies not chosen are
allowed.  Two or more compared policies do not all predict the same thing.  The
constructed cascades are exactly the construction's policies, and the compared
policies are exactly the constructed cascades: a cascade built and then left out
of the comparison is a restricted domain, whatever the record says about G.

Abstention is decided by the same comparison.  On a task, stopping is strictly
below every compared cascade.  On any comparison, no compared cascade predicts
what stopping predicts: a pick that predicts stopping is the click-12 façade seen
through predictions.  Only an empty field abstains with no comparison. -/
def Q11 (r : RunFacts) : Bool :=
  match r.currentDecision with
  | .pick target cascade =>
    r.comparisonRecorded && r.predictsOtherThanStopping && decide (
      cascade ∈ r.comparedPolicies ∧
      (r.kind = .selection → target ∈ r.enumeratedTasks) ∧
      (∃ chosen ∈ r.policyG, chosen.1 = cascade ∧
        chosen.2 < r.abstentionG ∧
        ∀ other ∈ r.policyG, other.1 ≠ chosen.1 → chosen.2 < other.2) ∧
      (2 ≤ r.comparedPolicies.card →
        1 < (r.policyPrediction.map Prod.snd).toFinset.card))
  | .abstainOnTask _ =>
    r.comparisonRecorded && r.predictsOtherThanStopping && decide (
      r.kind = .work ∧ ∀ g ∈ r.policyG, r.abstentionG < g.2)
  | .abstainEmptyField =>
    r.emptyField && decide (r.policyG = [] ∧ r.policyPrediction = [])

inductive Requirement where | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q9 | q11
  deriving DecidableEq, Repr

def violations (r : RunFacts) : List Requirement :=
  [(.q1, Q1 r), (.q2, Q2 r), (.q3, Q3 r),
   (.q4, Q4 r), (.q5, Q5 r), (.q6, Q6 r),
   (.q7, Q7 r), (.q9, Q9 r), (.q11, Q11 r)].filterMap
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
  kind := .work
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
  policyG := []
  abstentionG := 0
  policyPrediction := []
  abstentionPrediction := 0
  gTerms := ⟨true, false, false⟩
  policiesWithRiskTerm := 1
  policiesWithAmbiguityTerm := 0
  policiesWithInformationTerm := 0
  interpretationOrder := .interpretationBeforeSelection
  pathAbsenceCount := 62
  selectionPath := none
  previousDecision := .pick 0 20
  previousOutcome := .refused
  previousInputDigest := 99
  currentDecision := .pick 0 20
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

/-- Task 1's construction and its two compared policies. -/
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
  kind := .work
  openMissions := {1, 2, 3}
  openExcursions := ∅
  openTickets := ∅
  enumeratedTasks := {1, 2, 3}
  targetsReachingScoring := {1, 2, 3}
  targetsWithG := {1, 2, 3}
  libraryPatternCount := 1431
  targetConstruction := [goodConstruction]
  constructorPatternCount := 30
  constructedCascades := {60000, 60001}
  comparedPolicies := {60000, 60001}
  cascadesWithoutG := ∅
  policyPreferences := [goodPolicy 60000 4, goodPolicy 60001 2]
  policyG := [(60000, 2), (60001, 3/2)]
  abstentionG := 3
  policyPrediction := [(60000, 160000), (60001, 160001)]
  abstentionPrediction := 160999
  gTerms := ⟨true, true, true⟩
  policiesWithRiskTerm := 2
  policiesWithAmbiguityTerm := 2
  policiesWithInformationTerm := 2
  interpretationOrder := .selectionBeforeInterpretation
  pathAbsenceCount := 0
  selectionPath := none
  previousDecision := .pick 0 50000
  previousOutcome := .refused
  previousInputDigest := 7
  currentDecision := .pick 1 60001
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

/-- The whole three-task field's construction: a slice of 7 patterns from the
19-pattern task-selection library, arranged into 3 cascades. -/
def selectionConstruction : TargetConstruction where
  targets := {1, 2, 3}
  action := 70
  reading := 91
  library := 92
  graph := 93
  kernel := 94
  slice := ids 4000 7
  pool := ids 4000 7
  sliceFromWholeLibrary := true
  policyCount := 3
  policies := {70000, 70001, 70002}

/-- A selection run comparing `compared`, from the construction `tc`.  The
negatives below are built from it so that they keep the other requirements. -/
def goodSelectionPath : SelectionPath where
  receipt := .observed 80001
  pickRelation := .observed 80002
  pickReach := .observed 80003
  pendingRun := some (80012, .observed 80013)
  consumedRuns := [(80010, .observed 80011), (80012, .observed 80013)]
  learningApplied := true

def selectionRun (tc : TargetConstruction) (compared : List Id) : RunFacts :=
  { good with
    kind := .selection
    selectionPath := some goodSelectionPath
    libraryPatternCount := 19
    targetConstruction := [tc]
    constructorPatternCount := tc.pool.card
    constructedCascades := tc.policies
    comparedPolicies := compared.toFinset
    policyPreferences := compared.map (fun c => goodPolicy c 1)
    policyG := compared.map (fun c =>
      (c, if c = 70000 then 29949 / 10000 else 34841 / 10000))
    abstentionG := 47875 / 10000
    policyPrediction := compared.map (fun c => (c, c + 100000))
    abstentionPrediction := 179999
    policiesWithRiskTerm := compared.length
    policiesWithAmbiguityTerm := compared.length
    policiesWithInformationTerm := compared.length
    previousDecision := .pick 0 70001
    currentDecision := .pick 1 70000 }

def selectionGood : RunFacts :=
  selectionRun selectionConstruction [70000, 70001, 70002]

/-- `outer-makeup.edn`'s shape: three cascades listed in a file, over a pool of
three pattern ids that is no retrieval slice, and no library pin. -/
def handListedMenu : RunFacts :=
  selectionRun
    { selectionConstruction with
      library := 0
      slice := ids 4000 3
      pool := ids 4000 3
      sliceFromWholeLibrary := false }
    [70000, 70001, 70002]

def oneCascadeMenu : RunFacts :=
  selectionRun
    { selectionConstruction with policyCount := 1, policies := {70000} }
    [70000]

/-- A pool not drawn as the slice: it holds a pattern the slice lacks. -/
def menuNotFromSlice : RunFacts :=
  selectionRun { selectionConstruction with pool := ids 4001 7 }
    [70000, 70001, 70002]

def unpinnedGiraffe : RunFacts :=
  selectionRun { selectionConstruction with reading := 0 } [70000, 70001, 70002]

/-! One field of `selectionGood` wrong at a time, for the conjuncts the four
named witnesses do not isolate. -/

def libraryUnpinned : RunFacts :=
  selectionRun { selectionConstruction with library := 0 } [70000, 70001, 70002]

def graphUnpinned : RunFacts :=
  selectionRun { selectionConstruction with graph := 0 } [70000, 70001, 70002]

def kernelUnpinned : RunFacts :=
  selectionRun { selectionConstruction with kernel := 0 } [70000, 70001, 70002]

def sliceOutsideLibrary : RunFacts :=
  selectionRun { selectionConstruction with sliceFromWholeLibrary := false }
    [70000, 70001, 70002]

def sliceLargerThanLibrary : RunFacts :=
  selectionRun { selectionConstruction with slice := ids 4000 20, pool := ids 4000 20 }
    [70000, 70001, 70002]

/-- Three cascades over no patterns at all. -/
def emptyPoolMenu : RunFacts :=
  selectionRun { selectionConstruction with slice := ∅, pool := ∅ }
    [70000, 70001, 70002]

/-- Restricted domain: the construction serves part of the enumerated field. -/
def restrictedField : RunFacts :=
  selectionRun { selectionConstruction with targets := {1, 2} } [70000, 70001, 70002]

def policyCountOverstated : RunFacts :=
  selectionRun { selectionConstruction with policyCount := 4 } [70000, 70001, 70002]

def comparedOutsideMenu : RunFacts :=
  selectionRun selectionConstruction [70000, 70001, 70003]

def noSelectionConstruction : RunFacts :=
  { selectionGood with targetConstruction := [] }

def twoSelectionConstructions : RunFacts :=
  { selectionGood with targetConstruction := [selectionConstruction, selectionConstruction] }

def patternCountMisreported : RunFacts :=
  { selectionGood with constructorPatternCount := 19 }

/-- Relabelling a selection run as a work run does not pass it: the construction
then has to serve only the selected task. -/
def selectionLabelledWork : RunFacts :=
  { selectionGood with kind := .work }

/-- The work-kind counterparts of the two clauses that depend on the kind. -/
def workConstructionForOtherTask : RunFacts :=
  { good with targetConstruction := [{ goodConstruction with targets := {2} }] }

def workOneCascade : RunFacts :=
  { good with
    targetConstruction := [{ goodConstruction with policyCount := 1, policies := {60000} }]
    constructedCascades := {60000}
    comparedPolicies := {60000}
    policyPreferences := [goodPolicy 60000 4]
    policyG := [(60000, 2)]
    policyPrediction := [(60000, 160000)]
    policiesWithRiskTerm := 1
    policiesWithAmbiguityTerm := 1
    policiesWithInformationTerm := 1
    currentDecision := .pick 1 60000 }

/-! Q11 witnesses.  Each changes `selectionGood` or `good` in one respect. -/

/-- The 10-31 shape: every compared policy has the same G. -/
def exactTieAtMinimum : RunFacts :=
  { selectionGood with
    policyG := [(70000, 29949 / 10000), (70001, 29949 / 10000), (70002, 29949 / 10000)] }

/-- The other era-2 shape: two cascades share the minimum, the third is worse. -/
def twoWayTieAtMinimum : RunFacts :=
  { selectionGood with
    policyG := [(70000, 29949 / 10000), (70001, 29949 / 10000), (70002, 34841 / 10000)] }

/-- Menu order: the first cascade is chosen though another has the lower G. -/
def chosenNotMinimum : RunFacts :=
  { selectionGood with
    policyG := [(70000, 34841 / 10000), (70001, 29949 / 10000), (70002, 34841 / 10000)] }

def chosenOutsideMenu : RunFacts :=
  { selectionGood with currentDecision := .pick 1 70003 }

def chosenTargetOutsideField : RunFacts :=
  { selectionGood with currentDecision := .pick 9 70000 }

/-- The click-12 façade: choosing has the same G as choosing nothing. -/
def chosenEqualsAbstention : RunFacts :=
  { selectionGood with abstentionG := 29949 / 10000 }

def abstentionBelowChosen : RunFacts :=
  { selectionGood with abstentionG := 2 }

def allPredictionsEqual : RunFacts :=
  { selectionGood with
    policyPrediction := [(70000, 170000), (70001, 170000), (70002, 170000)] }

def predictionAbsent : RunFacts :=
  { selectionGood with
    policyPrediction := [(70000, 170000), (70001, 0), (70002, 170002)] }

def missingPrediction : RunFacts :=
  { selectionGood with policyPrediction := [(70000, 170000), (70001, 170001)] }

def missingPolicyG : RunFacts :=
  { selectionGood with
    policyG := [(70000, 29949 / 10000), (70001, 34841 / 10000)] }

/-- A second G for a compared policy, even an agreeing one. -/
def duplicatePolicyG : RunFacts :=
  { selectionGood with policyG := selectionGood.policyG ++ [(70002, 34841 / 10000)] }

def foreignPolicyG : RunFacts :=
  { selectionGood with policyG := selectionGood.policyG ++ [(70003, 34841 / 10000)] }

def constructedNotPolicies : RunFacts :=
  { selectionGood with constructedCascades := {70000, 70001, 70002, 70003} }

/-- Three cascades constructed, two compared, and the record asserts that
nothing lacks G.  Before 2026-11-01 this conformed (claude-2's review probe). -/
def constructedNotCompared : RunFacts :=
  { selectionGood with
    comparedPolicies := {70000, 70001}
    policyPreferences := [goodPolicy 70000 1, goodPolicy 70001 1]
    policyG := [(70000, 29949 / 10000), (70001, 34841 / 10000)]
    policyPrediction := [(70000, 170000), (70001, 170001)]
    policiesWithRiskTerm := 2
    policiesWithAmbiguityTerm := 2
    policiesWithInformationTerm := 2 }

/-- The work-kind counterparts: the same requirement binds the inner run. -/
def workTieAtMinimum : RunFacts :=
  { good with policyG := [(60000, 3/2), (60001, 3/2)] }

def workChosenEqualsAbstention : RunFacts :=
  { good with abstentionG := 3/2 }

def workAllPredictionsEqual : RunFacts :=
  { good with policyPrediction := [(60000, 160000), (60001, 160000)] }

/-! Q7 selection-path witnesses.  Each changes one thing in `goodSelectionPath`. -/

def selectionWithPath (path : SelectionPath) : RunFacts :=
  { selectionGood with selectionPath := some path }

/-- The live `:outer-task-selection` shape: `:status :absent`. -/
def receiptNotRetained : RunFacts :=
  selectionWithPath { goodSelectionPath with receipt := .absent }

/-- Click 12 and five others: `:relation :unknown`. -/
def relationUnknown : RunFacts :=
  selectionWithPath { goodSelectionPath with pickRelation := .absent }

def relationStatedInFile : RunFacts :=
  selectionWithPath { goodSelectionPath with pickRelation := .defaulted }

/-- Every record to date: `:default-reach 1/2` from `outer-makeup.edn`. -/
def reachDefaulted : RunFacts :=
  selectionWithPath { goodSelectionPath with pickReach := .defaulted }

def observedZeroDigest : RunFacts :=
  selectionWithPath { goodSelectionPath with pickReach := .observed 0 }

/-- The live shape: `:applied` beside `:classification-receipt-absent`. -/
def learningWithoutObservation : RunFacts :=
  selectionWithPath { goodSelectionPath with consumedRuns := [(80010, .absent), (80012, .absent)] }

def learningAppliedNothingConsumed : RunFacts :=
  selectionWithPath { goodSelectionPath with consumedRuns := [] }

def learningRefusedWithObservations : RunFacts :=
  selectionWithPath { goodSelectionPath with learningApplied := false }

def duplicateConsumedRun : RunFacts :=
  selectionWithPath { goodSelectionPath with consumedRuns := [(80010, .observed 80011), (80010, .observed 80011)] }

def selectionRunWithoutPath : RunFacts :=
  { selectionGood with selectionPath := none }

def workRunWithSelectionPath : RunFacts :=
  { good with selectionPath := selectionGood.selectionPath }

/-- Applied with one consumed run classified and the other not. -/
def learningPartlyClassified : RunFacts :=
  selectionWithPath { goodSelectionPath with consumedRuns := [(80010, .observed 80011), (80012, .absent)] }

/-- The first click: nothing pending, nothing to consume, nothing applied. -/
def nothingYetConsumed : RunFacts :=
  selectionWithPath { goodSelectionPath with
    pendingRun := none, consumedRuns := [], learningApplied := false }

/-- Listed as consumed without a classification, and not reported as applied. -/
def learningDeferredUnclassified : RunFacts :=
  selectionWithPath { goodSelectionPath with consumedRuns := [(80010, .absent)], learningApplied := false }

/-- The honest projection of `:outer/learning {:status :deferred, :reason
:terminal-ending-class-absent}`: the previous run was pending, nothing was
consumed, and it has no ending class. -/
def pendingRunUnclassified : RunFacts :=
  selectionWithPath { goodSelectionPath with
    pendingRun := some (80020, .absent), consumedRuns := [], learningApplied := false }

theorem selection_good_Q7 : Q7 selectionGood = true := by native_decide
theorem good_Q7 : Q7 good = true := by native_decide
theorem nothing_yet_consumed_Q7 : Q7 nothingYetConsumed = true := by native_decide
theorem learning_deferred_unclassified_not_Q7 :
    Q7 learningDeferredUnclassified = false := by native_decide
theorem pending_run_unclassified_not_Q7 : Q7 pendingRunUnclassified = false := by native_decide
theorem receipt_not_retained_not_Q7 : Q7 receiptNotRetained = false := by native_decide
theorem relation_unknown_not_Q7 : Q7 relationUnknown = false := by native_decide
theorem relation_stated_in_file_not_Q7 : Q7 relationStatedInFile = false := by native_decide
theorem reach_defaulted_not_Q7 : Q7 reachDefaulted = false := by native_decide
theorem observed_zero_digest_not_Q7 : Q7 observedZeroDigest = false := by native_decide
theorem learning_without_observation_not_Q7 :
    Q7 learningWithoutObservation = false := by native_decide
theorem learning_applied_nothing_consumed_not_Q7 :
    Q7 learningAppliedNothingConsumed = false := by native_decide
theorem learning_refused_with_observations_not_Q7 :
    Q7 learningRefusedWithObservations = false := by native_decide
theorem duplicate_consumed_run_not_Q7 : Q7 duplicateConsumedRun = false := by native_decide
theorem selection_run_without_path_not_Q7 : Q7 selectionRunWithoutPath = false := by native_decide
theorem work_run_with_selection_path_not_Q7 :
    Q7 workRunWithSelectionPath = false := by native_decide
theorem learning_partly_classified_not_Q7 :
    Q7 learningPartlyClassified = false := by native_decide

/-- Every other requirement holds on each of these runs, so `Q7` is the only
requirement that refuses them. -/
theorem selection_absence_negatives_fail_only_Q7 :
    violations receiptNotRetained = [.q7] ∧
    violations relationUnknown = [.q7] ∧
    violations relationStatedInFile = [.q7] ∧
    violations reachDefaulted = [.q7] ∧
    violations observedZeroDigest = [.q7] ∧
    violations learningWithoutObservation = [.q7] ∧
    violations learningAppliedNothingConsumed = [.q7] ∧
    violations learningRefusedWithObservations = [.q7] ∧
    violations duplicateConsumedRun = [.q7] ∧
    violations selectionRunWithoutPath = [.q7] ∧
    violations workRunWithSelectionPath = [.q7] ∧
    violations learningPartlyClassified = [.q7] ∧
    violations learningDeferredUnclassified = [.q7] ∧
    violations pendingRunUnclassified = [.q7] := by native_decide

/-! Abstention witnesses. -/

/-- Stopping wins strictly: the comparison stands, and task 1 is not progressed. -/
def workAbstains : RunFacts :=
  { good with
    currentDecision := .abstainOnTask 1
    previousOutcome := .changed
    abstentionG := 1 }

/-- Nothing is open.  `pickRelation` and `pickReach` are the receipt of the empty
census: there was no pick to relate, and that census is what measured it. -/
def selectionEmptyField : RunFacts :=
  { good with
    kind := .selection
    openMissions := ∅
    openExcursions := ∅
    openTickets := ∅
    enumeratedTasks := ∅
    targetsReachingScoring := ∅
    targetsWithG := ∅
    targetConstruction := []
    constructorPatternCount := 0
    comparedPolicies := ∅
    constructedCascades := ∅
    policyPreferences := []
    policyG := []
    policyPrediction := []
    policiesWithRiskTerm := 0
    policiesWithAmbiguityTerm := 0
    policiesWithInformationTerm := 0
    currentDecision := .abstainEmptyField
    selectionPath := some
      { receipt := .observed 80001
        pickRelation := .observed 80004
        pickReach := .observed 80004
        pendingRun := none
        consumedRuns := []
        learningApplied := false } }

/-- The machine abstains while work remains. -/
def selectionAbstainsWithWork : RunFacts :=
  { selectionGood with currentDecision := .abstainEmptyField }

/-- A construction over nothing, the fixture-in-production shape. -/
def emptyFieldWithConstruction : RunFacts :=
  { selectionEmptyField with
    targetConstruction := [selectionConstruction]
    comparedPolicies := selectionGood.comparedPolicies
    constructedCascades := selectionGood.constructedCascades
    policyPreferences := selectionGood.policyPreferences
    policiesWithRiskTerm := 3
    policiesWithAmbiguityTerm := 3
    policiesWithInformationTerm := 3 }

def workAbstainsWithoutComparison : RunFacts :=
  { workAbstains with
    comparedPolicies := ∅
    policyG := []
    policyPrediction := []
    constructedCascades := ∅
    targetConstruction := [] }

/-- Stopping ties the better cascade. -/
def workAbstainsNotMinimum : RunFacts :=
  { workAbstains with abstentionG := 3/2 }

/-- Stopping beats one cascade and not the other. -/
def workAbstainsBelowOneOnly : RunFacts :=
  { workAbstains with abstentionG := 7/4 }

/-- A cascade predicts stopping, so the comparison did not offer an alternative. -/
def workAbstainsAgainstStopping : RunFacts :=
  { workAbstains with policyPrediction := [(60000, 160000), (60001, 160999)] }

/-- The chosen policy predicts exactly what stopping predicts: click 12 seen
through predictions. -/
def pickPredictsStopping : RunFacts :=
  { good with policyPrediction := [(60000, 160000), (60001, 160999)] }

/-- A cascade not chosen predicts stopping.  `Q11` refuses this too. -/
def rejectedCascadePredictsStopping : RunFacts :=
  { good with policyPrediction := [(60000, 160999), (60001, 160001)] }

def abstentionPredictionAbsent : RunFacts :=
  { good with abstentionPrediction := 0 }

def abstainOnTaskLabelledSelection : RunFacts :=
  { workAbstains with kind := .selection }

/-- A pick from a field with nothing in it. -/
def pickFromEmptyField : RunFacts :=
  { selectionEmptyField with currentDecision := .pick 1 70000 }

/-- The empty-field decision on a work run. -/
def workClaimsEmptyField : RunFacts :=
  { good with currentDecision := .abstainEmptyField }

/-- `Q4`'s exception is the empty field, not any selection run. -/
def selectionNothingCompared : RunFacts :=
  { selectionGood with
    comparedPolicies := ∅
    policyPreferences := []
    policiesWithRiskTerm := 0
    policiesWithAmbiguityTerm := 0
    policiesWithInformationTerm := 0 }

theorem work_abstains_conforms : conforms workAbstains = true := by native_decide
theorem selection_empty_field_conforms : conforms selectionEmptyField = true := by native_decide
theorem selection_abstains_with_work_not_Q11 :
    Q11 selectionAbstainsWithWork = false := by native_decide
theorem empty_field_with_construction_not_Q2 :
    Q2 emptyFieldWithConstruction = false := by native_decide
theorem work_abstains_without_comparison_not_Q11 :
    Q11 workAbstainsWithoutComparison = false := by native_decide
theorem work_abstains_not_minimum_not_Q11 : Q11 workAbstainsNotMinimum = false := by native_decide
theorem work_abstains_below_one_only_not_Q11 :
    Q11 workAbstainsBelowOneOnly = false := by native_decide
theorem work_abstains_against_stopping_not_Q11 :
    Q11 workAbstainsAgainstStopping = false := by native_decide
theorem pick_predicts_stopping_not_Q11 : Q11 pickPredictsStopping = false := by native_decide
theorem rejected_cascade_predicts_stopping_not_Q11 :
    Q11 rejectedCascadePredictsStopping = false := by native_decide
theorem abstention_prediction_absent_not_Q11 :
    Q11 abstentionPredictionAbsent = false := by native_decide
theorem abstain_on_task_labelled_selection_not_Q11 :
    Q11 abstainOnTaskLabelledSelection = false := by native_decide
theorem pick_from_empty_field_not_Q11 : Q11 pickFromEmptyField = false := by native_decide
theorem work_claims_empty_field_not_Q11 : Q11 workClaimsEmptyField = false := by native_decide
theorem selection_nothing_compared_not_Q4 :
    Q4 selectionNothingCompared = false := by native_decide

/-- The exact requirements each abstention negative fails.  A run without a
comparison also fails `Q2` and `Q4`; a work record labelled selection also fails
`Q2` and `Q7`. -/
theorem abstention_negatives_fail_only :
    violations selectionAbstainsWithWork = [.q11] ∧
    violations emptyFieldWithConstruction = [.q2] ∧
    violations workAbstainsWithoutComparison = [.q2, .q4, .q11] ∧
    violations workAbstainsNotMinimum = [.q11] ∧
    violations workAbstainsBelowOneOnly = [.q11] ∧
    violations workAbstainsAgainstStopping = [.q11] ∧
    violations pickPredictsStopping = [.q11] ∧
    violations rejectedCascadePredictsStopping = [.q11] ∧
    violations abstentionPredictionAbsent = [.q11] ∧
    violations abstainOnTaskLabelledSelection = [.q2, .q7, .q11] := by native_decide

theorem good_Q2 : Q2 good = true := by native_decide
theorem good_Q11 : Q11 good = true := by native_decide
theorem selection_good_Q11 : Q11 selectionGood = true := by native_decide
theorem work_one_cascade_conforms : conforms workOneCascade = true := by native_decide
theorem exact_tie_at_minimum_not_Q11 : Q11 exactTieAtMinimum = false := by native_decide
theorem two_way_tie_at_minimum_not_Q11 : Q11 twoWayTieAtMinimum = false := by native_decide
theorem chosen_not_minimum_not_Q11 : Q11 chosenNotMinimum = false := by native_decide
theorem chosen_outside_menu_not_Q11 : Q11 chosenOutsideMenu = false := by native_decide
theorem chosen_target_outside_field_not_Q11 : Q11 chosenTargetOutsideField = false := by native_decide
theorem chosen_equals_abstention_not_Q11 : Q11 chosenEqualsAbstention = false := by native_decide
theorem abstention_below_chosen_not_Q11 : Q11 abstentionBelowChosen = false := by native_decide
theorem all_predictions_equal_not_Q11 : Q11 allPredictionsEqual = false := by native_decide
theorem prediction_absent_not_Q11 : Q11 predictionAbsent = false := by native_decide
theorem missing_prediction_not_Q11 : Q11 missingPrediction = false := by native_decide
theorem missing_policy_G_not_Q11 : Q11 missingPolicyG = false := by native_decide
theorem duplicate_policy_G_not_Q11 : Q11 duplicatePolicyG = false := by native_decide
theorem foreign_policy_G_not_Q11 : Q11 foreignPolicyG = false := by native_decide
theorem constructed_not_policies_not_Q11 : Q11 constructedNotPolicies = false := by native_decide
theorem constructed_not_compared_not_Q11 : Q11 constructedNotCompared = false := by native_decide
theorem work_tie_at_minimum_not_Q11 : Q11 workTieAtMinimum = false := by native_decide
theorem work_chosen_equals_abstention_not_Q11 :
    Q11 workChosenEqualsAbstention = false := by native_decide
theorem work_all_predictions_equal_not_Q11 :
    Q11 workAllPredictionsEqual = false := by native_decide

/-- Every other requirement holds on each of these runs, so `Q11` is the only
requirement that refuses them. -/
theorem strict_minimum_negatives_fail_only_Q11 :
    violations exactTieAtMinimum = [.q11] ∧
    violations twoWayTieAtMinimum = [.q11] ∧
    violations chosenNotMinimum = [.q11] ∧
    violations chosenOutsideMenu = [.q11] ∧
    violations chosenEqualsAbstention = [.q11] ∧
    violations allPredictionsEqual = [.q11] ∧
    violations missingPolicyG = [.q11] ∧
    violations constructedNotPolicies = [.q11] ∧
    violations constructedNotCompared = [.q11] ∧
    violations workTieAtMinimum = [.q11] := by native_decide

theorem selection_good_Q2 : Q2 selectionGood = true := by native_decide
theorem selection_good_conforms : conforms selectionGood = true := by native_decide
theorem hand_listed_menu_not_Q2 : Q2 handListedMenu = false := by native_decide
theorem one_cascade_menu_not_Q2 : Q2 oneCascadeMenu = false := by native_decide
theorem menu_not_from_slice_not_Q2 : Q2 menuNotFromSlice = false := by native_decide
theorem unpinned_giraffe_not_Q2 : Q2 unpinnedGiraffe = false := by native_decide
theorem library_unpinned_not_Q2 : Q2 libraryUnpinned = false := by native_decide
theorem graph_unpinned_not_Q2 : Q2 graphUnpinned = false := by native_decide
theorem kernel_unpinned_not_Q2 : Q2 kernelUnpinned = false := by native_decide
theorem slice_outside_library_not_Q2 : Q2 sliceOutsideLibrary = false := by native_decide
theorem slice_larger_than_library_not_Q2 : Q2 sliceLargerThanLibrary = false := by native_decide
theorem empty_pool_menu_not_Q2 : Q2 emptyPoolMenu = false := by native_decide
theorem restricted_field_not_Q2 : Q2 restrictedField = false := by native_decide
theorem policy_count_overstated_not_Q2 : Q2 policyCountOverstated = false := by native_decide
theorem compared_outside_menu_not_Q2 : Q2 comparedOutsideMenu = false := by native_decide
theorem no_selection_construction_not_Q2 : Q2 noSelectionConstruction = false := by native_decide
theorem two_selection_constructions_not_Q2 : Q2 twoSelectionConstructions = false := by native_decide
theorem pattern_count_misreported_not_Q2 : Q2 patternCountMisreported = false := by native_decide
theorem selection_labelled_work_not_Q2 : Q2 selectionLabelledWork = false := by native_decide
theorem work_construction_for_other_task_not_Q2 :
    Q2 workConstructionForOtherTask = false := by native_decide
theorem work_one_cascade_Q2 : Q2 workOneCascade = true := by native_decide

/-- Every other requirement holds on each of these menus, so `Q2` is the only
requirement that refuses them. -/
theorem selection_negatives_fail_only_Q2 :
    violations handListedMenu = [.q2] ∧
    violations oneCascadeMenu = [.q2] ∧
    violations menuNotFromSlice = [.q2] ∧
    violations unpinnedGiraffe = [.q2] ∧
    violations emptyPoolMenu = [.q2] ∧
    violations restrictedField = [.q2] := by native_decide

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
theorem click20_not_Q2 : Q2 click20 = false := by native_decide
theorem click20_not_Q4 : Q4 click20 = false := by native_decide
theorem click20_not_Q5 : Q5 click20 = false := by native_decide
theorem click20_not_Q6 : Q6 click20 = false := by native_decide
theorem click20_not_Q7 : Q7 click20 = false := by native_decide
theorem click20_not_Q11 : Q11 click20 = false := by native_decide
theorem click20_not_Q9 : Q9 click20 = false := by native_decide
theorem click20_violations :
    violations click20 = [.q1, .q2, .q4, .q5, .q6, .q7, .q9, .q11] := by native_decide
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
error: Tactic `native_decide` evaluated that the proposition
  Q2 click20 = true
is false
-/
#guard_msgs in
example : Q2 click20 = true := by native_decide
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
#print axioms click20_not_Q2
#print axioms click20_not_Q4
#print axioms click20_not_Q5
#print axioms click20_not_Q6
#print axioms click20_not_Q7
#print axioms click20_not_Q9
#print axioms click20_not_Q11
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
#print axioms good_Q2
#print axioms selection_good_conforms
#print axioms hand_listed_menu_not_Q2
#print axioms one_cascade_menu_not_Q2
#print axioms menu_not_from_slice_not_Q2
#print axioms unpinned_giraffe_not_Q2
#print axioms selection_negatives_fail_only_Q2
#print axioms selection_good_Q11
#print axioms exact_tie_at_minimum_not_Q11
#print axioms chosen_outside_menu_not_Q11
#print axioms chosen_equals_abstention_not_Q11
#print axioms all_predictions_equal_not_Q11
#print axioms missing_policy_G_not_Q11
#print axioms constructed_not_policies_not_Q11
#print axioms strict_minimum_negatives_fail_only_Q11
#print axioms selection_good_Q7
#print axioms work_abstains_conforms
#print axioms selection_empty_field_conforms
#print axioms abstention_negatives_fail_only
#print axioms selection_absence_negatives_fail_only_Q7

end DarkTower.WarMachine.Requirements
