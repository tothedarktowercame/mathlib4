import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import DarkTower.WarMachine.CascadeOrder
import DarkTower.Contract.Emit

/-!
# War Machine formalisation holes

This module separates vocabulary fixed by the written records from laws that
remain unproved.  `CLOSED-BY-RECORD` declarations transcribe an agreed shape or
definition; `HOLE` declarations name an implementation or proof still owed.
-/

open Set

universe u v w

namespace DarkTower.WarMachine.Holes

open DarkTower.Contract.Emit
noncomputable section

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §2.1d · holder: by-record · decided 2026-08-30 · A pattern has an antecedent and a guarded consequent. -/
structure Pattern (State Action : Type*) where
  fires : State → Prop
  «then» : State → Option Action

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e · holder: by-record · decided 2026-08-30 · A cascade records its nodes, authored organisation additions, edges, acyclicity, and precedence. -/
structure Cascade (P : Type*) where
  nodes : Set P
  addedByOrganise : Set P
  edges : P → P → Prop
  acyclic : acyclicDescent edges
  precedence : List P

/-- The three serialized lifecycle states of one endpoint-keyed have→want
arrow type. These are states of one arrow, not three arrow kinds. -/
inductive HaveWantArrowState where
  | correlated
  | open
  | constructed
  deriving DecidableEq

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:78 · P-glossary-mathematics · holder: by-record · evidence: HaveWantArrowWitness · falsifier: a composition whose left want differs from the right have elaborates · A Demonstration Foundry arrow is identified by its exact `(have, want)` endpoint pair; its lifecycle state does not change that identity. -/
structure HaveWantArrow (Endpoint : Type*) where
  source : Endpoint
  target : Endpoint
  state : HaveWantArrowState

/-- A serialized-arrow composition exists only when the first arrow's wanted
endpoint is exactly the second arrow's available endpoint. -/
structure HaveWantArrowComposition {Endpoint : Type*}
    (left right : HaveWantArrow Endpoint) : Prop where
  endpointMatch : left.target = right.source

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:68 · P-glossary-mathematics · holder: by-record · evidence: FoldWitness · falsifier: a fold without explicit policy holes elaborates · The common fold boundary is an implementation-specific typed wiring, an optional coverage-score delta (`none` means abstention), and an explicit list of policy holes. -/
structure Fold (Wiring PolicyHole : Type*) where
  wiring : Wiring
  coverageScoreDelta : Option ℝ
  policyHoles : List PolicyHole

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:68 · P-glossary-mathematics · holder: by-record · evidence: FoldEscrowRecordWitness · falsifier: a reconstructible prompt/digest pair is admitted to the non-reconstructible quarantine · The escrow envelope keeps prompt inputs, the stored digest, and the authored turn together; arming and fold output remain typed payloads rather than ambient state. -/
structure FoldEscrowRecord (PromptInputs Digest Turn Arming FoldOutput : Type*) where
  promptInputs : PromptInputs
  storedDigest : Digest
  turn : Turn
  arming : Arming
  foldOutput : FoldOutput

/-- Reconstructibility is equality between the stored digest and the digest of
the prompt reconstructed solely from the envelope's recorded inputs. -/
def FoldEscrowRecord.reconstructible
    {PromptInputs Digest Turn Arming FoldOutput Prompt : Type*}
    (record : FoldEscrowRecord PromptInputs Digest Turn Arming FoldOutput)
    (reconstruct : PromptInputs → Prompt) (digest : Prompt → Digest) : Prop :=
  digest (reconstruct record.promptInputs) = record.storedDigest

structure ControlVocabulary (Control : Type*) where
  allowable : Set Control

structure ControlPolicy {Control : Type*} (U : ControlVocabulary Control) where
  controls : List Control
  allowable : ∀ u ∈ controls, u ∈ U.allowable

structure AlivenessFactor where
  value : ℝ
  nonnegative : 0 ≤ value

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:54 · P-glossary-mathematics · holder: by-record · evidence: AlivenessWitness · falsifier: the 0.8·0.6 fixture differs from 0.48 or a negative factor elaborates. -/
def aliveness (temperature harmony : AlivenessFactor) : ℝ :=
  temperature.value * harmony.value

inductive ActGateVerdict where
  | pass | fail | abstainMissingLeg
  deriving DecidableEq, Repr

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:70 · P-glossary-mathematics · holder: by-record · evidence: ActGateWitness · falsifier: a missing leg passes or a non-improving complete gate passes. -/
def actGate (cascadeScore coverageScoreDelta : Option ℝ) : ActGateVerdict :=
  match cascadeScore, coverageScoreDelta with
  | some s, some d => if 0 < s ∧ d < 0 then .pass else .fail
  | _, _ => .abstainMissingLeg

structure Click (ClickId : Type*) where
  id : ClickId

structure Attempt (AttemptId ClickId : Type*) where
  id : AttemptId
  click : ClickId
  clickOrder : Nat

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:82 · P-glossary-mathematics · holder: by-record · evidence: CohortWitness · falsifier: a zero-target or overfull preregistered cohort elaborates. Outcome classes remain an epoch-specific parameter. -/
structure Cohort (CohortId AttemptId Epoch OutcomeClass : Type*) where
  id : CohortId
  semanticEpoch : Epoch
  stoppingTarget : Nat
  positiveTarget : 0 < stoppingTarget
  preregisteredOutcomes : Set OutcomeClass
  attempts : List AttemptId
  withinWindow : attempts.length ≤ stoppingTarget

structure Repository (P : Type*) where
  patterns : Set P
  standsOn : P → P → Prop
  acyclic : acyclicDescent standsOn

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e · holder: by-record · A tension is a context with a want and a however (review fix: D1b had only the context). -/
structure Tension (State : Type*) where
  context : State
  want : Prop
  however : Prop

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3d · holder: by-record · decided 2026-08-30 · Information state is exactly state, history, repository, and tension. -/
structure InformationState (State History Repo Tension : Type*) where
  state : State
  history : History
  repo : Repo
  tension : Tension

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3 · holder: by-record · A decision rule reads an information state and chooses an action. It is the result of inference, not the cascade-grain policy π that G scores. -/
abbrev DecisionRule (InformationState Action : Type*) := InformationState → Action

inductive Vertex where
  | people
  | money
  | organisations
  | evidence
  deriving DecidableEq, Repr

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §2a · holder: by-record · An outcome is an observation indexed by its vertex. -/
abbrev Outcome (Obs : Vertex → Type*) := Sigma Obs

/-- DELIBERATE IMPLEMENTATION REFUSAL · contract kind HOLE intentionally · owner: P-validated-R5 §2a · holder: by-record · evidence: REFUSED — this is an implementation, not a law, and the record fixes no observation that selects C · falsifier: REFUSED for the same reason · Preferences are declared per PRAGMATIC vertex only. C122's census proves this global declaration is free; it does not license choosing its value. -/
def C {Obs : Vertex → Type*} (v : Vertex) (_pragmatic : v ≠ Vertex.evidence) : Obs v → ℝ := sorry

/-- Expected free energy, shared by the risk-minus-information-gain and
risk-plus-ambiguity decompositions.  It is deliberately not definitionally
equal to either per-tick variational F or BMR model-change evidence. -/
structure ExpectedFreeEnergyValue where
  value : ℝ

instance : LE ExpectedFreeEnergyValue := ⟨fun x y => x.value ≤ y.value⟩

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §2a′ · holder: by-record · Policy grade is pragmatic risk minus epistemic gain. -/
def G {PolicyIndex : Type*} (risk eig : PolicyIndex → ℝ) : PolicyIndex → ExpectedFreeEnergyValue :=
  fun π => ⟨risk π - eig π⟩

def IsArgminOn {Policy Score : Type*} [LE Score] (policies : List Policy)
    (score : Policy → Score) (π : Policy) : Prop :=
  π ∈ policies ∧ ∀ ρ ∈ policies, score π ≤ score ρ

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §2a′ · holder: by-record · Non-degeneracy requires disagreement between the terms and a changed minimiser after ablation. -/
def nonDegenerate {Policy : Type*} (policies : List Policy)
    (pragmatic epistemic : Policy → ℝ) : Prop :=
  (∃ π₁ ∈ policies, ∃ π₂ ∈ policies,
      pragmatic π₁ < pragmatic π₂ ∧ epistemic π₁ > epistemic π₂) ∧
  ∃ πG πP,
    IsArgminOn policies (G pragmatic epistemic) πG ∧
    IsArgminOn policies pragmatic πP ∧ πG ≠ πP

structure AblationRow (Policy : Type*) where
  argminG : List Policy
  argminRisk : List Policy
  moved : Bool

abbrev AblationTable (Prior Policy : Type*) := Prior → AblationRow Policy

/-- CLOSED UNDER THE J9 CRITERION · contract kind CLOSED as of 2026-09-03 · owner: P-validated-R5 §2a′ · holder: by-record · fixture: `futon2:holes/labs/wm-contract/ablation-exact-dyadic.edn` · fixture-sha256: `f315b748420540688ef81086101b5789a4ecb2bd2a84c7a2b491f94fe8c56261` · SCOPE AMENDMENT 2026-08-31 (retained, this is what was closed): the former declaration asserted an existential for every carrier and graders, and was false for empty/singleton policies or identical graders. This predicate requires both argmins to exist and their complete minimizer sets to be disjoint; merely choosing two members of one tied minimizer set no longer counts as movement. · CLOSURE 2026-09-03, under the criterion recorded at `futon2:holes/labs/wm-contract/RUNBOOK.md` §"What ends a `closed-by-record` evidence obligation (J9 ruling, Joe, 2026-09-03)" (futon2 a2641b3), which also names this declaration's disposition. Leg (3), the Lean transcription: `wmRecordedAblationNonDegenerate` below proves this predicate over the pinned exact-dyadic table, no `sorry`. Leg (2), the rejecting witness: `futon2:checks/ablation_exact_dyadic_witness.clj` passes over the fixture and its `--negative` mode — which removes the minimizer separation — is rejected. Leg (1), the persisted record: the declared observation is a recorded score table, not a run observation, so the run leg is INAPPLICABLE here rather than met; the pinned fixture is an exact-dyadic transcription of the snatcher-dominant/g1 case of the persisted record `futon3:checks/ablation-snatch.edn`, all ten scores verified equal on decode. The earlier demotion (mathlib4 86186c3744, which added the proof and moved this row to `mkHole` in the same commit) stands in history as the pre-criterion state; it is superseded here, not amended. -/
def nonDegenerateAblationLaw {Prior Policy : Type*} (policies : List Policy)
    (grade pragmatic : Prior → Policy → ℝ) : Prop :=
    policies ≠ [] ∧ ∃ prior,
      (∃ πGrade, IsArgminOn policies (grade prior) πGrade) ∧
      (∃ πPragmatic, IsArgminOn policies (pragmatic prior) πPragmatic) ∧
      ∀ πGrade πPragmatic,
        IsArgminOn policies (grade prior) πGrade →
        IsArgminOn policies (pragmatic prior) πPragmatic →
        πGrade ≠ πPragmatic

inductive RecordedSnatchPolicy where
  | grim | patterns | exchangeFirst | probeOneToken | alwaysAbstain
  deriving DecidableEq, Repr

def recordedSnatchPolicies : List RecordedSnatchPolicy :=
  [.grim, .patterns, .exchangeFirst, .probeOneToken, .alwaysAbstain]

/-- The recorded IEEE-754 doubles, interpreted exactly as their dyadic-rational values. -/
def recordedSnatchG : RecordedSnatchPolicy → ℝ
  | .grim | .probeOneToken => 2075861046811937 / 140737488355328
  | .patterns | .exchangeFirst => 1220889258267895 / 70368744177664
  | .alwaysAbstain => 4222137547668389 / 281474976710656

def recordedSnatchRisk : RecordedSnatchPolicy → ℝ
  | .grim | .probeOneToken => 8486449631976525 / 562949953421312
  | .patterns | .exchangeFirst => 4975059755435969 / 281474976710656
  | .alwaysAbstain => 4222137547668389 / 281474976710656

/-- The exact recorded table has G minimizers `{grim, probeOneToken}` and the unique pragmatic-risk minimizer `alwaysAbstain`; the two minimizer sets are disjoint. -/
theorem wmRecordedAblationNonDegenerate :
    nonDegenerateAblationLaw recordedSnatchPolicies
      (fun _ : Unit => recordedSnatchG) (fun _ : Unit => recordedSnatchRisk) := by
  refine ⟨by simp [recordedSnatchPolicies], (), ?_, ?_, ?_⟩
  · exact ⟨.grim, by
      norm_num [IsArgminOn, recordedSnatchPolicies, recordedSnatchG]⟩
  · exact ⟨.alwaysAbstain, by
      norm_num [IsArgminOn, recordedSnatchPolicies, recordedSnatchRisk]⟩
  · intro πG πP hG hP
    have hg : πG = .grim ∨ πG = .probeOneToken := by
      cases πG <;> norm_num [IsArgminOn, recordedSnatchPolicies,
        recordedSnatchG] at hG
      all_goals simp
    have hp : πP = .alwaysAbstain := by
      cases πP <;> norm_num [IsArgminOn, recordedSnatchPolicies,
        recordedSnatchRisk] at hP
      all_goals simp
    rcases hg with rfl | rfl <;> rw [hp] <;> decide

inductive TypedAbsence where
  | noPatternAddressesThisTension
  deriving DecidableEq, Repr

structure Receipt where
  citesTextOrEdges : Prop
  scoreAlone : Prop

def Receipt.nonSelfCertifying (receipt : Receipt) : Prop :=
  receipt.citesTextOrEdges ∧ ¬ receipt.scoreAlone

structure FindResult (P : Type*) where
  selected : Set P
  receipts : P → Option Receipt
  absence : Option TypedAbsence

structure FindReceiptRow (Scenario P : Type*) where
  scenario : Scenario
  repository : Set P
  selected : Set P
  receipted : Set P
  nonSelfCertifying : Set P
  zeroMass : Set P
  absence : Option TypedAbsence

abbrev FindReceiptTable (Scenario P : Type*) := List (FindReceiptRow Scenario P)

/-- DELIBERATE IMPLEMENTATION REFUSAL · contract kind HOLE intentionally · owner: P-validated-R5 §3e find · holder: by-record · evidence: REFUSED — this is an implementation, not a law · falsifier: REFUSED for the same reason · Find maps a structured tension and repository to selected patterns, receipts, or typed absence. Its recorded F1–F4 instances do not select one canonical implementation. -/
def find {State P : Type*} : Tension State → Repository P → FindResult P := sorry

/-- CLOSED UNDER THE J9 CRITERION 2026-09-03 (worklist `:U46`) · owner: P-validated-R5 §3e F1 · holder: by-record · fixture: `futon3:checks/find-snatch.edn` · fixture-sha256: `c11673ea7164e90b10cc378ab6b2dfe14e545449d85e0dde70d5c2282e2430ce` · evidence: FindReceiptTable · falsifier: a selected pattern is outside the repository, or empty selection has no typed absence · SCOPE AMENDMENT 2026-08-31: the original declaration universally quantified over opaque, deliberately refused `find`; no serialized evidence could prove that correspondence. This predicate states exactly the recorded-row invariant: selection stays inside the recorded repository and an empty selection carries typed absence. CLOSE (criterion: futon2 `holes/labs/wm-contract/RUNBOOK.md`, which dispositions F1-F4 by name): leg (3) is `wmFindSnatchF1Containment`, `decide` over the 34 transcribed rounds, no `sorry`; leg (2) is `futon3:checks/find_snatch.clj` exiting 0 with `--negative-f1` rejected; leg (1) is INAPPLICABLE — the declared observation is a recorded find-receipt table over authored library text, not a run observation, so the run leg does not apply here rather than being met. -/
def findF1Containment {Scenario P : Type*} (row : FindReceiptRow Scenario P) : Prop :=
  row.selected ⊆ row.repository ∧
    (row.selected = ∅ → row.absence = some .noPatternAddressesThisTension)

/-- CLOSED UNDER THE J9 CRITERION 2026-09-03 (worklist `:U46`) · owner: P-validated-R5 §3e F2 · holder: by-record · fixture: `futon3:checks/find-snatch.edn` · fixture-sha256: `c11673ea7164e90b10cc378ab6b2dfe14e545449d85e0dde70d5c2282e2430ce` · evidence: FindReceiptTable · falsifier: a selected pattern has no receipt · SCOPE AMENDMENT 2026-08-31: the original declaration universally quantified over opaque, deliberately refused `find`; no serialized evidence could prove that correspondence. This predicate states exactly the recorded-row invariant: every selected member is in the recorded receipted set. CLOSE (criterion: futon2 `holes/labs/wm-contract/RUNBOOK.md`, which dispositions F1-F4 by name): leg (3) is `wmFindSnatchF2Receipted`, `decide` over the 34 transcribed rounds, no `sorry`; leg (2) is `futon3:checks/find_snatch.clj` exiting 0 with `--negative-f2` rejected; leg (1) is INAPPLICABLE for the reason given on findF1Containment. -/
def findF2Receipted {Scenario P : Type*} (row : FindReceiptRow Scenario P) : Prop :=
  row.selected ⊆ row.receipted

/-- CLOSED UNDER THE J9 CRITERION 2026-09-03 (worklist `:U46`) · owner: P-validated-R5 §3e F3 · holder: by-record · fixture: `futon3:checks/find-snatch.edn` · fixture-sha256: `c11673ea7164e90b10cc378ab6b2dfe14e545449d85e0dde70d5c2282e2430ce` · evidence: FindReceiptTable · falsifier: a selected pattern has only score evidence · SCOPE AMENDMENT 2026-08-31: the original declaration universally quantified over opaque, deliberately refused `find`; no serialized evidence could prove that correspondence. This predicate states exactly the recorded-row invariant: every selected member is in the set whose receipt cites text or authored edges and is not score-alone. CLOSE (criterion: futon2 `holes/labs/wm-contract/RUNBOOK.md`, which dispositions F1-F4 by name): leg (3) is `wmFindSnatchF3NonSelfCertifying`, `decide` over the 34 transcribed rounds, no `sorry`; leg (2) is `futon3:checks/find_snatch.clj` exiting 0 with `--negative-f3` rejected; leg (1) is INAPPLICABLE for the reason given on findF1Containment. The recorded non-self-certifying set equals the recorded receipted set in all 34 rows, so on THIS record the rejecting control, not the evidence, is what distinguishes F3 from F2. -/
def findF3NonSelfCertifying {Scenario P : Type*} (row : FindReceiptRow Scenario P) : Prop :=
  row.selected ⊆ row.nonSelfCertifying

/-- CLOSED UNDER THE J9 CRITERION 2026-09-03 (worklist `:U46`) · owner: P-validated-R5 §3e F4 · holder: by-record · fixture: `futon3:checks/find-snatch.edn` · fixture-sha256: `c11673ea7164e90b10cc378ab6b2dfe14e545449d85e0dde70d5c2282e2430ce` · evidence: FindReceiptTable · falsifier: a recorded zero-mass pattern is absent from the row repository or was selected · SCOPE AMENDMENT 2026-08-31: the original universal over opaque `find` was false for empty repositories and could not be connected to serialized evidence without assuming correspondence. This declaration is narrowed to one pinned `FindReceiptRow`: its declared zero-mass member is in the recorded repository and absent from the recorded selection. CLOSE (criterion: futon2 `holes/labs/wm-contract/RUNBOOK.md`, which dispositions F1-F4 by name): leg (3) is `wmFindSnatchF4Falsifiable`, `decide` over all six transcribed scenario rows at the `:selected-union` grain the check uses, no `sorry`; leg (2) is `futon3:checks/find_snatch.clj` exiting 0 with `--negative-f4` rejected; leg (1) is INAPPLICABLE for the reason given on findF1Containment. The row is no longer "deliberately tracked as an evidence obligation": the obligation is discharged, and what would still refute the claim is the falsifier field above. -/
def findF4Falsifiable {Scenario P : Type*} (row : FindReceiptRow Scenario P) : Prop :=
  row.repository.Nonempty ∧
    ∃ p, p ∈ row.repository ∧ p ∈ row.zeroMass ∧ p ∉ row.selected

/-! ### The pinned `find-snatch` record, transcribed (worklist `:U46`)

`futon3:checks/find-snatch.edn`, sha256 `c11673ea7164e90b10cc378ab6b2dfe14e545449d85e0dde70d5c2282e2430ce`, whose
`:as-of` is the futon3 commit `e58576cec0f14c3da4667ed452d522c561487ee8` that last touched
`library/snatch` -- 24 authored patterns, 6 scenarios, 34 recorded rounds.
This block is GENERATED from that file by
`futon2:holes/labs/wm-contract/u46_find_transcribe.bb`; edit the fixture and
regenerate rather than editing the literals.
-/

/-- The 24 authored Snatch patterns of the pinned record, in its
sorted order. Constructor names are the recorded ids in lowerCamel. -/
inductive SnatchPattern where
  | aFreeMarkIsAlwaysWorthAssigning
  | acceptAnOfferThatBeatsHolding
  | anUnmodelledResponseStopsTheLine
  | askForSurplusNotSurrender
  | consultTheRemedyBeforeExiting
  | escalateOnlyAsFarAsYouCanLose
  | exchangeWhenBothSidesGain
  | forcedPlayNeedsALossFloor
  | grimCutsTheCascadeAndNeverWidensIt
  | haveATemperament
  | institutionsVaryByPositionAndForce
  | leadWithTheExchangeRule
  | markWithoutForce
  | nonBindingTalkStillMovesPlay
  | playTheAuthoredOrderFirst
  | preserveTheRightToAbstain
  | priceTheFinalRoundAsFinal
  | probeBeforeCommitting
  | promoteTheRemedyBeforeTheExit
  | protectTheUnprotectedMove
  | reEnterAfterObservedRepair
  | revertThenInvert
  | useTalkToMakeATestableOffer
  | widenTheCascadeOnlyOnEvidence
  deriving DecidableEq, Repr

/-- The recorded repository as a list -- what `findF1Containment` contains
selection within, and where `findF4Falsifiable` finds its zero-mass member. -/
def snatchRepository : List SnatchPattern :=
  [.aFreeMarkIsAlwaysWorthAssigning, .acceptAnOfferThatBeatsHolding,
  .anUnmodelledResponseStopsTheLine, .askForSurplusNotSurrender,
  .consultTheRemedyBeforeExiting, .escalateOnlyAsFarAsYouCanLose,
  .exchangeWhenBothSidesGain, .forcedPlayNeedsALossFloor,
  .grimCutsTheCascadeAndNeverWidensIt, .haveATemperament,
  .institutionsVaryByPositionAndForce, .leadWithTheExchangeRule, .markWithoutForce,
  .nonBindingTalkStillMovesPlay, .playTheAuthoredOrderFirst, .preserveTheRightToAbstain,
  .priceTheFinalRoundAsFinal, .probeBeforeCommitting, .promoteTheRemedyBeforeTheExit,
  .protectTheUnprotectedMove, .reEnterAfterObservedRepair, .revertThenInvert,
  .useTalkToMakeATestableOffer, .widenTheCascadeOnlyOnEvidence]

/-- The six recorded scenarios, `treatment`/`disposition`
(`find_snatch.clj:22-24`, declaration order). -/
inductive FindSnatchScenario where
  | g1Snatcher
  | g1Sharer
  | g1Cautious
  | g4Snatcher
  | g2Snatcher
  | g5Sharer
  deriving DecidableEq, Repr

/-- The declared zero-mass pattern per scenario (`find_snatch.clj:25-31`),
as recorded in each scenario's `:f4` map. -/
def findSnatchZeroMass : FindSnatchScenario → List SnatchPattern
  | .g1Snatcher => [.consultTheRemedyBeforeExiting]
  | .g1Sharer => [.consultTheRemedyBeforeExiting]
  | .g1Cautious => [.consultTheRemedyBeforeExiting]
  | .g4Snatcher => [.forcedPlayNeedsALossFloor]
  | .g2Snatcher => [.consultTheRemedyBeforeExiting]
  | .g5Sharer => [.reEnterAfterObservedRepair]

/-- A recorded find row as a Lean literal: finite lists, so every predicate
over it is decidable. `round` is `some n` for a recorded round and `none`
for the scenario-grain row, whose `selected` is the recorded
`:selected-union`. -/
structure FindSnatchRowLit where
  scenario : FindSnatchScenario
  round : Option Nat
  selected : List SnatchPattern
  receipted : List SnatchPattern
  nonSelfCertifying : List SnatchPattern
  absence : Option TypedAbsence
  deriving DecidableEq, Repr

/-- The literal read as the `FindReceiptRow` the four declarations speak
about: each list becomes the set of its members, the repository and the
zero-mass set come from the record's own two constants. -/
def FindSnatchRowLit.toRow (r : FindSnatchRowLit) :
    FindReceiptRow FindSnatchScenario SnatchPattern where
  scenario := r.scenario
  repository := {p | p ∈ snatchRepository}
  selected := {p | p ∈ r.selected}
  receipted := {p | p ∈ r.receipted}
  nonSelfCertifying := {p | p ∈ r.nonSelfCertifying}
  zeroMass := {p | p ∈ findSnatchZeroMass r.scenario}
  absence := r.absence

/-- The 34 recorded rounds, in fixture order. The grain
`find_snatch.clj:157-171` iterates for F1, F2 and F3. -/
def findSnatchRounds : List FindSnatchRowLit :=
[
  { scenario := .g1Snatcher, round := some 1
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    absence := none },
  { scenario := .g1Snatcher, round := some 2
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    absence := none },
  { scenario := .g1Snatcher, round := some 3
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    absence := none },
  { scenario := .g1Snatcher, round := some 4
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    absence := none },
  { scenario := .g1Snatcher, round := some 5
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal]
    absence := none },
  { scenario := .g1Sharer, round := some 1
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    absence := none },
  { scenario := .g1Sharer, round := some 2
    selected := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    receipted := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    nonSelfCertifying := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    absence := none },
  { scenario := .g1Sharer, round := some 3
    selected := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    receipted := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    nonSelfCertifying := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    absence := none },
  { scenario := .g1Sharer, round := some 4
    selected := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    receipted := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    nonSelfCertifying := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    absence := none },
  { scenario := .g1Sharer, round := some 5
    selected := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .priceTheFinalRoundAsFinal]
    receipted := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .priceTheFinalRoundAsFinal]
    nonSelfCertifying := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .priceTheFinalRoundAsFinal]
    absence := none },
  { scenario := .g1Cautious, round := some 1
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    absence := none },
  { scenario := .g1Cautious, round := some 2
    selected := [.anUnmodelledResponseStopsTheLine, .askForSurplusNotSurrender,
      .exchangeWhenBothSidesGain, .probeBeforeCommitting]
    receipted := [.anUnmodelledResponseStopsTheLine, .askForSurplusNotSurrender,
      .exchangeWhenBothSidesGain, .probeBeforeCommitting]
    nonSelfCertifying := [.anUnmodelledResponseStopsTheLine, .askForSurplusNotSurrender,
      .exchangeWhenBothSidesGain, .probeBeforeCommitting]
    absence := none },
  { scenario := .g4Snatcher, round := some 1
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    absence := none },
  { scenario := .g4Snatcher, round := some 2
    selected := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain]
    receipted := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain]
    nonSelfCertifying := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain]
    absence := none },
  { scenario := .g4Snatcher, round := some 3
    selected := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain,
      .reEnterAfterObservedRepair]
    receipted := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain,
      .reEnterAfterObservedRepair]
    nonSelfCertifying := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain,
      .reEnterAfterObservedRepair]
    absence := none },
  { scenario := .g4Snatcher, round := some 4
    selected := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain]
    receipted := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain]
    nonSelfCertifying := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain]
    absence := none },
  { scenario := .g4Snatcher, round := some 5
    selected := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal, .reEnterAfterObservedRepair]
    receipted := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal, .reEnterAfterObservedRepair]
    nonSelfCertifying := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal, .reEnterAfterObservedRepair]
    absence := none },
  { scenario := .g2Snatcher, round := some 1
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting]
    absence := none },
  { scenario := .g2Snatcher, round := some 2
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    absence := none },
  { scenario := .g2Snatcher, round := some 3
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    absence := none },
  { scenario := .g2Snatcher, round := some 4
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    absence := none },
  { scenario := .g2Snatcher, round := some 5
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    absence := none },
  { scenario := .g2Snatcher, round := some 6
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    absence := none },
  { scenario := .g2Snatcher, round := some 7
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    absence := none },
  { scenario := .g2Snatcher, round := some 8
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    absence := none },
  { scenario := .g2Snatcher, round := some 9
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor]
    absence := none },
  { scenario := .g2Snatcher, round := some 10
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain]
    absence := none },
  { scenario := .g2Snatcher, round := some 11
    selected := []
    receipted := []
    nonSelfCertifying := []
    absence := some .noPatternAddressesThisTension },
  { scenario := .g2Snatcher, round := some 12
    selected := [.priceTheFinalRoundAsFinal]
    receipted := [.priceTheFinalRoundAsFinal]
    nonSelfCertifying := [.priceTheFinalRoundAsFinal]
    absence := none },
  { scenario := .g5Sharer, round := some 1
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting, .useTalkToMakeATestableOffer]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting, .useTalkToMakeATestableOffer]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .probeBeforeCommitting, .useTalkToMakeATestableOffer]
    absence := none },
  { scenario := .g5Sharer, round := some 2
    selected := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    receipted := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    nonSelfCertifying := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    absence := none },
  { scenario := .g5Sharer, round := some 3
    selected := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    receipted := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    nonSelfCertifying := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    absence := none },
  { scenario := .g5Sharer, round := some 4
    selected := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    receipted := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    nonSelfCertifying := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose]
    absence := none },
  { scenario := .g5Sharer, round := some 5
    selected := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .priceTheFinalRoundAsFinal]
    receipted := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .priceTheFinalRoundAsFinal]
    nonSelfCertifying := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .priceTheFinalRoundAsFinal]
    absence := none }
]

/-- The 6 recorded scenarios, each with its `:selected-union`.
The grain `find_snatch.clj:172-177` iterates for F4. -/
def findSnatchScenarios : List FindSnatchRowLit :=
[
  { scenario := .g1Snatcher, round := none
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal, .probeBeforeCommitting]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal, .probeBeforeCommitting]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal, .probeBeforeCommitting]
    absence := none },
  { scenario := .g1Sharer, round := none
    selected := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .exchangeWhenBothSidesGain, .priceTheFinalRoundAsFinal, .probeBeforeCommitting]
    receipted := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .exchangeWhenBothSidesGain, .priceTheFinalRoundAsFinal, .probeBeforeCommitting]
    nonSelfCertifying := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .exchangeWhenBothSidesGain, .priceTheFinalRoundAsFinal, .probeBeforeCommitting]
    absence := none },
  { scenario := .g1Cautious, round := none
    selected := [.anUnmodelledResponseStopsTheLine, .askForSurplusNotSurrender,
      .exchangeWhenBothSidesGain, .probeBeforeCommitting]
    receipted := [.anUnmodelledResponseStopsTheLine, .askForSurplusNotSurrender,
      .exchangeWhenBothSidesGain, .probeBeforeCommitting]
    nonSelfCertifying := [.anUnmodelledResponseStopsTheLine, .askForSurplusNotSurrender,
      .exchangeWhenBothSidesGain, .probeBeforeCommitting]
    absence := none },
  { scenario := .g4Snatcher, round := none
    selected := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal, .probeBeforeCommitting, .reEnterAfterObservedRepair]
    receipted := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal, .probeBeforeCommitting, .reEnterAfterObservedRepair]
    nonSelfCertifying := [.aFreeMarkIsAlwaysWorthAssigning, .askForSurplusNotSurrender,
      .consultTheRemedyBeforeExiting, .exchangeWhenBothSidesGain,
      .priceTheFinalRoundAsFinal, .probeBeforeCommitting, .reEnterAfterObservedRepair]
    absence := none },
  { scenario := .g2Snatcher, round := none
    selected := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor, .priceTheFinalRoundAsFinal, .probeBeforeCommitting]
    receipted := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor, .priceTheFinalRoundAsFinal, .probeBeforeCommitting]
    nonSelfCertifying := [.askForSurplusNotSurrender, .exchangeWhenBothSidesGain,
      .forcedPlayNeedsALossFloor, .priceTheFinalRoundAsFinal, .probeBeforeCommitting]
    absence := none },
  { scenario := .g5Sharer, round := none
    selected := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .exchangeWhenBothSidesGain, .priceTheFinalRoundAsFinal, .probeBeforeCommitting,
      .useTalkToMakeATestableOffer]
    receipted := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .exchangeWhenBothSidesGain, .priceTheFinalRoundAsFinal, .probeBeforeCommitting,
      .useTalkToMakeATestableOffer]
    nonSelfCertifying := [.askForSurplusNotSurrender, .escalateOnlyAsFarAsYouCanLose,
      .exchangeWhenBothSidesGain, .priceTheFinalRoundAsFinal, .probeBeforeCommitting,
      .useTalkToMakeATestableOffer]
    absence := none }
]

/-- A list-backed set is empty only when its list is: the bridge that lets the
empty-selection branch of `findF1Containment` be settled on the literal. -/
private theorem listNil_of_setOf_mem_eq_empty {α : Type*} {l : List α}
    (h : {a | a ∈ l} = (∅ : Set α)) : l = [] := by
  cases l with
  | nil => rfl
  | cons b t =>
    have hb : b ∈ ({a | a ∈ b :: t} : Set α) := by simp
    rw [h] at hb
    exact hb.elim

namespace FindSnatchRowLit

/-- F1 on the literal: every selected id is a member of the recorded repository,
and an empty selection carries the typed absence. Decidable by construction, so
`decide` settles it over the whole transcribed table. -/
def f1Ok (r : FindSnatchRowLit) : Bool :=
  r.selected.all (fun p => decide (p ∈ snatchRepository)) &&
    (!r.selected.isEmpty ||
      decide (r.absence = some TypedAbsence.noPatternAddressesThisTension))

/-- `f1Ok` is SOUND for the declaration: the Boolean check on the literal implies
the set-level proposition on the row it transcribes. Without this the `decide`
below would only be about lists. -/
theorem findF1Containment_toRow {r : FindSnatchRowLit} (h : r.f1Ok = true) :
    findF1Containment r.toRow := by
  rw [f1Ok, Bool.and_eq_true] at h
  obtain ⟨hsub, habs⟩ := h
  refine ⟨fun p hp => ?_, fun hempty => ?_⟩
  · have hmem : p ∈ r.selected := hp
    have : p ∈ snatchRepository :=
      of_decide_eq_true (List.all_eq_true.mp hsub p hmem)
    exact this
  · have hnil : r.selected = [] := listNil_of_setOf_mem_eq_empty hempty
    rw [hnil] at habs
    simpa [toRow] using habs

/-- F2 on the literal: every selected id is a member of the recorded receipted
set. -/
def f2Ok (r : FindSnatchRowLit) : Bool :=
  r.selected.all (fun p => decide (p ∈ r.receipted))

/-- `f2Ok` is SOUND for the declaration. -/
theorem findF2Receipted_toRow {r : FindSnatchRowLit} (h : r.f2Ok = true) :
    findF2Receipted r.toRow := by
  intro p hp
  have hmem : p ∈ r.selected := hp
  have : p ∈ r.receipted := of_decide_eq_true (List.all_eq_true.mp h p hmem)
  exact this

/-- F3 on the literal: every selected id is a member of the recorded
non-self-certifying set — the receipted patterns whose receipt is not
score-alone and cites a warrant file (`find_snatch.clj:166-171`). -/
def f3Ok (r : FindSnatchRowLit) : Bool :=
  r.selected.all (fun p => decide (p ∈ r.nonSelfCertifying))

/-- `f3Ok` is SOUND for the declaration. -/
theorem findF3NonSelfCertifying_toRow {r : FindSnatchRowLit} (h : r.f3Ok = true) :
    findF3NonSelfCertifying r.toRow := by
  intro p hp
  have hmem : p ∈ r.selected := hp
  have : p ∈ r.nonSelfCertifying := of_decide_eq_true (List.all_eq_true.mp h p hmem)
  exact this

/-- F4 on the literal: the scenario's declared zero-mass pattern is a member of
the recorded repository and is NOT in the recorded selection. -/
def f4Ok (r : FindSnatchRowLit) : Bool :=
  (findSnatchZeroMass r.scenario).any
    (fun p => decide (p ∈ snatchRepository) && !decide (p ∈ r.selected))

/-- `f4Ok` is SOUND for the declaration: the repository is nonempty because the
zero-mass witness is in it, so the existential and the nonemptiness conjunct are
discharged by the same recorded member. -/
theorem findF4Falsifiable_toRow {r : FindSnatchRowLit} (h : r.f4Ok = true) :
    findF4Falsifiable r.toRow := by
  rw [f4Ok, List.any_eq_true] at h
  obtain ⟨p, hzero, hp⟩ := h
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have hrepo : p ∈ snatchRepository := of_decide_eq_true hp.1
  have hsel : p ∉ r.selected := of_decide_eq_false hp.2
  exact ⟨⟨p, hrepo⟩, p, hrepo, hzero, hsel⟩

end FindSnatchRowLit

/-- CLOSED UNDER THE J9 CRITERION (worklist `:U46`, 2026-09-03) · leg (3) ·
Every one of the 34 recorded rounds of the pinned `find-snatch` record satisfies
`findF1Containment`: its selection lies inside the 18-member recorded repository,
and the one round that selected nothing (`g2`/`snatcher`, round 11) carries the
typed absence. Proved by `decide` over the transcribed table, no `sorry` — the
`wmTraceR2`/`wmTraceR8` precedent. The Clojure side of the same invariant is
`futon3:checks/find_snatch.clj:157-163`, whose `--negative-f1` control (a
selection member outside the repository) is rejected. -/
theorem wmFindSnatchF1Containment :
    ∀ row ∈ findSnatchRounds, findF1Containment row.toRow := by
  have h : findSnatchRounds.all FindSnatchRowLit.f1Ok = true := by decide
  exact fun row hrow =>
    FindSnatchRowLit.findF1Containment_toRow (List.all_eq_true.mp h row hrow)

/-- CLOSED UNDER THE J9 CRITERION (worklist `:U46`, 2026-09-03) · leg (3) ·
Every one of the 34 recorded rounds satisfies `findF2Receipted`: each selected
pattern carries a receipt in the same recorded row. Proved by `decide` over the
transcribed table, no `sorry`. The Clojure side is
`futon3:checks/find_snatch.clj:164-165`, whose `--negative-f2` control (the
first selected pattern's receipt dropped) is rejected. -/
theorem wmFindSnatchF2Receipted :
    ∀ row ∈ findSnatchRounds, findF2Receipted row.toRow := by
  have h : findSnatchRounds.all FindSnatchRowLit.f2Ok = true := by decide
  exact fun row hrow =>
    FindSnatchRowLit.findF2Receipted_toRow (List.all_eq_true.mp h row hrow)

/-- CLOSED UNDER THE J9 CRITERION (worklist `:U46`, 2026-09-03) · leg (3) ·
Every one of the 34 recorded rounds satisfies `findF3NonSelfCertifying`. Proved
by `decide` over the transcribed table, no `sorry`. STATED, because it bounds
what this proof shows: on this record the recorded non-self-certifying set IS
the recorded receipted set in all 34 rows — every receipt is
`:structured-antecedent` with a warrant file — so F3 discriminates nothing here
that F2 does not. What separates them is the rejecting control
`futon3:checks/find_snatch.clj --negative-f3` (a receipt rewritten to
score-alone), not the record. -/
theorem wmFindSnatchF3NonSelfCertifying :
    ∀ row ∈ findSnatchRounds, findF3NonSelfCertifying row.toRow := by
  have h : findSnatchRounds.all FindSnatchRowLit.f3Ok = true := by decide
  exact fun row hrow =>
    FindSnatchRowLit.findF3NonSelfCertifying_toRow (List.all_eq_true.mp h row hrow)

/-- CLOSED UNDER THE J9 CRITERION (worklist `:U46`, 2026-09-03) · leg (3) ·
Every one of the 6 recorded scenarios satisfies `findF4Falsifiable`: its declared
zero-mass pattern is in the 18-member recorded repository and absent from that
scenario's recorded `:selected-union`. Proved by `decide` over the transcribed
scenario table, no `sorry`. The grain is the union, matching
`futon3:checks/find_snatch.clj:172-177` — the statement per recorded ROUND is
weaker and follows from it. The `--negative-f4` control (the omitted member
struck from the recorded repository) is rejected. -/
theorem wmFindSnatchF4Falsifiable :
    ∀ row ∈ findSnatchScenarios, findF4Falsifiable row.toRow := by
  have h : findSnatchScenarios.all FindSnatchRowLit.f4Ok = true := by decide
  exact fun row hrow =>
    FindSnatchRowLit.findF4Falsifiable_toRow (List.all_eq_true.mp h row hrow)

inductive ReachOutside {P : Type*} (selected : Set P) (standsOn : P → P → Prop) : P → P → Prop
  | direct {u v} : standsOn u v → ReachOutside selected standsOn u v
  | through {u x v} : ReachOutside selected standsOn u x → x ∉ selected →
      standsOn x v → ReachOutside selected standsOn u v

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O3 · holder: by-record · Fast-forward connects selected endpoints through authored paths whose intermediate vertices are unselected. -/
def fastForward {P : Type*} (selected : Set P) (standsOn : P → P → Prop)
    (u v : P) : Prop :=
  u ∈ selected ∧ v ∈ selected ∧ ReachOutside selected standsOn u v

/-- FIELD AMENDMENT 2026-09-02 (worklist `:LA2`): `admittedBy` is O1's third node
origin. `futon3:holes/labs/library-contract/LA1c-restatement.md` §3.2 gives a
cascade node a provenance — `found | stoodOn | admittedBy (Pattern policy)` — and
before `:LA2` the third case could not arise, because nothing executed a
policy-grain rule and so nothing could emit an `admit` edit. It can now:
`futon3:checks/playout_snatch.clj` fires two of `library/snatch`'s six
policy-grain patterns through `construct`, and `apply-edit`'s `:admit` arm writes
`[:admitted-by <rule-id>]` into the cascade's `:provenance`. The field is a `Set
P` rather than the full `NodeOrigin` map because O1 is a statement about the
CARRIER of the nodes; which policy-grain rule admitted each one is recorded on
the Clojure side and is not what O1 quantifies over. It is `∅` in the C59 fixture
below, and in every cascade `futon3:checks/find_organise.clj` `organise` builds,
since neither temperament that file carries emits an `admit`. -/
structure CascadeDiff (P Score : Type*) where
  selected : Set P
  nodes : Set P
  addedByOrganise : Set P
  admittedBy : Set P
  authoredEdges : P → P → Prop
  organisedEdges : P → P → Prop
  precedenceBefore : List P
  precedenceAfter : List P
  actingOrderBefore : List P
  actingOrderAfter : List P
  scoreBefore : Score
  scoreAfter : Score

/-- DELIBERATE IMPLEMENTATION REFUSAL · contract kind HOLE intentionally · owner: P-validated-R5 §3e organise · holder: by-record · evidence: REFUSED — this is an implementation, not a law · falsifier: REFUSED for the same reason · Organise turns selected patterns and authored relations into a cascade, under a temperament — a cascade at policy grain. Its recorded O1–O4 instance does not select one canonical implementation. TYPE AMENDMENT 2026-09-02 (worklist `:L6`, taking the foresight of `futon3:holes/labs/library-contract/LA1c-restatement.md` §10): the temperament is now an argument. Under `Set P → Repository P → Cascade P` there was nowhere to put the policy-grain cascade that decides which patterns enter and in what precedence, and the two organise policies this file already records were therefore indistinguishable in the type: `checks/playout_snatch.clj` takes the up-closure under `standsOn`, while `wmCascadeDiffFixture` below keeps `nodes = selected` and fast-forwards through the unselected bridge. O1's narrowed form admits both, so the choice between them is data, and the temperament is where that datum lives. The STATUS does not move with the type: whether the refusal weakens to definable is LA2's to decide from a running policy-grain rule, not this amendment's. Clojure mirror: `futon3:checks/find_organise.clj` `organise`, which reads the temperament's closure policy and precedence and fires nothing. -/
def organise {Policy P : Type*} : Cascade Policy → Set P → Repository P → Cascade P := sorry

private def cascadeFixtureSelected : Set Nat
  | 0 | 2 => True
  | _ => False

private def cascadeFixtureAuthored : Nat → Nat → Prop
  | 0, 1 | 1, 2 => True
  | _, _ => False

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O1–O4 · holder: by-record · evidence: CascadeDiff · decided 2026-08-31 · Lean transcription of the independently hand-derived C59 fixture: 0=probe, 1=unselected bridge, 2=remedy. -/
def wmCascadeDiffFixture : CascadeDiff Nat Int :=
  { selected := cascadeFixtureSelected
    nodes := cascadeFixtureSelected
    addedByOrganise := ∅
    admittedBy := ∅
    authoredEdges := cascadeFixtureAuthored
    organisedEdges := fastForward cascadeFixtureSelected cascadeFixtureAuthored
    precedenceBefore := [0, 2]
    precedenceAfter := [2, 0]
    actingOrderBefore := [0, 2]
    actingOrderAfter := [2, 0]
    scoreBefore := 3
    scoreAfter := -5 }

private theorem reachOutside_to_reach {P : Type*} {selected : Set P}
    {r : P → P → Prop} {u v : P} : ReachOutside selected r u v → Reach r u v := by
  intro path
  induction path with
  | direct edge => exact Reach.single edge
  | through _ _ edge ih => exact Reach.tail ih edge

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O1 · holder: by-record · evidence: CascadeDiff · falsifier: nodes differ from the union of the three recorded origins · SCOPE AMENDMENT 2026-08-31: formerly a universal claim about refused `organise`; now the witnessed C59 instance only. UNION AMENDMENT 2026-09-02 (worklist `:LA2`): the union is three-way. A node is in the cascade because `find` selected it, because organise closed over an authored edge to it, or because a policy-grain THEN admitted it — and O1's content is that there is no FOURTH way in. Under the two-way union the third origin had no carrier, so an admitted node would have had to be smuggled in as `addedByOrganise` and would have read as authored closure. -/
def organiseO1NodesRecorded :
    wmCascadeDiffFixture.nodes =
      wmCascadeDiffFixture.selected ∪ wmCascadeDiffFixture.addedByOrganise ∪
        wmCascadeDiffFixture.admittedBy := by
  ext x
  simp [wmCascadeDiffFixture]

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O2 · holder: by-record · evidence: CascadeDiff · falsifier: an organised edge lacks authored reachability · SCOPE AMENDMENT 2026-08-31: formerly a universal claim about refused `organise`; now the witnessed C59 instance only. -/
def organiseO2AuthoredReachability :
    ∀ u v, wmCascadeDiffFixture.organisedEdges u v →
      Reach wmCascadeDiffFixture.authoredEdges u v := by
  intro u v edge
  exact reachOutside_to_reach edge.2.2

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O3 · holder: by-record · evidence: CascadeDiff · falsifier: organised edges differ from selected-endpoint fast-forwards · SCOPE AMENDMENT 2026-08-31: formerly a universal claim about refused `organise`; now exactness for the witnessed C59 instance only. -/
def organiseO3FastForward :
    ∀ u v, wmCascadeDiffFixture.organisedEdges u v ↔
      fastForward wmCascadeDiffFixture.selected wmCascadeDiffFixture.authoredEdges u v := by
  intro u v
  rfl

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O4 and S-G4 · holder: by-record · evidence: CascadeDiff · falsifier: changed precedence changes neither acting order nor score · SCOPE AMENDMENT 2026-08-31: the former arbitrary-function existential was false for constant functions and empty carriers; this declaration requires the fixture's precedence change explicitly and states its witnessed consequence. -/
def organiseO4PrecedenceGovernance
    (_precedenceSensitive : wmCascadeDiffFixture.precedenceBefore ≠
      wmCascadeDiffFixture.precedenceAfter) :
    wmCascadeDiffFixture.actingOrderBefore ≠ wmCascadeDiffFixture.actingOrderAfter ∨
      wmCascadeDiffFixture.scoreBefore ≠ wmCascadeDiffFixture.scoreAfter := by
  left
  norm_num [wmCascadeDiffFixture]

-- F12 SLICE 2 TRANSCRIPTION BEGIN (checked by
-- futon2:holes/labs/wm-contract/f12_zaif_transcription.clj)
/-- The zaif library cascade as a `CascadeDiff`, transcribed from
`futon3:checks/zaif-cascade.edn` run `:widen-to-a-budget` over the `@why`
relation of `library/` at `futon3` commit `1b8b1d1`.  Index table and every
number below are derived by
`futon2:holes/labs/wm-contract/f12_zaif_transcription.clj` into
`runs/F12-organise/01-zaif-transcription.edn`, which also re-reads this block
and fails if the two disagree; nothing here is hand-entered without that check.

WHY A SECOND FIXTURE AND NOT A REPLACEMENT.  `wmCascadeDiffFixture` above is
the three-node C59 fixture, in which `admittedBy = ∅` and `nodes = selected`.
Both coincidences hide something.  `admittedBy = ∅` makes O1's three-way union
witnessed trivially — the third origin contributes nothing — and this cascade's
9 admitted nodes make it non-trivial.  `nodes = selected` makes the two readings
of O3 indistinguishable, which `organiseO3FastForwardOverSelectedFails` below
shows is not a harmless coincidence.

THE INDEX, from the record and nothing else: `0-10` are the 11 patterns `find`
selected (`:find :selected`), `11-19` the 9 the policy-grain rule admitted
(`:runs :widen-to-a-budget :cascade :provenance`, the entries carrying
`[:admitted-by :widen-the-cascade-only-on-evidence]`), `20-26` the 7 vertices
that are authored targets reachable from a node but are not nodes — the bridges
`fastForward` routes around.  Ids in the artifact.

WHAT IS NOT TRANSCRIBED, and why the four O4 fields are empty rather than
plausible.  `futon3:checks/construct_cascade.clj` `cascade-of` (`:402`, the two fields at
`:420-421`) sets
`:precedence-before []` and `:precedence-after []` for exactly this run and
carries no score at all, because nothing was played: the record's `:o4` reads
`:not-exercised-fewer-than-two-members-carry-a-play-grain-rule`.  So the O4
fields here are `[]`/`0` and NO O4 statement is made of this fixture.  That gap
is F12 slice 3's, not this one's. -/
private def zaifSelected : Set Nat := {n | n < 11}

private def zaifAdmitted : Set Nat := {n | 11 ≤ n ∧ n < 20}

private def zaifNodes : Set Nat := {n | n < 20}

/-- The 13 authored `@why` edges over the 27 vertices the cascade's nodes reach,
at the transcription basis.  Direction is `standsOn`: `u` stands on `v`. -/
private def zaifAuthored : Nat → Nat → Prop
  | 6, 26 | 7, 20 | 14, 23 | 15, 22 | 16, 24 | 17, 20 | 18, 19 | 19, 20
  | 22, 24 | 23, 26 | 24, 21 | 25, 21 | 26, 25 => True
  | _, _ => False

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O1–O3 · holder: by-record ·
evidence: CascadeDiff · decided 2026-09-06 · The zaif run of the library
cascade, 20 nodes over 1239 patterns.  `organisedEdges` is `fastForward` over
`nodes`, which is what `construct_cascade.clj:415` passes. -/
def wmZaifCascadeDiffFixture : CascadeDiff Nat Int :=
  { selected := zaifSelected
    nodes := zaifNodes
    addedByOrganise := ∅
    admittedBy := zaifAdmitted
    authoredEdges := zaifAuthored
    organisedEdges := fastForward zaifNodes zaifAuthored
    precedenceBefore := []
    precedenceAfter := []
    actingOrderBefore := []
    actingOrderAfter := []
    scoreBefore := 0
    scoreAfter := 0 }

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O1 · holder: by-record ·
evidence: CascadeDiff · falsifier: a node in none of the three recorded origins ·
O1 on a real construction: unlike the C59 fixture, `admittedBy` here is the 9
nodes a policy-grain THEN admitted, so the third origin supplies 9 of the 20
nodes and the union is not `selected ∪ ∅ ∪ ∅`. -/
def organiseO1NodesRecordedZaif :
    wmZaifCascadeDiffFixture.nodes =
      wmZaifCascadeDiffFixture.selected ∪ wmZaifCascadeDiffFixture.addedByOrganise ∪
        wmZaifCascadeDiffFixture.admittedBy := by
  ext x
  simp [wmZaifCascadeDiffFixture, zaifNodes, zaifSelected, zaifAdmitted]
  omega

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O2 · holder: by-record ·
evidence: CascadeDiff · falsifier: an organised edge lacks authored reachability ·
The zaif instance of O2. -/
def organiseO2AuthoredReachabilityZaif :
    ∀ u v, wmZaifCascadeDiffFixture.organisedEdges u v →
      Reach wmZaifCascadeDiffFixture.authoredEdges u v := by
  intro u v edge
  exact reachOutside_to_reach edge.2.2

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O3 · holder: by-record ·
evidence: CascadeDiff · falsifier: organised edges differ from the
node-endpoint fast-forwards · O3 for the zaif instance, stated over `nodes` —
the set `construct_cascade.clj:415` and `find_organise.clj:529` both pass. -/
def organiseO3FastForwardZaif :
    ∀ u v, wmZaifCascadeDiffFixture.organisedEdges u v ↔
      fastForward wmZaifCascadeDiffFixture.nodes wmZaifCascadeDiffFixture.authoredEdges u v := by
  intro u v
  rfl

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O3 · holder: by-record ·
evidence: CascadeDiff · falsifier: the two readings of O3 agree on this
cascade · WHAT THE C59 FIXTURE CANNOT SEE.  `organiseO3FastForward` above
states O3 with `.selected`; the Clojure law `o3-fast-forward`
(`futon3:checks/find_organise.clj:529`) evaluates `fast-forward` over `nodes`,
as does the constructor that builds the edges (`:415`).  On the C59 fixture
`nodes = selected`, so the two forms are the same proposition and the file has
never had to choose.  Here they are not: the cascade's one organised edge runs
between vertices 18 and 19, both ADMITTED and so neither selected, and
`fastForward` over the 11 selected is empty.  This states the disagreement
rather than repairing either side.  Which set O3 is owed is a SECOND question,
next to but not the same as C539 §4's decision D1 — D1 asks which carrier the
laws are stated of, this asks which of that carrier's two fields O3 quantifies
over — and both are Joe's, not a slice's. -/
def organiseO3FastForwardOverSelectedFails :
    ¬ (∀ u v, wmZaifCascadeDiffFixture.organisedEdges u v ↔
        fastForward wmZaifCascadeDiffFixture.selected
          wmZaifCascadeDiffFixture.authoredEdges u v) := by
  intro h
  have edge : wmZaifCascadeDiffFixture.organisedEdges 18 19 := by
    refine ⟨?_, ?_, ReachOutside.direct ?_⟩
    · show (18 : Nat) ∈ zaifNodes
      simp [zaifNodes]
    · show (19 : Nat) ∈ zaifNodes
      simp [zaifNodes]
    · trivial
  have selectedEnd := ((h 18 19).mp edge).1
  simp [wmZaifCascadeDiffFixture, zaifSelected] at selectedEnd
-- F12 SLICE 2 TRANSCRIPTION END

inductive Layer where
  | L1
  | L2
  deriving DecidableEq, Repr

structure Claim (Part : Type*) where
  producingPart : Set Part

structure Witness (Part : Type*) where
  producer : Part
  layer : Layer

/-- CLOSED-BY-RECORD · owner: P-R9 S1 · holder: by-record · Independence means the witness producer is outside the claim's producing part. -/
def independent {Part : Type*} (claim : Claim Part) (witness : Witness Part) : Prop :=
  witness.producer ∉ claim.producingPart

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 2 · holder: by-record · The verdict is three-valued: `unknown` is a value, not the absence of one (claude-20's proposal, ratified 2026-08-30 — run (i) against the ledger alone returns `unknown` for all thirteen). -/
inductive IndependenceVerdict where
  | independent
  | self
  | unknown
  deriving DecidableEq, Repr

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 1–2 · holder: by-record · The decision procedure: no declared producing part → `unknown`; producer inside it → `self`; outside → `independent`. `producingPart` is DECLARED (a cited declaration record), never inferred. -/
def independenceVerdict {Part : Type*} [DecidableEq Part]
    (declared : Option (Claim Part)) (witness : Witness Part)
    (decide? : Part → Set Part → Bool) : IndependenceVerdict :=
  match declared with
  | none => .unknown
  | some claim => if decide? witness.producer claim.producingPart then .self else .independent

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 3 · holder: by-record · What it means for a membership checker to be SOUND for verdicts: a witness whose producer is inside the declared part is never judged `independent`, and `independent` is returned only when the Prop holds. Stated as a predicate on a GIVEN checker — no soundness hypothesis, so it can be false of a broken one (review fix, same family as r2ContractCensus: the earlier form assumed `_sound` and could not fail). -/
def r9CheckerSound {Part : Type*} [DecidableEq Part] (decide? : Part → Set Part → Bool) : Prop :=
  ∀ (claim : Claim Part) (witness : Witness Part),
    (witness.producer ∈ claim.producingPart →
      independenceVerdict (some claim) witness decide? ≠ .independent) ∧
    (independenceVerdict (some claim) witness decide? = .independent → independent claim witness)

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 3 (claude-13's load-bearing lemma, ratified 2026-08-30) · holder: by-record · evidence: a proof term · falsifier: `independenceVerdict` decides membership itself and ignores `decide?` · The checker argument is load-bearing: there is an UNSOUND `decide?` under which a self-producer is judged `independent` — so a wrong checker can be detected, and the Lean definition does not bypass its own argument. -/
def r9VerdictConsultsChecker :
  ∀ {Part : Type*} [DecidableEq Part] (claim : Claim Part) (w : Witness Part),
    w.producer ∈ claim.producingPart →
    ∃ decide? : Part → Set Part → Bool,
      ¬ (∀ p S, decide? p S = true ↔ p ∈ S) ∧
      independenceVerdict (some claim) w decide? = .independent := by
  intro Part inst claim w hw
  refine ⟨fun _ _ => false, ?_, ?_⟩
  · intro h
    have inside := (h w.producer claim.producingPart).mpr hw
    simp at inside
  · simp [independenceVerdict]

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 2 (declaration source) · holder: by-record · Where a row's declaration of the producing part came from: the paper's sentence (sec-discussion.tex:238) or the row's own text naming a closer. A sum type, so "per-row" is per-row in fact — a free string let every row be labelled "paper:…" (claude-13's 5th read via claude-20, ratified 2026-08-30). -/
inductive DeclarationSource where
  | paperSentence
  | rowText (id : String)
  deriving DecidableEq, Repr

/-- Fixture scaffolding: one recorded verdict row — the FACTS from the artefact (producer, declared part) and the checker's verdict. Membership is COMPUTED below, never transcribed: a transcribed `inDeclaredPart` let the transcriber set both sides of the soundness implication (R9's own subject matter recreated inside its contract — claude-13, 2026-08-30). -/
structure VerdictRow where
  row : String
  declarationSource : DeclarationSource
  producer : String
  declaredPart : List String
  verdict : IndependenceVerdict
  deriving DecidableEq, Repr

/-- Derived, not transcribed. -/
def VerdictRow.inDeclaredPart (r : VerdictRow) : Bool := r.producer ∈ r.declaredPart

abbrev VerdictTable := List VerdictRow

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 3 · holder: by-record · Soundness of a RECORDED table: no row whose closer is inside the declared part is judged `independent`; a row judged `independent` has its closer outside. Decidable; false exactly when the checker is broken. (Replaces r9WmCheckerSound, which quantified over every checker and was false for `fun _ _ => false` — claude-13, 2026-08-30, fourth member of the family.) -/
def r9VerdictsSound (table : VerdictTable) : Prop :=
  ∀ r ∈ table, (r.inDeclaredPart = true → r.verdict ≠ .independent) ∧
               (r.verdict = .independent → r.inDeclaredPart = false)

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 2 (per-row declarations) · holder: by-record · Exactly the three rows that name a specific closer (O7, O14, O15 — R9-D1b) carry a row-text declaration; every other row carries the paper's sentence. -/
def r9PerRowDeclarations (t : VerdictTable) : Prop :=
  ∀ r ∈ t, (r.row ∈ ["O7", "O14", "O15"]) ↔ (∃ id, r.declarationSource = .rowText id)

private def wmVerdictRowIds : List String :=
  ["O1", "O2", "O3", "O5", "O6", "O7", "O8", "O9", "O14", "O15", "O16", "O17", "O20"]

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 2 (fixture) · holder: by-record · evidence: VerdictTable · falsifier: a row missing or a verdict absent · The pinned R9-D2 ledger-only run: absence of a producing-part declaration is represented by `unknown`, never coerced to either verdict. -/
def wmVerdictsLedgerAlone : VerdictTable := wmVerdictRowIds.map fun id =>
  { row := id, declarationSource := .paperSentence, producer := "unknown",
    declaredPart := [], verdict := .unknown }

private def declaredVerdictRow (id : String) : VerdictRow :=
  if id = "O7" ∨ id = "O14" ∨ id = "O15" then
    { row := id, declarationSource := .rowText id,
      producer := if id = "O15" then "zai" else "codex-1",
      declaredPart := ["author", "codex-1", "codex-7", "zai"], verdict := .self }
  else
    { row := id, declarationSource := .paperSentence, producer := "author",
      declaredPart := ["author"], verdict := .self }

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 2 (fixture) · holder: by-record · evidence: VerdictTable · falsifier: a row missing or a verdict absent · The pinned R9-D2 declared-part run. -/
def wmVerdictsDeclared : VerdictTable := wmVerdictRowIds.map declaredVerdictRow

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 3 (falsifier) · holder: by-record · evidence: wmVerdictsDeclared · falsifier: a row with inDeclaredPart = true judged independent · The shipped checker's recorded verdicts are sound. Proved directly over the source table; false if the checker is broken. -/
def r9WmVerdictsSound : r9VerdictsSound wmVerdictsDeclared := by
  simp [r9VerdictsSound, wmVerdictsDeclared, wmVerdictRowIds,
    declaredVerdictRow, VerdictRow.inDeclaredPart]

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 2 (per-row declarations) · holder: by-record · evidence: wmVerdictsDeclared · falsifier: a named-agent row under the paper's sentence, or an unnamed row under row text · The run-(ii) source table's declaration sources are per-row in fact. -/
def r9WmPerRowDeclarations : r9PerRowDeclarations wmVerdictsDeclared := by
  simp [r9PerRowDeclarations, wmVerdictsDeclared, wmVerdictRowIds,
    declaredVerdictRow]

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 2 (the two runs, R9-D1b) · holder: by-record · evidence: both tables · falsifier: run (i) not all `unknown`; run (ii) any row ≠ `self` under the declaration that places commissioned agents inside the author's part — the three named-agent rows (O7, O14, O15) are where this can fail · Proved over the compact source tables: 13 unknown / 13 self. -/
def r9TwoRunCensus :
    wmVerdictsLedgerAlone.length = 13 ∧ wmVerdictsDeclared.length = 13 ∧
    (∀ r ∈ wmVerdictsLedgerAlone, r.verdict = .unknown) ∧
    (∀ r ∈ wmVerdictsDeclared, r.verdict = .self) := by
  simp [wmVerdictsLedgerAlone, wmVerdictsDeclared, wmVerdictRowIds,
    declaredVerdictRow]

/-- A value-evidence predicate carrying the admission law that excludes L1. -/
structure ValueEvidencePolicy (Part : Type*) where
  accepts : Witness Part → Prop
  l2Only : ∀ w, accepts w → w.layer = Layer.L2

/-- CLOSED-BY-RECORD · owner: P-R9 S1 · holder: by-record · SCOPE AMENDMENT 2026-08-31: the former theorem quantified over an unconstrained predicate and was false (`fun _ => True` accepts L1). The missing L2 admission hypothesis now travels in `ValueEvidencePolicy` and cannot be omitted at a call site. -/
def valueEvidenceRequiresL2 {Part : Type*} (policy : ValueEvidencePolicy Part)
    (w : Witness Part) (accepted : policy.accepts w) : w.layer = Layer.L2 :=
  policy.l2Only w accepted

inductive DeliveryGuarantee where
  | exactlyOnce
  | atLeastOnce
  deriving DecidableEq, Repr

structure Retry where
  cap : Nat
  sameIdentity : Bool

/-- CLOSED-BY-RECORD · owner: delivery-lifecycle §0.6 · holder: by-record · Delivery := {from, to, payload : Schema, guarantee, atomic-with, retry, timeout-ms, idem-key, receipt : Schema} (review fix: D1b's field list was not the record's). -/
structure Delivery (Role Schema Write Key : Type*) where
  «from» : Role
  «to» : Role
  payload : Schema
  guarantee : DeliveryGuarantee
  atomicWith : List Write
  retry : Retry
  timeoutMs : Nat
  idemKey : Key
  receipt : Schema

/-- CLOSED-BY-RECORD · owner: delivery-lifecycle §0.10 · holder: by-record · Handoff := {artefact, from, to, at, iteration, awaiting, deadline, receipt} (review fix: D1b's field list was not the record's). -/
structure Handoff (Artefact Role Time JobId Deadline Receipt : Type*) where
  artefact : Artefact
  «from» : Role
  «to» : Role
  «at» : Time
  iteration : Nat
  awaiting : List JobId
  deadline : Deadline
  receipt : Receipt

/-- CLOSED-BY-RECORD · owner: delivery-lifecycle §0.10 · holder: by-record · Workflow := {holder : Role, iteration, history : List Handoff} — provenance is `history` (review fix: D1b had only the list). -/
structure Workflow (Role Handoff : Type*) where
  holder : Role
  iteration : Nat
  history : List Handoff

structure R2Tick (Channel Value : Type*) where
  observation : Channel → Option Value

/-- CLOSED-BY-RECORD · owner: P-R2 §solved 1 · holder: by-record · A tick is well-formed against the DECLARED channel list (declaration order, `observation.clj:18–32`) — never against the keys it happens to carry (review fix: the earlier `= Set.univ` form was vacuous or refuted depending on where `Channel` came from; claude-20 2026-08-30). -/
def r2WellFormed {Channel Value : Type*} (declared : List Channel)
    (tick : R2Tick Channel Value) : Prop :=
  ∀ channel, (tick.observation channel).isSome ↔ channel ∈ declared

/-- CLOSED-BY-RECORD · owner: P-R2 §solved 1 · holder: by-record · The census is a COMPUTED value: how many ticks of a corpus fail the declared list (review fix, codex-1 via claude-20 2026-08-30: the earlier form universally quantified the answer and was false for every instantiation). -/
def r2ContractCensus {Channel Value : Type*} (corpus : List (R2Tick Channel Value))
    (wellFormed? : R2Tick Channel Value → Bool) : Nat :=
  (corpus.filter (fun tick => !wellFormed? tick)).length

/-- CLOSED-BY-RECORD · owner: P-R2 §solved 1 (Channel) · holder: by-record · evidence: ChannelWitness · falsifier: the declared names or order differ from the 14-channel record · The fourteen declared channels as NAMED constructors in declaration order (`observation.clj:18–32`) — identity and order, not arity. Presence/typed absence belongs to a measurement at a channel, not to channel identity. -/
inductive Channel where
  | loopHealth | supportCoverage | attackCoverage | missionHealth | stackPct | consultingPct
  | portfolioPct | mathematicsPct | activeRepoRatio | sorryCountNorm | couplingDensity
  | ticksFiringRatio | depositingSignal | annotationHealth
  deriving DecidableEq, Repr

/-- The fourteen channels in declaration order — the list a census iterates (no typeclass needed). -/
def Channel.all : List Channel :=
  [.loopHealth, .supportCoverage, .attackCoverage, .missionHealth, .stackPct, .consultingPct,
   .portfolioPct, .mathematicsPct, .activeRepoRatio, .sorryCountNorm, .couplingDensity,
   .ticksFiringRatio, .depositingSignal, .annotationHealth]

/-- Fixture scaffolding: a wm-trace tick as a Lean literal — for each of the 14 declared channels, present or not (order = declaration order, `observation.clj:18–32`). The adapter (P-lean-clojure-adapter, AD-D2/D3) transcribes the run into this type. -/
abbrev R2TickLit := R2Tick Channel Unit

/-- Content watermark for the immutable R2 snapshot: 54 files / 801 forms, SHA-256 over newline-joined sorted form hashes. It names the captured corpus, not a promise to follow later STORE growth. -/
def wmTraceR2ContentPin : String :=
  "b2c3aeb408cc4de59947ad93f9c1ea17b735fc0da26e188ada7c24609bffbca1"

private def r2CompleteTick : R2TickLit := { observation := fun _ => some () }
private def r2MissingAnnotationTick : R2TickLit :=
  { observation := fun c => if c = .annotationHealth then none else some () }

/-- CLOSED-BY-RECORD · owner: P-R2 §solved 1 (fixture) · holder: by-record · evidence: List R2TickLit · falsifier: digest differs from `wmTraceR2ContentPin` · SNAPSHOT 2026-08-31: the pinned 801-form corpus, represented extensionally as its two annotation-health absences followed by 799 complete channel rows. Future corpus growth does not rewrite this value. -/
def wmTraceR2 : List R2TickLit :=
  [r2MissingAnnotationTick, r2MissingAnnotationTick] ++ List.replicate 799 r2CompleteTick

/-- CLOSED-BY-RECORD · owner: P-R2 §solved 1 · holder: by-record · evidence: IllFormedList · falsifier: the pinned census is not 2 · Against the declared 14 channels the pinned 801-form snapshot has exactly the two annotation-health absences. -/
def r2ContractCensusWmTrace :
    r2ContractCensus wmTraceR2 (fun tick => Channel.all.all (fun c => (tick.observation c).isSome)) = 2 := by
  native_decide

inductive FreeEnergyShape where
  | gMap          -- `:free-energy` holds {:G-total …}         (760 forms, files 05-18 … 07-09)
  | controllerMap -- `:free-energy` holds {:controller-score …} (32 forms, files 07-14 … 07-21, 08-30)
  | unknown       -- neither key, or both — never observed; a finding if it ever is
  deriving DecidableEq, Repr

/-- Field names follow the artefact's keys (`:prediction-errors`, `:precision-state`, `:variational-free-energy`, `:selection-gain`), so clause-2 signature comparison against the Clojure census is literal (review fix, claude-20 2026-08-30). -/
structure R8Tick (Errors Precision Gain : Type*) where
  predictionErrors : Option Errors
  precisionState : Option Precision
  storedF : Option ℝ
  selectionGain : Option Gain
  hasControllerScore : Bool   -- FACT: `:free-energy` carries the key `:controller-score`
  hasGTotal : Bool            -- FACT: `:free-energy` carries the key `:G-total`
  fileDate : Nat   -- YYYYMMDD of the trace file

/-- DERIVED, not transcribed: the shape of `:free-energy` is a classification of two key-presence facts (claude-20's question at R8-D3, 2026-08-30 — a generator writing `gMap`/`controllerMap` would be writing what the era law tests, R9's `inDeclaredPart` one level subtler). `unknown` when neither or both keys are present — a possible outcome, and a finding. -/
def R8Tick.freeEnergyShape {Errors Precision Gain : Type*} (t : R8Tick Errors Precision Gain) : FreeEnergyShape :=
  if t.hasControllerScore && !t.hasGTotal then .controllerMap
  else if t.hasGTotal && !t.hasControllerScore then .gMap
  else .unknown

inductive R8Disposition where
  | missingFComputable
  | storedF
  | insufficientInputs
  deriving DecidableEq, Repr

/-- CLOSED-BY-RECORD · owner: P-R8 §solved 1 · holder: by-record · R8 records exactly missing-computable, stored, or insufficient-inputs. -/
def r8Disposition {Errors Precision Gain : Type*}
    (tick : R8Tick Errors Precision Gain) : R8Disposition :=
  match tick.predictionErrors, tick.precisionState, tick.storedF with
  | some _, some _, none => .missingFComputable
  | some _, some _, some _ => .storedF
  | _, _, _ => .insufficientInputs

/-- CLOSED-BY-RECORD · owner: P-R8 §solved 1 (census) · holder: by-record · The three-disposition census as a COMPUTED triple (same review fix as r2ContractCensus). -/
def r8Census {Errors Precision Gain : Type*} (corpus : List (R8Tick Errors Precision Gain)) :
    Nat × Nat × Nat :=
  ((corpus.filter (fun t => decide (r8Disposition t = R8Disposition.missingFComputable))).length,
   (corpus.filter (fun t => decide (r8Disposition t = R8Disposition.storedF))).length,
   (corpus.filter (fun t => decide (r8Disposition t = R8Disposition.insufficientInputs))).length)

/-- Fixture scaffolding: a wm-trace form as a Lean literal with the fields the R8 laws read. -/
abbrev R8TickLit := R8Tick Unit Unit Unit

/-- CLOSED-BY-RECORD · owner: P-R8 §solved 1 (fixture) · holder: by-record · evidence: the corpus itself, transcribed · falsifier: the digest recomputed by the method stated in P-R8 §content-pin (`:sha256-over-newline-joined-sorted-form-sha256`, published by `checks/r8_f_contract.clj`) differs from the value recorded there for the same 53 files / 792 forms — today `c9add16a…`; a value without its method is not a pin (claude-20 / codex-12, 2026-08-30) · The 792 forms as a Lean literal — filled by the adapter from the run. -/
def wmTraceR8 : List R8TickLit :=
[
  { predictionErrors := none
    precisionState := none
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260518 },
  { predictionErrors := none
    precisionState := none
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260518 },
  { predictionErrors := some ()
    precisionState := none
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260518 },
  { predictionErrors := some ()
    precisionState := none
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260518 },
  { predictionErrors := some ()
    precisionState := none
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260518 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260518 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260518 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260519 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260519 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260519 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260519 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260519 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260519 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260519 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260519 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260519 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260521 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260522 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260523 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260524 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260525 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260526 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260527 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260527 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260527 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260527 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260527 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260527 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260527 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260527 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260527 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260530 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260530 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260531 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260601 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260602 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260603 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260604 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260605 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260606 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260607 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260608 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260609 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260610 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260612 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260612 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260612 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260612 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260612 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260612 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260612 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260613 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260614 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260615 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260615 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260615 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260615 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260615 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260615 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260615 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260615 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260616 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260617 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260618 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260621 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260621 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260621 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260622 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260623 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260624 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260624 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260624 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260624 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260624 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260624 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260624 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260624 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260624 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260624 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260625 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260626 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260627 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260627 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260627 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260627 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260627 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260627 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260627 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260627 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260627 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260627 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260627 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260628 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260629 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260630 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260701 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260702 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260703 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260704 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260705 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260706 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := none
    selectionGain := none
    hasControllerScore := false
    hasGTotal := true
    fileDate := 20260709 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260714 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260715 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260715 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260715 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260715 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260715 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260715 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260716 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260716 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260716 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260716 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260716 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260716 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260717 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260718 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260719 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260721 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260721 },
  { predictionErrors := some ()
    precisionState := some ()
    storedF := some 0
    selectionGain := some ()
    hasControllerScore := true
    hasGTotal := false
    fileDate := 20260830 }
]

/-- CLOSED-BY-RECORD · owner: P-R8 §solved 1 (census) · holder: by-record · evidence: the triple with tick ids per disposition · falsifier: the census over the transcribed corpus is not (755, 32, 5) · Stated about the fixture constant (family fix, 2026-08-30). Moves by `decide` once `wmTraceR8` is transcribed. -/
def r8CensusWmTrace : r8Census wmTraceR8 = (755, 32, 5) := by
  native_decide

/-- CLOSED-BY-RECORD · owner: P-R8 §solved 1 (iii), by era · holder: by-record · evidence: EraTable · falsifier: a post-boundary form without stored F, or a pre-boundary form with one (non-interleaving fails) · CORRECTED 2026-08-30 (claude-13 via claude-20): `:free-energy`, `:variational-free-energy` and `:selection-gain` are three keys of ONE unconditional map literal (`war_machine.clj:4664–4687`), so conjuncts 1–2 are a write-site identity, not two facts; the only CONTINGENT conjunct is 3 — the stored-F forms are a contiguous date suffix (non-interleaving), and since the boundary 20260714 was read off the data, "0 violations at that boundary" tests contiguity, not the date. Proved by decision over the full 792-row source object. Precision scale remains the proximate driver of the F gap; cause untested. -/
def r8EraBoundary :
    ∀ t ∈ wmTraceR8,
      (t.storedF.isSome ↔ t.selectionGain.isSome) ∧
      (t.storedF.isSome ↔ t.freeEnergyShape = .controllerMap) ∧
      (t.storedF.isSome ↔ 20260714 ≤ t.fileDate) := by
  native_decide

/-! ## AIF glossary bindings

These declarations transcribe the thirteen theory entries selected by
`glossary-formal-lines.md`.  They do not identify the pre-existing operational
`G` with the glossary's expected-free-energy functional.
-/

structure ProbabilityKernel (S O : Type*) where
  support : S → List O
  mass : S → O → ℝ
  nonnegative : ∀ s o, 0 ≤ mass s o
  normalised : ∀ s, ((support s).map (mass s)).sum = 1

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:23 · P-glossary-mathematics · holder: by-record · evidence: PredictiveOutcomeKernelWitness · falsifier: an unconditional outcome distribution or softmax policy vector is accepted as policy-conditioned `Q(o∣π)` · `Q(o∣π)` is a normalized finite-support predictive distribution over vertex-tagged outcomes for each policy. -/
abbrev PredictiveOutcomeKernel (PolicyIndex : Type*) (Obs : Vertex → Type*) :=
  ProbabilityKernel PolicyIndex (Outcome Obs)

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:33 · P-glossary-mathematics · holder: by-record · evidence: ParameterPriorKernelWitness · falsifier: predictive outcome `Q(o∣π)` or unconditioned policy habit `Q(π)` is accepted as parameter prior `Q(θ∣π)` · `Q(θ∣π)` is the normalized parameter prior predicted by a policy. -/
abbrev ParameterPriorKernel (PolicyIndex Parameter : Type*) :=
  ProbabilityKernel PolicyIndex Parameter

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:33 · P-glossary-mathematics · holder: by-record · evidence: ParameterPosteriorKernelWitness · falsifier: parameter-prior `Q(θ∣π)` or predictive-outcome `Q(o∣π)` is accepted as posterior `Q(θ∣o,π)` · `Q(θ∣o,π)` is the normalized parameter posterior conditioned jointly on the observed outcome and policy. -/
abbrev ParameterPosteriorKernel (PolicyIndex : Type*) (Obs : Vertex → Type*)
    (Parameter : Type*) :=
  ProbabilityKernel (PolicyIndex × Outcome Obs) Parameter

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:7 · P-glossary-mathematics · holder: by-record · evidence: TransitionKernelWitness · falsifier: an action-unconditioned state kernel or the scalar multivariate-beta normalizer `B(α)` is accepted as controlled transition `B` · The controlled state transition `B : S×U ⇝ S`. -/
abbrev TransitionKernel (State Action : Type*) :=
  ProbabilityKernel (State × Action) State

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:41,7 · P-glossary-mathematics · holder: by-record · evidence: PolicyPriorKernelWitness · falsifier: the proposed prior is conditioned on state rather than Unit, or its policy masses are not a distribution · The normalized policy prior `E : 1 ⇝ Π`; its Unit domain prevents contextual likelihoods from masquerading as the prior. -/
abbrev PolicyPriorKernel (PolicyIndex : Type*) :=
  ProbabilityKernel Unit PolicyIndex

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:25 · P-glossary-mathematics · holder: by-record · evidence: PreferenceDistributionWitness · falsifier: a state-conditioned kernel or vertex-local pragmatic cost is accepted as the unconditioned preferred-outcome distribution · Preferred outcomes `C` as a normalized distribution, distinct from the existing vertex-local pragmatic cost function. -/
abbrev PreferenceDistribution (Obs : Vertex → Type*) :=
  ProbabilityKernel Unit (Outcome Obs)

structure NonnegativeReal where
  value : ℝ
  nonnegative : 0 ≤ value

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:7 · P-glossary-mathematics · holder: by-record · evidence: GenerativeModelWitness · falsifier: the proposed joint does not factor as observation × transition × policy prior · A finite generative model shares one hidden-state carrier across observation and transition kernels and includes a normalized policy prior.  The shared type makes a differently wired state space unrepresentable. -/
structure GenerativeModel (Obs : Vertex → Type*) (State Action PolicyIndex : Type*) where
  observation : ProbabilityKernel State (Outcome Obs)
  transition : TransitionKernel State Action
  policyPrior : PolicyPriorKernel PolicyIndex

/-- The one-step joint factor required by the model: observation likelihood ×
controlled transition probability × policy prior. -/
def generativeFactorMass {Obs : Vertex → Type*} {State Action PolicyIndex : Type*}
    (model : GenerativeModel Obs State Action PolicyIndex)
    (state : State) (action : Action) (nextState : State)
    (outcome : Outcome Obs) (policy : PolicyIndex) : ℝ :=
  model.observation.mass nextState outcome *
    model.transition.mass (state, action) nextState *
      model.policyPrior.mass () policy

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:31 · P-glossary-mathematics · holder: by-record · evidence: ObservationKernelWitness · falsifier: a row has negative mass or its declared masses do not sum to one · The observation model is a finite-support Markov kernel A : S ⇝ O; normalisation sums the row's own mass.  This witnesses kernel well-formedness, not semantic observation correctness. -/
abbrev observationKernel (State Observation : Type*) := ProbabilityKernel State Observation

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:9 · P-glossary-mathematics · holder: by-record · evidence: BeliefStateWitness · falsifier: a declared channel lacks its mean or nonnegative variance · Every channel carries both its posterior mean and a nonnegative variance.  This is the carrier claim; observation-responsive change is separately enforced by `beliefUpdate`. -/
structure BeliefState where
  mean : Channel → ℝ
  variance : Channel → NonnegativeReal

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex paragraph:Observation vector o · P-glossary-mathematics · holder: by-record · evidence: ObservationVectorWitness · falsifier: a partial channel map or a single vertex-tagged outcome is accepted as the complete observation vector · A standardized numeric observation has exactly one value at every one of the fourteen declared channel coordinates. Typed absence belongs to the producer measurement envelope and must be resolved before constructing this complete update input. -/
structure ObservationVector where
  value : Channel → ℝ

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:15 · P-glossary-mathematics · holder: by-record · evidence: PredictionErrorWitness · falsifier: prediction error equals either operand or uses the reversed sign · Prediction error is the signed difference ε_k := o_k - μ_k. -/
def predictionError (observation : ObservationVector)
    (beliefMean : Channel → ℝ) : Channel → ℝ :=
  fun k => observation.value k - beliefMean k

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:17 · P-glossary-mathematics · holder: by-record · evidence: PrecisionWitness · falsifier: swapping precision with its signed prediction error preserves variational F, or a signed error map is accepted as precision · Precision is a nonnegative channel-indexed multiplicative weight. -/
abbrev PrecisionMap := Channel → NonnegativeReal

/-- Per-tick precision-weighted prediction error.  This is not expected free
energy and is not the evidence change used by Bayesian model reduction. -/
structure VariationalFreeEnergyValue where
  value : ℝ

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:19 · P-glossary-mathematics · holder: by-record · evidence: VariationalFreeEnergyWitness · falsifier: the Gaussian reference value disagrees, or an expected-free-energy value is accepted as variational F · F = ½ · mean_k (Π_k · ε_k²), over Channel.all. -/
def variationalFreeEnergy (precision error : Channel → ℝ) : VariationalFreeEnergyValue :=
  ⟨(1 / 2 : ℝ) *
    ((Channel.all.map fun k => precision k * (error k) ^ 2).foldl (· + ·) 0 /
      Channel.all.length)⟩

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:31 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · The computed mass of a kernel row; `ProbabilityKernel.normalised` proves it is one. -/
def observationKernelRowMass {State Observation : Type*}
    (A : observationKernel State Observation) (s : State) : ℝ :=
  ((A.support s).map (A.mass s)).sum

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:9,15,17,19,31 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · The posterior applies the precision-weighted prediction-error correction and an evidence-weighted EMA of squared error plus sensor-noise floor. `none` is loud unknown provenance: both mean and variance pass through. Defaults remain external parameters recorded by C32. -/
def beliefUpdate (learningRate sensorNoiseFloor : NonnegativeReal)
    (evidenceWeight : Channel → Option NonnegativeReal)
    (A : observationKernel Channel Channel) (prior : BeliefState)
    (observation : ObservationVector) (precision : PrecisionMap)
    (posterior : BeliefState) : Prop :=
  learningRate.value ≤ 1 ∧
  (∀ k w, evidenceWeight k = some w → w.value ≤ 1) ∧
  (∀ k, posterior.mean k =
    match evidenceWeight k with
    | none => prior.mean k
    | some w => prior.mean k + learningRate.value * w.value *
        observationKernelRowMass A k * (precision k).value *
          predictionError observation prior.mean k) ∧
  (∀ k, (posterior.variance k).value =
    match evidenceWeight k with
    | none => (prior.variance k).value
    | some w =>
        (1 - learningRate.value * w.value) * (prior.variance k).value +
          learningRate.value * w.value *
            ((predictionError observation prior.mean k) ^ 2 + sensorNoiseFloor.value)) ∧
  (variationalFreeEnergy (fun k => (precision k).value)
      (predictionError observation posterior.mean)).value ≤
    (variationalFreeEnergy (fun k => (precision k).value)
      (predictionError observation prior.mean)).value

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:21,27 · P-glossary-mathematics · holder: by-record · evidence: PredictiveOutcomeRiskWitness · falsifier: predictive support contains an outcome with zero preference mass, or the KL value disagrees with the reference · The risk term `KL[Q(o∣π)‖C]`, over the predictive kernel's declared finite
support.  Strict positivity of `C` on that support keeps the real-valued formula
inside its domain; a zero preferred mass would require an extended-real score. -/
def predictiveOutcomeRisk {PolicyIndex : Type*} {Obs : Vertex → Type*}
    (Q : PredictiveOutcomeKernel PolicyIndex Obs) (Cdist : PreferenceDistribution Obs)
    (_positivePreference : ∀ π o, o ∈ Q.support π → 0 < Cdist.mass () o)
    (π : PolicyIndex) : ℝ :=
  (Q.support π).map (fun o => Q.mass π o * Real.log (Q.mass π o / Cdist.mass () o)) |>.sum

/-- Shannon entropy, in nats, of one finite observation-kernel row.  Mathlib's
`Real.log 0 = 0` gives the standard zero-mass convention `0 * log 0 = 0`. -/
def observationEntropy {State Observation : Type*}
    (A : observationKernel State Observation) (s : State) : ℝ :=
  -((A.support s).map (fun o => A.mass s o * Real.log (A.mass s o))).sum

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:21,29 · P-glossary-mathematics · holder: by-record · evidence: AmbiguityWitness · falsifier: expected observation entropy disagrees with the kernel-derived value · Ambiguity is expected observation entropy: the predicted state mass weights the entropy of that state's observation-model row. -/
def ambiguity {PolicyIndex State Observation : Type*}
    (predictedState : ProbabilityKernel PolicyIndex State)
    (A : observationKernel State Observation) (π : PolicyIndex) : ℝ :=
  (predictedState.support π).map
    (fun s => predictedState.mass π s * observationEntropy A s) |>.sum

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:21,27,29 · P-glossary-mathematics · holder: by-record · evidence: ExpectedFreeEnergyWitness · falsifier: the supplied risk-plus-ambiguity value disagrees with the kernel-derived value · Expected free energy is predictive-outcome risk plus expected ambiguity.  The ambiguity argument is an explicit estimator seam; the canonical kernel-derived estimator is `ambiguity` above. -/
def expectedFreeEnergy {PolicyIndex : Type*} {Obs : Vertex → Type*}
    (Q : PredictiveOutcomeKernel PolicyIndex Obs) (Cdist : PreferenceDistribution Obs)
    (positivePreference : ∀ π o, o ∈ Q.support π → 0 < Cdist.mass () o)
    (ambiguity : PolicyIndex → ℝ) : PolicyIndex → ExpectedFreeEnergyValue :=
  fun π => ⟨predictiveOutcomeRisk Q Cdist positivePreference π + ambiguity π⟩

/-- The two decompositions agree exactly under their bridge assumptions: `G`'s
risk is the kernel-derived KL and its epistemic gain is negative ambiguity. -/
theorem G_eq_expectedFreeEnergy {PolicyIndex : Type*} {Obs : Vertex → Type*}
    (risk eig : PolicyIndex → ℝ)
    (Q : PredictiveOutcomeKernel PolicyIndex Obs) (Cdist : PreferenceDistribution Obs)
    (positivePreference : ∀ π o, o ∈ Q.support π → 0 < Cdist.mass () o)
    (ambiguity : PolicyIndex → ℝ)
    (risk_eq : ∀ π, risk π = predictiveOutcomeRisk Q Cdist positivePreference π)
    (ambiguity_eq : ∀ π, ambiguity π = -eig π) :
  ∀ π, G risk eig π = expectedFreeEnergy Q Cdist positivePreference ambiguity π := by
  intro π
  change ExpectedFreeEnergyValue.mk (risk π - eig π) =
    ExpectedFreeEnergyValue.mk (predictiveOutcomeRisk Q Cdist positivePreference π + ambiguity π)
  congr 1
  rw [risk_eq π, ambiguity_eq π]
  ring

/-- Expected information gain is kept distinct from free-energy values and from
the live engineering posterior-spread bonus. -/
structure ExpectedInformationGainValue where
  value : ℝ

/-- The information gained about parameters from one outcome: posterior-to-
prior KL over the posterior kernel's declared support. -/
def parameterInformationGain {PolicyIndex Parameter : Type*} {Obs : Vertex → Type*}
    (prior : ParameterPriorKernel PolicyIndex Parameter)
    (posterior : ParameterPosteriorKernel PolicyIndex Obs Parameter)
    (_positivePrior : ∀ π o θ, θ ∈ posterior.support (π, o) → 0 < prior.mass π θ)
    (π : PolicyIndex) (o : Outcome Obs) : ℝ :=
  (posterior.support (π, o)).map (fun θ =>
    posterior.mass (π, o) θ * Real.log (posterior.mass (π, o) θ / prior.mass π θ)) |>.sum

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:33 · P-glossary-mathematics · holder: by-record · evidence: ExpectedInformationGainWitness · falsifier: posterior-to-prior KL disagrees with recorded EIG · Canonical EIG is the predictive-outcome expectation of posterior-to-prior parameter KL. -/
def expectedInformationGain {PolicyIndex Parameter : Type*} {Obs : Vertex → Type*}
    (Q : PredictiveOutcomeKernel PolicyIndex Obs)
    (prior : ParameterPriorKernel PolicyIndex Parameter)
    (posterior : ParameterPosteriorKernel PolicyIndex Obs Parameter)
    (positivePrior : ∀ π o θ, θ ∈ posterior.support (π, o) → 0 < prior.mass π θ)
    (π : PolicyIndex) : ExpectedInformationGainValue :=
  ⟨(Q.support π).map (fun o =>
      Q.mass π o * parameterInformationGain prior posterior positivePrior π o) |>.sum⟩

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:60 · P-glossary-mathematics · holder: by-record · evidence: DirichletConcentrationsWitness · falsifier: an empty vector or a zero/negative concentration is accepted · A nonempty vector of strictly positive Dirichlet concentration parameters. -/
def DirichletConcentrations := {xs : List ℝ // xs ≠ [] ∧ ∀ x ∈ xs, 0 < x}

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:62 · P-glossary-mathematics · holder: by-record · evidence: LogMultivariateBetaWitness · falsifier: the analytic value disagrees with the Dirichlet normaliser · The logarithm of the Dirichlet normaliser.  Its subtype excludes an empty vector and every zero or negative concentration, where the Dirichlet distribution is not defined. -/
def logMultivariateBeta
    (concentrations : DirichletConcentrations) : ℝ :=
  (concentrations.val.map fun x => Real.log (Real.Gamma x)).sum -
    Real.log (Real.Gamma concentrations.val.sum)

/-- BMR evidence change between a full and reduced Dirichlet model.  The name
and wrapper prevent composition with per-tick variational F by shared `ℝ`. -/
structure ModelReductionFreeEnergyChange where
  value : ℝ

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:62 · P-glossary-mathematics · holder: by-record · evidence: ModelReductionFreeEnergyChangeWitness · falsifier: the analytic Dirichlet-normalizer result is perturbed or per-tick variational F is accepted as BMR ΔF · BMR ΔF = ln B(A) + ln B(a′) - ln B(a) - ln B(A′). -/
def modelReductionFreeEnergyChange
    (A aPrime a APrime : {xs : List ℝ // xs ≠ [] ∧ ∀ x ∈ xs, 0 < x}) :
    ModelReductionFreeEnergyChange :=
  ⟨logMultivariateBeta A + logMultivariateBeta aPrime -
    logMultivariateBeta a - logMultivariateBeta APrime⟩

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:64 · P-glossary-mathematics · holder: by-record · evidence: BayesFactorThresholdWitness · falsifier: a change above -3 passes, or a variational-free-energy value is accepted as BMR evidence · A reduction passes exactly when ΔF ≤ -3. -/
def bayesFactorThreshold (change : ModelReductionFreeEnergyChange) : Prop := change.value ≤ -3

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:35 · P-glossary-mathematics · holder: by-record · evidence: SoftmaxWitness · falsifier: weights fail to normalise or higher expected free energy receives higher probability at positive temperature · Q(π) ∝ exp(ln E(π) − G(π)/τ): both the log habit prior and grade term are retained. -/
def softmax {PolicyIndex : Type*} (exp log : ℝ → ℝ)
    (habit : PolicyIndex → ℝ) (grade : PolicyIndex → ExpectedFreeEnergyValue) (tau : ℝ)
    (policies : List PolicyIndex) : List ℝ :=
  let weights := policies.map fun π => exp (log (habit π) - (grade π).value / tau)
  let total := weights.foldl (· + ·) 0
  weights.map fun weight => weight / total

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:58 · P-glossary-mathematics · holder: by-record · evidence: BayesianModelReductionWitness · falsifier: the reduced posterior fails to preserve the accumulated count vector A-a under the new prior a' · BMR re-expresses the old counts under the reduced prior: A′ = A + a′ - a, componentwise. -/
def bayesianModelReduction (A aPrime a : List ℝ) : List ℝ :=
  (A.zip (aPrime.zip a)).map fun x => x.1 + x.2.1 - x.2.2

/-- The live engineering quantity: a sum of current posterior standard
deviations.  It has no policy, predicted-outcome, or simulated-update input. -/
def modelUncertaintyBonus (posteriorStddevs : List NonnegativeReal) : NonnegativeReal :=
  ⟨(posteriorStddevs.map (·.value)).sum, by
    induction posteriorStddevs with
    | nil => simp
    | cons x xs ih =>
      simpa using add_nonneg x.nonnegative ih⟩

private inductive EIGCounterPolicy where | only
private inductive EIGCounterParameter where | only
private def EIGCounterObs : Vertex → Type := fun _ => Unit
private def eigCounterOutcome : Outcome EIGCounterObs := ⟨.evidence, ()⟩

private def eigCounterPredictive :
    PredictiveOutcomeKernel EIGCounterPolicy EIGCounterObs :=
  { support := fun _ => [eigCounterOutcome]
    mass := fun _ _ => 1
    nonnegative := by intros; norm_num
    normalised := by intros; norm_num }

private def eigCounterPrior :
    ParameterPriorKernel EIGCounterPolicy EIGCounterParameter :=
  { support := fun _ => [.only]
    mass := fun _ _ => 1
    nonnegative := by intros; norm_num
    normalised := by intros; norm_num }

private def eigCounterPosterior :
    ParameterPosteriorKernel EIGCounterPolicy EIGCounterObs EIGCounterParameter :=
  { support := fun _ => [.only]
    mass := fun _ _ => 1
    nonnegative := by intros; norm_num
    normalised := by intros; norm_num }

private theorem eigCounterPositivePrior :
    ∀ π o θ, θ ∈ eigCounterPosterior.support (π, o) →
      0 < eigCounterPrior.mass π θ := by
  intros
  norm_num [eigCounterPrior]

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:33 · P-glossary-mathematics · holder: by-record · evidence: proof term · falsifier: the normalized point-mass counterexample no longer elaborates, or the collapsed equality elaborates · COUNTEREXAMPLE 2026-08-31: the former refusal asked whether the live aggregate posterior-spread bonus equals canonical outcome-weighted posterior-to-prior KL.  In the normalized one-policy/one-outcome/one-parameter model with identical point-mass prior and posterior, canonical EIG is zero, while a positive recorded posterior standard deviation gives live bonus one.  Therefore no unconditional identification exists; promoting the live bonus to canonical EIG is permanently refuted. -/
def modelUncertaintyAndEIG :
    (modelUncertaintyBonus [⟨1, by norm_num⟩]).value ≠
      (expectedInformationGain eigCounterPredictive eigCounterPrior
        eigCounterPosterior eigCounterPositivePrior .only).value := by
  norm_num [modelUncertaintyBonus, expectedInformationGain,
    parameterInformationGain, eigCounterPredictive, eigCounterPrior,
    eigCounterPosterior, eigCounterOutcome]

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:52 · P-glossary-mathematics · holder: by-record · π is the pattern-language cascade scored as one policy; the state-to-action result of inference is `DecisionRule`. -/
abbrev cascadeGrainPi (P : Type*) := Cascade P

/-- CLOSED-BY-RECORD · owner: P-R19-preferences-open §principle · holder: by-record · How a preference layer was determined; open — new constructors are expected (delegate = a company or domain's own harness). -/
inductive PreferenceSource where
  | operatorDeclared | learnedFromOperator | corpusDerived | delegateSupplied | scriptProduced
  deriving DecidableEq

/-- CLOSED-BY-RECORD · owner: P-R19-preferences-open §tetrahedron · holder: by-record · The data half of a layer: what R19-D1 records per stratum. The fixture carries facts; laws derive. `site` is folded-at when folded, enters-at otherwise. -/
structure PreferenceLayerRecord where
  id : String
  source : PreferenceSource
  author : String
  basis : String
  folded : Bool
  site : String
  deriving DecidableEq

/-- CLOSED-BY-RECORD · owner: R19-preference-stack.edn @ dc1dac8 (gated b7cc268) · holder: by-record · The machine as it runs today: five sources, four folded; declared purpose is honestly absent — this stack is what accumulated. -/
def wmPreferenceStack2026_08_30 : List PreferenceLayerRecord :=
  [⟨"floor", .operatorDeclared, "Joseph Corneli", "preferences.clj sha256 22ae618a…", true, "efe.clj:601-614,725-733"⟩,
   ⟨"capability-zone-load", .learnedFromOperator, "wm-outer-loop, implementation Joseph Corneli", "substrate-2 2026-08-30: 242 records, 14 classes, max as-of 2026-07-18", true, "efe.clj:586-614"⟩,
   ⟨"live-goal-outcomes", .corpusDerived, "futon2.aif.c-vector/entries-from-corpus", "substrate-2 :7071 2026-08-30: signature -1131096431, 36 capabilities, 293 sorries", true, "efe.clj:655-665,725-733"⟩,
   ⟨"c-vector-overlays", .scriptProduced, "futon6/scripts/c_vector.bb", "2026-06-26 overlay snapshots (three sha256 pins in the record)", true, "c_vector.clj:227-240,633-640"⟩,
   ⟨"habit-prior", .learnedFromOperator, "unknown operator whose selections are recorded in wm-trace", "wm-trace-2026-08-30.edn sha256 6da3ccda…", false, "policy/select-action ln E(π) seam (since 2026-07-13 flip): computed and recorded with declared :counterfactual-only authority — orders the counterfactual, does not choose (policy.clj:234-270); R14 supplies τ beside it"⟩]

/-- CLOSED-BY-RECORD · owner: R19-preference-stack.edn @ dc1dac8 · holder: by-record · No declaration naming the situation this stack models exists; the observed purpose is the fold's own behaviour. -/
def wmStackDeclaredPurpose : Option String := none

/-- CLOSED-BY-RECORD · owner: P-R19-preferences-open §gate · holder: by-record · Every recorded layer names a non-empty author and basis — decided against the fixture, kernel `decide`. -/
theorem preferenceStackRecorded :
    (wmPreferenceStack2026_08_30.all fun l => l.author != "" && l.basis != "") = true := by decide

/-- CLOSED-BY-RECORD · owner: P-R19-preferences-open §principle · holder: by-record · The semantic layer: a preference with provenance and its own composition rule. `prefers` is ln P(o) up to a constant on this layer alone. -/
structure PreferenceLayer (Outcome : Type*) where
  record : PreferenceLayerRecord
  prefers : Outcome → ℝ
  compose : ℝ → ℝ → ℝ

/-- CLOSED-BY-RECORD · owner: P-R19-preferences-open §principle · holder: by-record · C for one deployment is the fold of an ordered layer stack; the machine never holds a C of its own. The habit prior connects to `softmax`'s `habit` argument — no new name. -/
def foldC {Outcome : Type*} (base : Outcome → ℝ)
    (layers : List (PreferenceLayer Outcome)) : Outcome → ℝ :=
  layers.foldl (fun acc l o => l.compose (acc o) (l.prefers o)) base

/-- CLOSED-BY-RECORD · owner: P-R19-preferences-open §tetrahedron · holder: by-record · A stack is admissible only with its purpose stated at the strata level, evidence of fit, a falsifier, and a holder — the R19 tetrahedron's organisation and mass. -/
structure PreferenceStack (Outcome : Type*) where
  layers : List (PreferenceLayer Outcome)
  purpose : String
  evidence : List String
  falsifier : String
  holder : String

inductive PreferenceSpineDeclaration where
  | vertexLocalC
  | gradeG
  | recordedSnatchRisk
  | preferenceDistribution
  | predictiveOutcomeRisk
  | expectedFreeEnergy
  | softmaxHabit
  | preferenceLayerPrefers
  | foldC
  deriving DecidableEq, Repr

structure PreferenceConstantCensusRow where
  declaration : PreferenceSpineDeclaration
  preferenceInput : Bool
  freeConstant : Bool
  reason : String
  deriving DecidableEq, Repr

/-- CLOSED-BY-RECORD · owner: P-R19-preferences-open §principle · holder: by-record · The in-language census of the spine's complete named preference surface. `preferenceInput` says the declaration receives its preference-bearing value or layers from the caller. `freeConstant` says it instead supplies a preference function/table from its own global definition. -/
def preferenceConstantCensus : List PreferenceConstantCensusRow :=
  [⟨.vertexLocalC, false, true,
      "C returns Obs v -> Real without a preference distribution, base, or layer input"⟩,
   ⟨.gradeG, true, false, "risk and epistemic grade are parameters"⟩,
   ⟨.recordedSnatchRisk, false, false,
      "a pinned ablation fixture table, not a deployment preference C"⟩,
   ⟨.preferenceDistribution, true, false, "a carrier type, not a value"⟩,
   ⟨.predictiveOutcomeRisk, true, false, "preference distribution Cdist is a parameter"⟩,
   ⟨.expectedFreeEnergy, true, false, "preference distribution Cdist is a parameter"⟩,
   ⟨.softmaxHabit, true, false, "habit prior is a parameter"⟩,
   ⟨.preferenceLayerPrefers, true, false, "prefers is supplied as structure data"⟩,
   ⟨.foldC, true, false, "base preference and ordered layers are parameters"⟩]

def freePreferenceConstants : List PreferenceSpineDeclaration :=
  (preferenceConstantCensus.filter (·.freeConstant)).map (·.declaration)

/-- The census has exactly one free preference constant: the vertex-local `C`. -/
theorem freePreferenceConstants_eq :
    freePreferenceConstants = [.vertexLocalC] := by decide

/-- PERMANENT EXTERNAL ATTESTATION · Lean cannot prove an event · evidence is the executable witness · contract kind HOLE intentionally · owner: P-R19-preferences-open §gate · holder: by-record · evidence: `checks/preference_stack_binding_check.clj` over `holes/labs/wm-contract/PreferenceStackWitness.edn` · falsifier: a C value in a live trace with no layer record behind it · Every running instance's C is the fold of a recorded stack. C114 considered and declined narrowing: a theorem over one pinned witness would prove a pinned instance, not the existing world-level claim. -/
def preferenceStackLiveRecorded : Prop := sorry

/-- CLOSED-BY-RECORD · owner: P-R19-preferences-open §principle · holder: by-record · COUNTEREXAMPLE 2026-08-31: the original `machineHasNoC` claim said C is a parameter everywhere.  The in-language census refutes it: global `C` returns `Obs v → ℝ` without receiving a preference distribution, base preference, or layer stack, while every other deployment preference surface is parameterized.  The historical name remains legible; the proposition now records the refutation that the free-constant census is non-empty. -/
def machineHasNoC : freePreferenceConstants ≠ [] := by
  rw [freePreferenceConstants_eq]
  decide

/-- CLOSED-BY-RECORD · owner: record: futon2:holes/problems/BUILD-packets/WM-RUN1.md · Joe 2026-08-31 · runs-once receipt · holder: by-record · What one completed tick leaves behind: the receipt is the evidence, and each field is one of the standing invariants made concrete for a single run. On-demand ticks (run one, like the APM machine's clicks) are first-class; a scheduler is one caller among others. -/
structure TickRunRecord where
  runId : String            -- generated at tick start; stable across receipt reserialisation
  startedAt : String
  storeBasisCount : Nat     -- I_data_current: the STORE's count at tick time (the pin)
  storeBasisMaxAt : String
  entriesRead : Nat         -- the sample the tick actually consumed (limit-capped fetch)
  entriesLimit : Nat        -- the cap under which entriesRead was taken — the unit of the sample
  inputsRead : Nat          -- I_absent_is_loud: input-status travelled
  inputIssues : Nat
  preferenceLayers : Nat    -- the C stack was named (R19)
  traceWritten : Bool       -- the emission has a consumer path (I_evidence_consumed)
  selectorSeam : String     -- "live" or the declared stub — never silent
  deriving DecidableEq

/-- PERMANENT EXTERNAL ATTESTATION · Lean cannot prove an event · evidence is the executable witness · contract kind HOLE intentionally · owner: record: futon2:holes/problems/BUILD-packets/WM-RUN1.md · Joe 2026-08-31 · holder: by-record · evidence: `checks/wm_runs_once_witness.clj` over `holes/labs/wm-contract/tick-run-record-2026-08-30.edn` · falsifier: no invocation of the tick entry point completes end-to-end with a TickRunRecord · OWNER AMENDMENT 2026-08-31: the original annotation said "CURRENTLY FIRING: selector-seam blocker". That was true of the earlier diagnostic standalone report, but a nine-hop tick subsequently completed through the explicitly recorded bounded stub. Futon3c remains absent from Futon2's local classpath; the production operator loop instead uses the live Agency HTTP selector. Original claim retained here as history, not current state. · The machine can run at least once on demand, leaving a receipt. C114 considered and declined narrowing: a theorem over the receipt would prove a pinned instance, not that the world-level event occurred. -/
def wmRunsOnce : Prop := sorry

/-- CLOSED-BY-RECORD · owner: record: futon2:holes/problems/BUILD-packets/WM-RUN2.md · Joe 2026-08-31 · route tracer · holder: by-record · One hop of the route a tick actually took: the tracer tag conj'd onto the flowing map at a node boundary, reassembled pairwise into hops. The wiring diagram (control-map-edges.edn, Figure 4 as data) is the specification the route is judged against. -/
structure RouteHop where
  fromNode : String
  toNode : String
  via : String        -- the function at the boundary
  at_ : String
  deriving DecidableEq

/-- OPEN, RUN-GATED · the close path is a Lean certificate per accepted run · contract kind HOLE, until a certificate is accepted · owner: record: futon2:holes/problems/BUILD-packets/WM-RUN2.md · Joe 2026-08-31 · holder: by-record · evidence: `checks/wm_route_conformance.clj` over `holes/labs/wm-contract/tick-run-record-2026-08-30.edn` and the live Figure 4 edge layers; and, since 2026-09-04, `wmS5RunConformsToDrawnWiring` over the pinned 2026-09-01-s5 run · falsifier: an empty route or any hop absent from both the original and measured figure layers · A completed tick's reassembled route is non-empty and every hop is an edge of the wiring specification. CLOSE PATH (Joe's RUN4 ruling, 2026-09-03, futon2 worklist.edn `:run4-lean-ruling`; executed by `:U49`). The PERMANENT EXTERNAL ATTESTATION reading this annotation used to carry is REFUSED BY ITS OWNER, verbatim: "I'm not sure I believe that wmRunConformsToWiring cannot be attested to... all that's really needed here is to run the machine and see if it conforms to the wiring that we drew. And that should be something we can validate in Lean. So I don't see this as a permanent hole at all... It might be the last one we fill. But it's not permanent." C114's decline of the pinned transcription is SUPERSEDED by that ruling: a Lean certificate over a pinned run -- the reassembled route against the drawn Figure 4 layers, proved by `decide`, the `wmTraceR2`/`wmTraceR8` pattern applied per run -- is exactly the wanted validation, and it is leg (3) of the J9 criterion. So this is RUN-GATED, not permanent: the machinery exists and is exercised (`wmS5RunConformsToDrawnWiring`, with `wmS5RouteCensus` deciding its numbers), and the hole closes when Joe ACCEPTS a certificate over a qualifying run -- which run qualifies is his call at certificate time, and the flip-era run may be what he means. Nothing here is closed by the s5 certificate alone; `mkHole` stays until that acceptance. -/
def wmRunConformsToWiring : Prop := sorry

/-! ### The 2026-09-01-s5 run's route against the drawn wiring (worklist `:U49`)

Joe's RUN4 ruling (2026-09-03) refuses the permanent-attestation reading of
`wmRunConformsToWiring`: what is wanted is to run the machine and validate in
Lean that the run conforms to the wiring that was drawn. This block is the
transcription that makes the validation decidable -- the drawn map as data and
one pinned run's reassembled route -- and
`wmS5RunConformsToDrawnWiring` below is the certificate over it.

SOURCES, both pinned:
* `p4ng:empirics-futon/control-map-edges.edn`, `:as-of` 2026-08-30, commit `e508ece`,
  sha256 `161d0abffd21551078ac2d7a87427e6cacafbfca0695c09a496260be21fafdec`
  -- 22 `:edges`, 8 `:route-measured-drawn`, 8 retired pairs.
* `futon2:holes/labs/wm-contract/runs/2026-09-01-s5`, the run at futon2 sha `5a66411` --
  4 records selected by `:run/id` (RUN11), extracted trace sha256
  `c3480955286e548be6fd4bbde80e5081446cfaaac1500294e2de1fa44e2d7c67`.

GENERATED from those two files by
`futon2:holes/labs/wm-contract/u49_route_transcribe.bb`; edit the sources and
regenerate rather than editing the literals.
-/

/-- The nodes of the drawn control map (`control-map-edges.edn :nodes`), plus
`TRACE`, the sink the route's last hop reaches. Constructor names are the
recorded ids verbatim. -/
inductive RouteNode where
  | R1
  | R2
  | R3
  | R3a
  | R4
  | R5
  | R6
  | R7
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
  | R16
  | R17
  | R20
  | TRACE
  deriving DecidableEq, Repr

/-- A hop, and equally an edge of the figure: an ordered pair of nodes. The
route a tick records is a SEQUENCE of node tags, so a hop is a consecutive
pair (`run3_conformance.bb:113-114`). -/
abbrev WiringEdge := RouteNode × RouteNode

/-- The grounds on which a drawn edge was retired by a `:decisions` entry of
the control map. `code` retirements are claims about the code; `ruling`
retirements are Joe's. A pair may carry both, from different decisions. -/
inductive RetirementGrounds where
  | code
  | ruling
  deriving DecidableEq, Repr

/-- A retired pair with the SET of grounds it was retired on -- the shape
`run3_conformance.bb:57-61` reduces `:decisions` to. -/
structure RetiredWiringEdge where
  edge : WiringEdge
  grounds : List RetirementGrounds
  deriving DecidableEq, Repr

/-- Every pair in the map's `:edges`, in file order. NOTE, and it is a real
difference between the two checkers rather than an oversight: `:status` is NOT
filtered here, because `run3_conformance.bb:55` does not filter it and run3 is
what produced this run's pinned verdict. So the one `:unresolved` self-loop
`R5 -> R5` is in this list, where `checks/wm_route_conformance.clj:28` would
drop it. It is not traversed by this run, so nothing here turns on it. -/
def figureDrawnEdges : List WiringEdge :=
  [(.R1, .R4),
   (.R2, .R3),
   (.R3, .R1),
   (.R4, .R5),
   (.R5, .R6),
   (.R6, .R13),
   (.R11, .R16),
   (.R13, .R14),
   (.R14, .R16),
   (.R16, .R2),
   (.R5, .R5),
   (.R6, .R11),
   (.R7, .R3),
   (.R7, .R8),
   (.R7, .R14),
   (.R8, .R5),
   (.R9, .R16),
   (.R10, .R8),
   (.R12, .R7),
   (.R15, .R13),
   (.R15, .R16),
   (.R20, .R7)]

/-- The `:route-measured-drawn` layer: edges added to Figure 4 because a route
measurement found them. Conformance against this layer is weaker than
conformance against `figureDrawnEdges` and the certificate's docstring says so. -/
def figureMeasuredEdges : List WiringEdge :=
  [(.R20, .R12),
   (.R12, .R2),
   (.R2, .R7),
   (.R2, .R3a),
   (.R3a, .R7),
   (.R3, .R8),
   (.R6, .R14),
   (.R14, .TRACE)]

/-- The retired pairs and their grounds. -/
def figureRetiredEdges : List RetiredWiringEdge :=
  [{ edge := (.R11, .R16), grounds := [.ruling] },
   { edge := (.R13, .R14), grounds := [.code] },
   { edge := (.R14, .R16), grounds := [.code] },
   { edge := (.R2, .R3), grounds := [.code] },
   { edge := (.R2, .R7), grounds := [.code] },
   { edge := (.R5, .R6), grounds := [.ruling] },
   { edge := (.R6, .R13), grounds := [.code, .ruling] },
   { edge := (.R7, .R14), grounds := [.code] }]

/-- Decidable membership without a `BEq` detour. -/
def edgeMem (e : WiringEdge) (es : List WiringEdge) : Bool :=
  es.any (fun x => decide (x = e))

/-- The grounds recorded against a pair; `[]` when it was never retired. -/
def retirementGroundsOf (e : WiringEdge) : List RetirementGrounds :=
  match figureRetiredEdges.find? (fun r => decide (r.edge = e)) with
  | some r => r.grounds
  | none => []

/-- How run3 dispositions one hop. -/
inductive HopClass where
  | refutation
  | rulingUnrealised
  | excludedDependencyGrain
  | drawn
  | routeMeasured
  | unmapped
  deriving DecidableEq, Repr

/-- `run3_conformance.bb:116-124`, transcribed clause for clause. The order
matters and is the script's: a `code` retirement whose pair is ALSO on the
measured layer retired a dependency claim while the route stayed drawn as
measured, so it is excluded rather than a refutation. -/
def classifyHop (e : WiringEdge) : HopClass :=
  let g := retirementGroundsOf e
  let hasCode := g.any (fun x => decide (x = RetirementGrounds.code))
  let hasRuling := g.any (fun x => decide (x = RetirementGrounds.ruling))
  if hasCode && edgeMem e figureMeasuredEdges then .excludedDependencyGrain
  else if hasCode then .refutation
  else if hasRuling then .rulingUnrealised
  else if edgeMem e figureDrawnEdges then .drawn
  else if edgeMem e figureMeasuredEdges then .routeMeasured
  else .unmapped

/-- A recorded route reassembled into hops: the consecutive pairs. Written
with `zip` rather than by recursion so that `decide` reduces it in the kernel
without going through the equation compiler's `brecOn`. -/
def routeHops (r : List RouteNode) : List WiringEdge := r.zip r.tail

/-- THE CONFORMANCE VERDICT, as run3 states it and stripped of nothing:
the run recorded at least one route, no route is empty, no hop is unmapped,
and no hop is a refutation (a code-retired pair traversed at route grain).
The two retired classes run3 does NOT count against a run --
`excludedDependencyGrain` and `rulingUnrealised` -- are absent here for the
same reason they are absent there, and this run hits both, so a flat "no
retired edge traversed" would report it not conformant.

`reducible` because `decide` needs the `Decidable` instance for THIS
conjunction, and instance synthesis does not unfold an irreducible `def`. -/
@[reducible] def runConformsToDrawnWiring (routes : List (List RouteNode)) : Prop :=
  routes ≠ [] ∧
    (∀ r ∈ routes, r ≠ []) ∧
    (∀ h ∈ routes.flatMap routeHops, classifyHop h ≠ HopClass.unmapped) ∧
    (∀ h ∈ routes.flatMap routeHops, classifyHop h ≠ HopClass.refutation)

/-- The 4 routes the run recorded, in the order `:run/id` selection
returns them out of the shared trace:
`4e35e740-8c9f-42c1-b8a9-0cdfc024e9c8`,
`c51a8da3-883e-4038-b493-1b268d5d8357`,
`b69ec193-5aa0-45ca-9cbb-9df45cbb8d82`,
`28da19d2-3a03-40f6-8eef-2818fe5583a9`. -/
def s5Routes : List (List RouteNode) :=
  [[.R20, .R12, .R2, .R7, .R3, .R8, .R5, .R6, .R14, .TRACE],
   [.R20, .R12, .R2, .R7, .R3, .R8, .R5, .R6, .R14, .TRACE],
   [.R20, .R12, .R2, .R7, .R3, .R8, .R5, .R6, .R14, .TRACE],
   [.R20, .R12, .R2, .R7, .R3, .R8, .R5, .R6, .R14, .TRACE]]

/-- The run's 36 hops, 9 of them distinct. -/
def s5Hops : List WiringEdge := s5Routes.flatMap routeHops

/-- The drawn edges this run never traversed. -/
def s5UnfiredDrawnEdges : List WiringEdge :=
  figureDrawnEdges.filter (fun e => !edgeMem e s5Hops)

/-- CLOSED UNDER THE J9 CRITERION · leg (3) · THE RUN-CONFORMANCE CERTIFICATE
for the run `runs/2026-09-01-s5` (futon2 sha `5a66411`),
worklist `:U49` under Joe's RUN4 ruling of 2026-09-03. Every one of the 36
hops the run recorded is an edge of the drawn wiring on run3's own
classification, no route is empty, and no code-retired pair was traversed at
route grain. Proved by `decide` over the transcribed tables, no `sorry` and no
`native_decide` -- the `wmTraceR2`/`wmTraceR8` precedent. The Clojure side of
the same comparison is `futon2:holes/labs/wm-contract/run3_conformance.bb`,
whose pinned verdict for this run is
`runs/2026-09-01-s5/conformance.edn` `:verdict :conformant`; the mutations that
break this proposition are listed at `runs/U49-run-conformance/04-controls.edn`
control C4.

WHAT IT DOES NOT SHOW, because a reader will otherwise take it for more: 5 of
the 9 distinct hops are on the `:route-measured-drawn` layer, which is the
layer a previous route MEASUREMENT put on the figure, so for those the run is
being compared against a record of a run; and 19 of the 22 drawn edges never
fired at all. The certificate says this run stayed inside the union of the two
layers. It does not say the drawn figure predicted the run. -/
theorem wmS5RunConformsToDrawnWiring : runConformsToDrawnWiring s5Routes := by
  decide

/-- The census the certificate is stated over, so the numbers a reader checks
against `runs/2026-09-01-s5/conformance.edn` are themselves decided rather than
asserted in prose: 4 routes, 36 hops, 9 distinct, and the class split
-- 2 drawn, 5 route-measured, 1 excluded at dependency grain, 1 ruling-unrealised,
0 refutations, 0 unmapped -- with 19 of 22 drawn edges unfired. -/
theorem wmS5RouteCensus :
    s5Routes.length = 4 ∧
      s5Hops.length = 36 ∧
      s5Hops.dedup.length = 9 ∧
      (s5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.drawn))).length = 2 ∧
      (s5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.routeMeasured))).length = 5 ∧
      (s5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.excludedDependencyGrain))).length = 1 ∧
      (s5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.rulingUnrealised))).length = 1 ∧
      (s5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.refutation))).length = 0 ∧
      (s5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.unmapped))).length = 0 ∧
      figureDrawnEdges.length = 22 ∧
      s5UnfiredDrawnEdges.length = 19 := by
  decide

/-! ### The 2026-09-04-re5 run's route against the drawn wiring (worklist `:RE5`)

The SECOND run certified against the drawn wiring, under Joe's RUN4 ruling.
The transcription's shared definitions -- `RouteNode`, `WiringEdge`,
`figureDrawnEdges`, `figureRouteMeasured`, `figureRetired`, `classifyHop`,
`routeHops`, `runConformsToDrawnWiring` -- are the ones the `:U49` block
above defines, and are NOT redefined here. They are a function of the drawn
map alone, so reusing them is a claim that the map has not moved since that
block was generated; the producer checks it (control C7) rather than
assuming it.

SOURCES, both pinned:
* `p4ng:empirics-futon/control-map-edges.edn`, `:as-of` 2026-08-30, commit `e508ece`,
  sha256 `161d0abffd21551078ac2d7a87427e6cacafbfca0695c09a496260be21fafdec`
  -- 22 `:edges`, 8 `:route-measured-drawn`, 8 retired pairs.
* `futon2:holes/labs/wm-contract/runs/2026-09-04-re5`, the run at futon2 sha `e0552943` --
  4 records selected by `:run/id` (RUN11), extracted trace sha256
  `f343432d772986ddc2f7fe38107913afc997201ebae9b6240dff152e235b1120`.

GENERATED from those two files by
`futon2:holes/labs/wm-contract/u49_route_transcribe.bb`; edit the sources and
regenerate rather than editing the literals.
-/

/-- The 4 routes the run recorded, in the order `:run/id` selection
returns them out of the shared trace:
`8ae111bc-d758-45f3-9c5b-f98832e10bb6`,
`308d1622-55ca-4671-aab7-273731d3c99e`,
`67c72ac3-5d8b-4ffd-8732-650864d18182`,
`c149f9de-669c-4817-9b0e-ed4aad77db79`. -/
def re5Routes : List (List RouteNode) :=
  [[.R20, .R12, .R2, .R7, .R3, .R8, .R5, .R6, .R14, .TRACE],
   [.R20, .R12, .R2, .R7, .R3, .R8, .R5, .R6, .R14, .TRACE],
   [.R20, .R12, .R2, .R7, .R3, .R8, .R5, .R6, .R14, .TRACE],
   [.R20, .R12, .R2, .R7, .R3, .R8, .R5, .R6, .R14, .TRACE]]

/-- The run's 36 hops, 9 of them distinct. -/
def re5Hops : List WiringEdge := re5Routes.flatMap routeHops

/-- The drawn edges this run never traversed. -/
def re5UnfiredDrawnEdges : List WiringEdge :=
  figureDrawnEdges.filter (fun e => !edgeMem e re5Hops)

/-- CLOSED UNDER THE J9 CRITERION · leg (3) · THE RUN-CONFORMANCE CERTIFICATE
for the run `runs/2026-09-04-re5` (futon2 sha `e0552943`),
worklist `:RE5` under Joe's RUN4 ruling of 2026-09-03. Every one of the 36
hops the run recorded is an edge of the drawn wiring on run3's own
classification, no route is empty, and no code-retired pair was traversed at
route grain. Proved by `decide` over the transcribed tables, no `sorry` and no
`native_decide` -- the `wmTraceR2`/`wmTraceR8` precedent. The Clojure side of
the same comparison is `futon2:holes/labs/wm-contract/run3_conformance.bb`,
whose pinned verdict for this run is
`runs/2026-09-04-re5/conformance.edn` `:verdict :conformant`; the mutations that
break this proposition are listed at `runs/RE5-run-conformance/04-controls.edn`
control C4.

WHAT IT DOES NOT SHOW, because a reader will otherwise take it for more: 5 of
the 9 distinct hops are on the `:route-measured-drawn` layer, which is the
layer a previous route MEASUREMENT put on the figure, so for those the run is
being compared against a record of a run; and 19 of the 22 drawn edges never
fired at all. The certificate says this run stayed inside the union of the two
layers. It does not say the drawn figure predicted the run. -/
theorem wmRe5RunConformsToDrawnWiring : runConformsToDrawnWiring re5Routes := by
  decide

/-- The census the certificate is stated over, so the numbers a reader checks
against `runs/2026-09-04-re5/conformance.edn` are themselves decided rather than
asserted in prose: 4 routes, 36 hops, 9 distinct, and the class split
-- 2 drawn, 5 route-measured, 1 excluded at dependency grain, 1 ruling-unrealised,
0 refutations, 0 unmapped -- with 19 of 22 drawn edges unfired. -/
theorem wmRe5RouteCensus :
    re5Routes.length = 4 ∧
      re5Hops.length = 36 ∧
      re5Hops.dedup.length = 9 ∧
      (re5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.drawn))).length = 2 ∧
      (re5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.routeMeasured))).length = 5 ∧
      (re5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.excludedDependencyGrain))).length = 1 ∧
      (re5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.rulingUnrealised))).length = 1 ∧
      (re5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.refutation))).length = 0 ∧
      (re5Hops.dedup.filter (fun h => decide (classifyHop h = HopClass.unmapped))).length = 0 ∧
      figureDrawnEdges.length = 22 ∧
      re5UnfiredDrawnEdges.length = 19 := by
  decide

/-! ### The 2026-09-01-s5 run's selection discrimination (worklist `:RE7`)

Joe's ruling of 2026-09-04 (worklist `:U51`/`:U52`): "the Lean model is
supposed to help by validating logged info. A 55-way tie should be seen as an
obvious defect." This block is the transcription that makes that decidable --
each recorded decision's controller-score tie as data, and the check's verdict
as a proposition about it.

SOURCES, both pinned and both committed:
* `futon2:holes/labs/wm-contract/runs/RE4-rationale-logging/store` -- 4 rationale records
  for run `2026-09-01-s5`; the tie of each `chosenRank`/`tieCount`/`tieBand` field is
  read from these.
* `futon2:holes/labs/wm-contract/runs/2026-09-01-s5/wm-trace-s5.edn` -- the run store's own
  trace extraction; `fieldSize` and `widestPlateauNotChosen` are recomputed from it.

GENERATED from those files by
`futon2:holes/labs/wm-contract/re7_selection_discrimination.bb`; edit the
sources and regenerate rather than editing the literals.
-/

/-- One recorded decision's controller-score tie, transcribed from the run's
rationale record (`:rationale/chosen :controller-score-tie`, written at decision
time by `futon2:src/futon2/aif/selection_rationale.clj:139-153`) together with
the plateau census recomputed from the run store's own committed trace -- which
is not always the file the record names; each run block's SOURCES says which
file its census was computed from. Ranks are 1-based positions in the
controller ranking. -/
structure SelectionTie where
  /-- The tick's `:rationale/tick-id`, verbatim. -/
  tick : String
  /-- The chosen candidate's controller rank. -/
  chosenRank : Nat
  /-- How many candidates share the chosen candidate's controller score. -/
  tieCount : Nat
  /-- The lowest rank of that tie. -/
  tieBandLo : Nat
  /-- The highest rank of that tie. -/
  tieBandHi : Nat
  /-- Candidates scored on this tick. -/
  fieldSize : Nat
  /-- CENSUS, NOT VERDICT: the widest plateau of the field that does NOT hold
  the chosen candidate. -/
  widestPlateauNotChosen : Nat
  deriving DecidableEq, Repr

/-- DERIVED: the choice was made by the sort's tie-break rather than by the
score, i.e. the chosen candidate's score has no unique argmin. 1 is not a
threshold anyone picked: it is the width at which a score decides. -/
def SelectionTie.chosenByTiebreak (t : SelectionTie) : Bool := decide (1 < t.tieCount)

/-- The property `:selection-discrimination` verdicts on: the run recorded at
least one decision, and no decision's choice was a tie-break. Note what is NOT
here -- `widestPlateauNotChosen` is carried by the data and read by no
conjunct, because a plateau the choice is not in is a census and not a defect.

`reducible` because `decide` needs the `Decidable` instance for THIS
conjunction, and instance synthesis does not unfold an irreducible `def` (the
`runConformsToDrawnWiring` precedent). -/
@[reducible] def selectionDiscriminates (ts : List SelectionTie) : Prop :=
  0 < ts.length ∧ ts.all (fun t => !t.chosenByTiebreak) = true

/-- The 4 decisions run `2026-09-01-s5` recorded, ordered by tick. -/
def s5SelectionTies : List SelectionTie :=
  [{ tick := "2026-09-01T22:50:42.709079837Z", chosenRank := 123, tieCount := 55, tieBandLo := 73, tieBandHi := 127, fieldSize := 145, widestPlateauNotChosen := 6 },
   { tick := "2026-09-01T22:52:07.418144767Z", chosenRank := 115, tieCount := 55, tieBandLo := 73, tieBandHi := 127, fieldSize := 145, widestPlateauNotChosen := 6 },
   { tick := "2026-09-01T22:53:32.871991661Z", chosenRank := 123, tieCount := 55, tieBandLo := 73, tieBandHi := 127, fieldSize := 145, widestPlateauNotChosen := 6 },
   { tick := "2026-09-01T22:54:48.942309598Z", chosenRank := 115, tieCount := 55, tieBandLo := 73, tieBandHi := 127, fieldSize := 145, widestPlateauNotChosen := 6 }]

/-- THE `:selection-discrimination` VERDICT for run `2026-09-01-s5`, decided.
4 of the 4 recorded decisions chose a candidate from inside a tie
of up to 55 candidates sharing one controller score to sixteen digits -- so the
score ranked a plateau and the sort's tie-break picked the member. The chosen
rank runs as deep as 123 in a field of 145, which a reader would otherwise take
for a large score gap.

This is the defect Joe's ruling names. The negation is stated rather than a
positive `chosenByTiebreak` conjunct because it is the SAME proposition the
green run satisfies, so the two certificates are comparable.

Proved by `decide` over the transcribed data, no `sorry` and no `native_decide`
-- the `wmS5RunConformsToDrawnWiring` precedent. The Clojure side of the same
comparison is `futon2:holes/labs/wm-contract/re7_selection_discrimination.bb`,
whose verdict for this run is `:defect`; the plants that move it are in
`runs/RE7-selection-discrimination/2026-09-01-s5/03-controls.edn`, controls C2-C6. -/
theorem wmS5SelectionDiscrimination :
    ¬ selectionDiscriminates s5SelectionTies := by
  decide

/-- The census the verdict is stated over, so the numbers a reader checks
against `runs/RE7-selection-discrimination/2026-09-01-s5/01-decisions.edn`
are themselves decided rather than asserted in prose: 4 decisions, 4 of them
chosen by tie-break, widest chosen tie 55, deepest chosen rank 123, field size
145, and the widest plateau NOT holding the choice 6. -/
theorem wmS5SelectionTieCensus :
    s5SelectionTies.length = 4 ∧
      (s5SelectionTies.filter (fun t => t.chosenByTiebreak)).length = 4 ∧
      (s5SelectionTies.map (fun t => t.tieCount)).foldl max 0 = 55 ∧
      (s5SelectionTies.map (fun t => t.chosenRank)).foldl max 0 = 123 ∧
      (s5SelectionTies.map (fun t => t.fieldSize)).foldl max 0 = 145 ∧
      (s5SelectionTies.map (fun t => t.widestPlateauNotChosen)).foldl max 0 = 6 := by
  decide

/-! ### The 2026-09-04-re5 run's selection discrimination (worklist `:RE7`)

Joe's ruling of 2026-09-04 (worklist `:U51`/`:U52`): "the Lean model is
supposed to help by validating logged info. A 55-way tie should be seen as an
obvious defect." This block is the transcription that makes that decidable --
each recorded decision's controller-score tie as data, and the check's verdict
as a proposition about it.

The shared definitions -- `SelectionTie`, `SelectionTie.chosenByTiebreak`,
`selectionDiscriminates` -- are the ones the first `:RE7` block above defines
and are NOT redefined here. They are a function of the producer alone, so
reusing them is a claim that the producer has not moved since that block was
generated; control C9 checks it rather than assuming it.

SOURCES, both pinned and both committed:
* `futon2:holes/labs/wm-contract/runs/2026-09-04-re5/rationale` -- 4 rationale records
  for run `2026-09-04-re5`; the tie of each `chosenRank`/`tieCount`/`tieBand` field is
  read from these.
* `futon2:holes/labs/wm-contract/runs/2026-09-04-re5/wm-trace-re5.edn` -- the run store's own
  trace extraction; `fieldSize` and `widestPlateauNotChosen` are recomputed from it.
  NOT the file the records' `:rationale/trace-path` names, which is
  ["/home/joe/code/futon2/data/wm-trace/wm-trace-2026-09-04.edn"] -- the live, untracked
  corpus the tick wrote as it ran, which no reviewer and no other machine can
  read. Control C1 requires this committed file to reproduce every recorded
  tie, so the substitution is checked rather than assumed.

GENERATED from those files by
`futon2:holes/labs/wm-contract/re7_selection_discrimination.bb`; edit the
sources and regenerate rather than editing the literals.
-/

/-- The 4 decisions run `2026-09-04-re5` recorded, ordered by tick. -/
def re5SelectionTies : List SelectionTie :=
  [{ tick := "2026-09-04T07:46:52.742121237Z", chosenRank := 1, tieCount := 1, tieBandLo := 1, tieBandHi := 1, fieldSize := 146, widestPlateauNotChosen := 56 },
   { tick := "2026-09-04T07:48:10.260151161Z", chosenRank := 1, tieCount := 1, tieBandLo := 1, tieBandHi := 1, fieldSize := 146, widestPlateauNotChosen := 56 },
   { tick := "2026-09-04T07:49:29.060729571Z", chosenRank := 1, tieCount := 1, tieBandLo := 1, tieBandHi := 1, fieldSize := 146, widestPlateauNotChosen := 56 },
   { tick := "2026-09-04T07:50:47.952039102Z", chosenRank := 1, tieCount := 1, tieBandLo := 1, tieBandHi := 1, fieldSize := 146, widestPlateauNotChosen := 56 }]

/-- THE `:selection-discrimination` VERDICT for run `2026-09-04-re5`, decided.
Every one of the 4 recorded decisions chose a candidate whose
controller score no other candidate shared, so no choice was made by the sort's
tie-break.

WHAT IT DOES NOT SHOW, because a reader will otherwise take it for more: the
score field of these ticks still carries a plateau 56 candidates wide that the
chosen candidate is not in (`widestPlateauNotChosen`). The proposition is about
the CHOICES this run made, not about whether the scoring discriminates.

Proved by `decide` over the transcribed data, no `sorry` and no `native_decide`
-- the `wmS5RunConformsToDrawnWiring` precedent. The Clojure side of the same
comparison is `futon2:holes/labs/wm-contract/re7_selection_discrimination.bb`,
whose verdict for this run is `:green`; the plants that move it are in
`runs/RE7-selection-discrimination/2026-09-04-re5/03-controls.edn`, controls C2-C6. -/
theorem wmRe5SelectionDiscrimination :
    selectionDiscriminates re5SelectionTies := by
  decide

/-- The census the verdict is stated over, so the numbers a reader checks
against `runs/RE7-selection-discrimination/2026-09-04-re5/01-decisions.edn`
are themselves decided rather than asserted in prose: 4 decisions, 0 of them
chosen by tie-break, widest chosen tie 1, deepest chosen rank 1, field size
146, and the widest plateau NOT holding the choice 56. -/
theorem wmRe5SelectionTieCensus :
    re5SelectionTies.length = 4 ∧
      (re5SelectionTies.filter (fun t => t.chosenByTiebreak)).length = 0 ∧
      (re5SelectionTies.map (fun t => t.tieCount)).foldl max 0 = 1 ∧
      (re5SelectionTies.map (fun t => t.chosenRank)).foldl max 0 = 1 ∧
      (re5SelectionTies.map (fun t => t.fieldSize)).foldl max 0 = 146 ∧
      (re5SelectionTies.map (fun t => t.widestPlateauNotChosen)).foldl max 0 = 56 := by
  decide

/-- Fixture scaffolding: one COMPARABLE tick of a wm-trace run — the mission the recorded Q(π) decision selected (`:decision :action :target`) against the mission the actuation path enacted (`:realized-outcome :policy`). A form is COMPARABLE iff it carries both halves; forms carrying only one are not transcribed, so the list lengths below are smaller than the files' form counts. -/
structure EnactedVsSelected where
  selected : String
  enacted : String
  deriving DecidableEq

/-- DERIVED: the two halves name the same mission — the property the original `enactedActionEqualsSelected` asserted of every record. A computed predicate, not a fact. -/
def EnactedVsSelected.agrees (r : EnactedVsSelected) : Bool := r.selected == r.enacted

private def firstFlightsVsBayesianStructureLearning : EnactedVsSelected :=
  {selected := "M-first-flights", enacted := "M-bayesian-structure-learning"}

/-- CLOSED-BY-RECORD · owner: wm-organization · TN-edge-review worklist H1b · holder: by-record · evidence: `futon2:data/wm-trace/wm-trace-2026-07-04.edn` · falsifier: the file's comparable records are not 37 copies of this pair · SNAPSHOT 2026-09-01: the file holds 38 forms, 37 of which carry both halves, and every one of the 37 carries the SAME pair — selection `M-first-flights`, enactment `M-bayesian-structure-learning`. Represented extensionally. Later trace growth does not rewrite this value. -/
def wmTrace20260704EnactedVsSelected : List EnactedVsSelected :=
  List.replicate 37 firstFlightsVsBayesianStructureLearning

/-- CLOSED-BY-RECORD · owner: wm-organization · TN-edge-review worklist H1b · holder: by-record · evidence: `futon2:data/wm-trace/wm-trace-2026-07-05.edn` · falsifier: the file's comparable records are not 13 copies of this pair · SNAPSHOT 2026-09-01: the file holds 18 forms, 13 of which carry both halves, all carrying the same pair as the 07-04 file. The gate verdicts differ across these 13 (5 records gate `M-canon-fingerprint-store` `:fail`, 8 `:abstain-missing-leg`) without changing either half. -/
def wmTrace20260705EnactedVsSelected : List EnactedVsSelected :=
  List.replicate 13 firstFlightsVsBayesianStructureLearning

/-- CLOSED-BY-RECORD · owner: wm-organization · TN-edge-review worklist H1b · holder: by-record · evidence: the two file snapshots above · falsifier: a trace file carrying both halves that is absent from this concatenation · The comparable population, and it is exactly two files wide: of the 57 wm-trace forms' files, only 07-04 and 07-05 join a recorded selection to a recorded enactment. 07-03 records a selection on a sorry against an enacted mission and has no join key; the other 54 record no actuation; the two tick-run records carry neither half and declare a stub selector (C460 §2). -/
def enactedVsSelectedComparable : List EnactedVsSelected :=
  wmTrace20260704EnactedVsSelected ++ wmTrace20260705EnactedVsSelected

/-- CLOSED-BY-RECORD · owner: wm-organization · TN-edge-review worklist H1 (refuted), H1b (this record) · holder: by-record · evidence: proof term over `enactedVsSelectedComparable`, transcribed from `futon2:holes/labs/wm-contract/C460-enacted-vs-selected.md` and re-counted form by form against `futon2:data/wm-trace/wm-trace-2026-07-04.edn` and `futon2:data/wm-trace/wm-trace-2026-07-05.edn` · falsifier: a comparable record whose selection and enactment name the same mission · COUNTEREXAMPLE 2026-09-01: the original claim held open that the enacted action equals the recorded Q(π) selection on every path, with falsifier "a run in which the enacted action differs". V1/C460 produced that run, and the scale is not marginal — 50 records carry both halves, the enactment differs from the selection in 50 of them, and none agree. The mechanism is `close-loop!`'s and it is worse than a tie broken differently: the rank-1 selection never reached the gate stage, so the first lower-ranked candidate to pass its act gate was enacted (`futon2/src/futon2/aif/enact.clj:287-316`, C460 §4). The historical name remains legible; the proposition now records the refutation — the agreeing set is empty over a non-empty population. What replaces it is `enactedEqualsSelectedWhenRankOneGated`, a bound to be tested and NOT a claim believed true. -/
def enactedActionEqualsSelected :
    enactedVsSelectedComparable.length = 50 ∧
      enactedVsSelectedComparable.filter EnactedVsSelected.agrees = [] := by
  decide

/-- PERMANENT EXTERNAL ATTESTATION · Lean cannot prove an event · evidence is the executable witness · contract kind HOLE intentionally · owner: wm-organization · TN-edge-review worklist H1b · holder: by-record · evidence: a run record in which the rank-1 selection passes its own act gate, paired with the action that was then enacted · falsifier: a run in which the rank-1 selection passes its gate and a different action is enacted · A BOUND TO BE TESTED, NOT A CLAIM BELIEVED TRUE — read the counterexample above first. `enactedActionEqualsSelected` is refuted on record: over `futon2/data/wm-trace/wm-trace-2026-07-04.edn` and `futon2/data/wm-trace/wm-trace-2026-07-05.edn`, the only two files joining a selection to an enactment, the paths disagree in 50 of 50 comparable records and agree in none. So this is not a weaker form of something observed to hold; it is the untested remainder after the strong claim fell. THE ANTECEDENT HAS NEVER OCCURRED ON RECORD: in all 50 records the act gates run over exactly two missions (`M-canon-fingerprint-store`, `M-bayesian-structure-learning`) and the rank-1 selection `M-first-flights` is not among them, so the rank-1 selection passes its gate in ZERO of 50 — the bound is vacuously unfalsified rather than supported, and a reader must not take its openness for evidence. The two paths can coincide only when the selected entry is also the first to pass its gate: `full_loop_runner`'s `selected-entry` enacts the recorded selection (`futon2/src/futon2/aif/full_loop_runner.clj:870-873`), `close-loop!` takes the first passing gate in ranking order (`futon2/src/futon2/aif/enact.clj:287-316`), and nothing enforces that they meet. Deciding this needs a run that produces the antecedent at all. -/
def enactedEqualsSelectedWhenRankOneGated : Prop := sorry

/-- PERMANENT EXTERNAL ATTESTATION · Lean cannot prove the absence of a code path · evidence is the executable witness · contract kind HOLE intentionally · owner: wm-organization · TN-edge-review worklist H2 · holder: by-record · evidence: a provenance walk from `DirichletConcentrations` back to its producer — name the feeder, grep the store, find the writer · falsifier: a code path from the tick model's o or μ into R17's concentrations · THE THEORY AND THE MACHINE ACCUMULATE FROM DIFFERENT SOURCES. Da Costa eq. 21 accumulates Dirichlet concentrations from the tick model's (o, s). A4a instead builds a capability × mission model: `a4a_substrate/read-corpus` reads `hyperedges-by-type :capability/*` and hands the corpus to `a4a/corpus->concentration` (`futon2/src/futon2/aif/a4a_substrate.clj:46-60`), and those hyperedges are written by the A3 actuator (`futon2/src/futon2/aif/actuator_a3.clj:31, 68`, discharge records at `:486-487`). The A4a namespace says so itself: it is pure, and its concepts are "demo-validated until real :capability/* production writes flow" (`futon2/src/futon2/aif/a4a.clj:2-6`). So R2→R17 and R1→R17 are not realised, and this is why: not a missing wire between two boxes that otherwise agree, but two accumulations over different data. The claim held open is the ABSENCE — no path carries the tick model's o or μ into R17's concentrations. Finding one falsifies it, and would also close the two edges. -/
def dirichletAccumulationImportAbsent : Prop := sorry

/-- PERMANENT EXTERNAL ATTESTATION · Lean cannot prove an event · evidence is the executable witness · contract kind HOLE intentionally · owner: wm-organization · TN-edge-review worklist H3, from Joe's J1 ruling · holder: by-record · evidence: a run record carrying τ together with the β it was derived from · falsifier: no run record carries τ together with the β it was derived from — every persisted tick's τ produced by an engineering calibration law and none by carry-β · THE MACHINE'S DIAL IS NOT THE FORMALISM'S. Friston 2017 eq. 2.7 and Da Costa 2020 A.2 give policy precision as γ = 1/β with β ← β + (π − π₀)·G — the precision learns from the policy posterior's departure from its prior, weighted by expected free energy. What the machine uses instead is τ from the score spread and an engineering selection gain (`futon2/src/futon2/aif/policy.clj:77-145`, `effective-temperature`; the DEFAULT `:spread` mode computes τ_eff = τ_spread / g at `:133`), and `selection_gain.clj` says in its own words that this "is not Friston's variational policy precision". Live, the gain does not even move: the fold returns the state unchanged unless a realised outcome is well-formed and new, and the field "is ABSENT today, sim-only", so τ holds at its prior (`futon2/src/futon2/aif/selection_gain.clj:187-193`). No β appears anywhere in the policy path. J1 ruled the drawn R7→R14 was a conflation and that the theory-aligned precision is to be pursued; this is the claim held open: policy precision is γ = 1/β updated by eq. 2.7. · OWNER CORRECTION 2026-09-03 (Joe's J10 ruling, executed by worklist :U47). THE FALSIFIER FIELD: it read "a run record in which τ is set by the β update from G and π", which is the CONFIRMING observation — word for word what the evidence field asks for — and not a refutation. Twelve of the fifteen holes use the field as a genuine refutation (`wmRunsOnce`: "no invocation of the tick entry point completes end-to-end with a TickRunRecord"; `dirichletAccumulationImportAbsent` says outright "the claim held open is the ABSENCE"), so H3/H4 were the anomaly and both are corrected to that absence form. THE POINTER: `policy.clj:242-245` was re-resolved at source and now holds `gap-report`, an unrelated helper; the τ law is `effective-temperature`, cited above at its current lines. DISPOSITION :run-gated, and no persisted record exists: `futon2/data/wm-trace/wm-trace-2026-09-01.edn` carries 18 `:tau-source` values and every one is `:selection-gain-only`, and S3's one live τ = β tick ran under a write-suppressing preflight (`futon2/holes/labs/wm-contract/run8_s3_preflight.clj:28-54`), so nothing was persisted. NOT REPAIRED AND STATED RATHER THAN SMOOTHED: the sentence "No β appears anywhere in the policy path" above is false of the current tree — `effective-temperature`'s `:variational-beta-gamma` mode sets τ = β (`futon2/src/futon2/aif/policy.clj:101-105`, `:135-144`) and `carry-beta` supplies it with its provenance (`futon2/src/futon2/aif/policy_precision.clj:544-560`), both landed by RUN8/I1 after this docstring was written; it is true of the DEFAULT `:spread` path. That is H4's F4 defect occurring in H3, and J10 did not enumerate it, so it is reported here rather than repaired. -/
def policyPrecisionIsGammaFromBeta : Prop := sorry

/-- PERMANENT EXTERNAL ATTESTATION · Lean cannot prove an event · evidence is the executable witness · contract kind HOLE intentionally · owner: wm-organization · TN-edge-review worklist H4, from Joe's J2 ruling · holder: by-record · evidence: a run record whose Q(π) carries a per-policy F term alongside E and G · falsifier: no default-path run record's Q(π) carries a per-policy F term — F_π reaching the posterior only under `FUTON_WM_FPI_POSTERIOR=1` · TWO DIFFERENT FREE ENERGIES, AND THE MACHINE COMPUTES NEITHER WHERE THE FORMALISM NEEDS IT. Parr 2022 B.9 gives the policy posterior as π = σ(ln E − F − G), where F_π is the variational free energy of the observations under each policy. The machine's policy score is −G/τ + log-prior (`futon2/src/futon2/aif/policy.clj:157-215`, `selection-scores` normalised by `softmax-weights`) — there is no F term in it, and no free-energy symbol anywhere in the scoring path. The Laplace channel F that R8 does compute is a different quantity and a diagnostic: it is bound at `futon2/scripts/futon2/report/war_machine.clj:5773`, route-tagged :R8 at :6087, and appears exactly once more, in the report map at :6472 — downstream of scoring, consumed by nothing (C448, C452, D1). So the free energy that exists is not consumed, and the free energy the posterior needs is not computed. J2 ruled on the composition; this is the claim held open: the policy posterior imports F_π. · OWNER CORRECTION 2026-09-03 (Joe's J10 ruling, executed by worklist :U47). THE FALSIFIER FIELD: it read "a run record in which Q(π) is computed with an F_π term from the observations under each policy", which is the CONFIRMING observation — word for word what the evidence field asks for — and not a refutation; it is corrected to the absence form the other twelve holes use, and scoped to the default path because the flagged path's record already exists. THE SENTENCE ABOVE IS SCOPED, NOT RETIRED: "there is no F term in it, and no free-energy symbol anywhere in the scoring path" is true of the DEFAULT path and false of the seam. `selection-scores` now writes the score as `ln E(a) − G(a)/τ [− F_pi(a)]` (`futon2/src/futon2/aif/policy.clj:158`) and takes `:f-pi-policy-posterior?`, `:f-pi-values` and `:f-pi-scaling` as options (`:184-186`), both landed by RUN9/I2 after this docstring was written; `FUTON_WM_FPI_POSTERIOR` is read from the environment and is default-off (`futon2/scripts/futon2/report/war_machine.clj:199-219`), so F_π enters no default-path score. THE THREE war_machine.clj POINTERS were re-resolved at source and their subject is GONE: the Laplace-channel scalar F was RETIRED on 2026-09-01 by worklist I5 slice (c) under Joe's J2 ruling (futon2 `5a66411`; `futon2/src/futon2/aif/free_energy.clj:7-12` records why). So `:5773` binds the controller-diagnostics map that used to carry it, `:6087`'s :R8 tag now names `futon2.aif.free-energy/compute-prediction-error` — ε, not the removed `compute-variational-free-energy` — and `:6472` puts that same diagnostics map on the report, not the scalar. THE RECEIPT DISCREPANCY, STATED: the 2026-08-30 measurement still records the R3→R8 hop `:via "futon2.aif.free-energy/compute-variational-free-energy"` (`p4ng/empirics-futon/control-map-edges.edn:140-144`, carried derivatively at `futon2/holes/labs/wm-contract/edge-census.edn:82`). It is not rewritten: it records what was measured against `tick-run-record-2026-08-30.edn` and is still true of that receipt, so the registry row and the code now disagree by construction — C473 §1 reports it unrepaired. DISPOSITION :witnessed-under-flag, held open :run-gated: `futon2/holes/labs/wm-contract/runs/2026-09-01-s4/wm-trace-s4.edn` carries `:f-pi-posterior {:status :present, :applied? true}` on 3 of its 4 ticks, which witnesses the FLAGGED path; the hole closes on a default-path persisted record carrying the term, or if the flag is ruled default-on, which is its own ruling. -/
def policyPosteriorImportsPolicyF : Prop := sorry

structure WitnessLayerRow where
  row : String
  layer : Layer
  usedAsValueEvidence : Bool

abbrev WitnessLayerTable := List WitnessLayerRow

structure IllFormedTick where
  tickId : String
  missingChannels : List String
  unexpectedChannels : List String

abbrev IllFormedList := List IllFormedTick

structure R8DispositionEvidence where
  missingFComputableTickIds : List String
  storedFTickIds : List String
  insufficientInputsTickIds : List String

inductive Era where | before | after

/-- Per-era tally of the three `:free-energy` shapes — a non-uniform era is REPRESENTABLE (claude-13 via claude-20, 2026-08-30: a single `shape` value presupposed the uniformity that `r8EraBoundary` exists to test — an evidence type that cannot express its own falsifier makes `:conformant` a certainty). -/
structure ShapeTally where
  gMap : Nat
  controllerMap : Nat
  unknown : Nat
  deriving DecidableEq, Repr

/-- Evidence for `r8EraBoundary`, as FACTS only, with UNITS in the names (claude-20, 2026-08-30: 520403.9349 / 755 forms = 689.28, / 5502 channel values = 94.5845 — the reported mean was per channel value while the docstring paired it with the per-form population; a denominator without its unit is a second population choice). `count` is the era's form count; `storedFCount` / `selectionGainCount` are how many forms carry each key (the LAW decides uniformity); `shapes` is the tally; `precisionSum` is the sum of channel precision VALUES, `precisionValues` how many values were summed (the mean's denominator, by construction), and `precisionForms` how many forms contributed them (a fact a reader wants — 755 of 760 — never a denominator). Before era today: 5502 values from 755 forms → 94.5845. -/
structure EraSummary where
  count : Nat
  storedFCount : Nat
  selectionGainCount : Nat
  shapes : ShapeTally
  precisionSum : ℝ
  precisionValues : Nat
  precisionForms : Nat

/-- DERIVED: the mean over the VALUES summed — true by construction; a computed value, not a fact (claude-13 / claude-20, 2026-08-30). `0` when no values were summed, and that is a typed absence the lint can see. -/
noncomputable def EraSummary.meanPrecision (e : EraSummary) : ℝ :=
  if e.precisionValues = 0 then 0 else e.precisionSum / e.precisionValues

/-- DERIVED: an era is uniform in the two keys iff every form carries both or none carries either — the property the law tests, stated on the tally so that its failure is representable. -/
def EraSummary.uniform (e : EraSummary) : Prop :=
  (e.storedFCount = e.count ∧ e.selectionGainCount = e.count) ∨
  (e.storedFCount = 0 ∧ e.selectionGainCount = 0)

structure EraTable where
  boundary : Nat
  perEra : Era → EraSummary

private def mkClosed (name owner : String) : Declaration :=
  {name, kind := .closed, signature := s!"see {name} in the source module", owner,
   holder := "by-record", decided := "2026-08-30"}

private def mkWitnessedClosed (name owner evidence falsifier : String) : Declaration :=
  {name, kind := .closed, signature := s!"see {name} in the source module", owner,
   holder := "by-record", decided := "2026-08-31", evidence := some evidence,
   falsifier := some falsifier}

private def mkHole (name owner evidence falsifier : String) : Declaration :=
  {name, kind := .hole, signature := s!"see {name} in the source module", owner,
   holder := "by-record", decided := "2026-08-30", evidence := some evidence,
   falsifier := some falsifier}

-- A claim closed by REFUTATION rather than by witness: the historical name is kept,
-- its proposition now records the counterexample, and `decided` is the date the record
-- refuted it — not the batch date `mkWitnessedClosed` carries.
private def mkRefutedByRecord (name owner evidence falsifier : String) : Declaration :=
  {name, kind := .closed, signature := s!"see {name} in the source module", owner,
   holder := "by-record", decided := "2026-09-01", evidence := some evidence,
   falsifier := some falsifier}

-- A hole CLOSED by the J9 criterion (futon2 holes/labs/wm-contract/RUNBOOK.md,
-- Joe 2026-09-03): the declared evidence obligation ended, and `decided` is the
-- date of that ruling rather than the batch date `mkClosed`/`mkWitnessedClosed`
-- carry.  The `evidence` and `falsifier` fields are KEPT: what discharged the
-- obligation and what would still refute the claim are the content of the
-- closure, and `mkClosed` would drop both.
private def mkClosedUnderCriterion (name owner evidence falsifier : String) : Declaration :=
  {name, kind := .closed, signature := s!"see {name} in the source module", owner,
   holder := "by-record", decided := "2026-09-03", evidence := some evidence,
   falsifier := some falsifier}

private def mkRefused (name owner reason : String) : Declaration :=
  {name, kind := .hole, signature := s!"see {name} in the source module", owner,
   holder := "by-record", decided := "2026-08-30", falsifier := some s!"REFUSED: {reason}"}

private def closedDeclarations : List Declaration :=
  ([("Pattern", "P-validated-R5 §2.1d"), ("Cascade", "P-validated-R5 §3e"),
   ("HaveWantArrowState", "sec-glossary.tex:78 · P-glossary-mathematics"),
   ("HaveWantArrowComposition", "sec-glossary.tex:78 · P-glossary-mathematics"),
   ("ControlPolicy", "sec-glossary.tex:39 · P-glossary-mathematics"),
   ("AlivenessFactor", "sec-glossary.tex:54 · P-glossary-mathematics"),
   ("ActGateVerdict", "sec-glossary.tex:70 · P-glossary-mathematics"),
   ("Click", "sec-glossary.tex:82 · P-glossary-mathematics"),
   ("Attempt", "sec-glossary.tex:82 · P-glossary-mathematics"),
   ("Tension", "P-validated-R5 §3e"), ("InformationState", "P-validated-R5 §3d"),
   ("DecisionRule", "P-validated-R5 §3"), ("Outcome", "P-validated-R5 §2a"),
   ("G", "P-validated-R5 §2a′"), ("nonDegenerate", "P-validated-R5 §2a′"),
   ("fastForward", "P-validated-R5 §3e O3"), ("independent", "P-R9 S1"),
   ("IndependenceVerdict", "P-R9 §solved 2"), ("independenceVerdict", "P-R9 §solved 1–2"),
   ("r9CheckerSound", "P-R9 §solved 3"), ("r9VerdictsSound", "P-R9 §solved 3"), ("ShapeTally", "P-R8 §solved 1 (iii) evidence"), ("EraSummary.meanPrecision", "P-R8 §solved 1 (iii) evidence"), ("EraSummary.uniform", "P-R8 §solved 1 (iii) evidence"), ("DeclarationSource", "P-R9 §solved 2 (declaration source)"), ("r9PerRowDeclarations", "P-R9 §solved 2 (per-row declarations)"),
   ("TickRunRecord", "record: futon2:holes/problems/BUILD-packets/WM-RUN1.md · Joe 2026-08-31 · runs-once receipt"), ("RouteHop", "record: futon2:holes/problems/BUILD-packets/WM-RUN2.md · Joe 2026-08-31 · route tracer"),
   ("PreferenceSource", "P-R19-preferences-open §principle"), ("PreferenceLayerRecord", "P-R19-preferences-open §tetrahedron"),
   ("wmPreferenceStack2026_08_30", "R19-preference-stack.edn @ dc1dac8"), ("wmStackDeclaredPurpose", "R19-preference-stack.edn @ dc1dac8"),
   ("preferenceStackRecorded", "P-R19-preferences-open §gate"), ("PreferenceLayer", "P-R19-preferences-open §principle"),
   ("foldC", "P-R19-preferences-open §principle"), ("PreferenceStack", "P-R19-preferences-open §tetrahedron"),
   ("PreferenceSpineDeclaration", "P-R19-preferences-open §principle"),
   ("PreferenceConstantCensusRow", "P-R19-preferences-open §principle"),
   ("preferenceConstantCensus", "P-R19-preferences-open §principle"),
   ("freePreferenceConstants", "P-R19-preferences-open §principle"),
   ("freePreferenceConstants_eq", "P-R19-preferences-open §principle"),
   ("machineHasNoC", "P-R19-preferences-open §principle"),
   ("Delivery", "delivery-lifecycle §0.6"), ("Handoff", "delivery-lifecycle §0.10"),
   ("Workflow", "delivery-lifecycle §0.10"), ("r2WellFormed", "P-R2 §solved 1"),
   ("r2ContractCensus", "P-R2 §solved 1"), ("r8Disposition", "P-R8 §solved 1"),
   ("r8Census", "P-R8 §solved 1"),
   ("cascadeGrainPi", "sec-glossary.tex:52 · P-glossary-mathematics"),
   ("observationKernelRowMass", "sec-glossary.tex:31 · P-glossary-mathematics"),
   ("beliefUpdate", "sec-glossary.tex:9,15,17,19,31 · P-glossary-mathematics")].map fun p => mkClosed p.1 p.2)
  ++ [mkWitnessedClosed "modelReductionFreeEnergyChange" "sec-glossary.tex:62 · P-glossary-mathematics"
      "ModelReductionFreeEnergyChangeWitness" "the analytic Dirichlet-normalizer result is perturbed or per-tick variational F is accepted as BMR delta-F",
      mkWitnessedClosed "ObservationVector" "sec-glossary.tex paragraph:Observation vector o · P-glossary-mathematics"
      "ObservationVectorWitness" "a partial channel map or single vertex-tagged outcome is accepted as the complete 14-coordinate observation vector",
      mkWitnessedClosed "PredictiveOutcomeKernel" "sec-glossary.tex:23 · P-glossary-mathematics"
      "PredictiveOutcomeKernelWitness" "an unconditional outcome distribution or softmax policy vector is accepted as policy-conditioned Q(o|pi)",
      mkWitnessedClosed "ParameterPriorKernel" "sec-glossary.tex:33 · P-glossary-mathematics"
      "ParameterPriorKernelWitness" "predictive outcome Q(o|pi) or unconditioned policy habit Q(pi) is accepted as parameter prior Q(theta|pi)",
      mkWitnessedClosed "ParameterPosteriorKernel" "sec-glossary.tex:33 · P-glossary-mathematics"
      "ParameterPosteriorKernelWitness" "parameter-prior Q(theta|pi) or predictive-outcome Q(o|pi) is accepted as posterior Q(theta|o,pi)",
      mkWitnessedClosed "TransitionKernel" "sec-glossary.tex:7 · P-glossary-mathematics"
      "TransitionKernelWitness" "an action-unconditioned state kernel or scalar multivariate-beta normalizer B(alpha) is accepted as controlled transition B",
      mkWitnessedClosed "PreferenceDistribution" "sec-glossary.tex:25 · P-glossary-mathematics"
      "PreferenceDistributionWitness" "a state-conditioned kernel or vertex-local pragmatic cost is accepted as the unconditioned preferred-outcome distribution"]
  ++ [mkClosed "observationEntropy" "sec-glossary.tex:21,29 · P-glossary-mathematics",
      mkClosed "G_eq_expectedFreeEnergy" "sec-glossary.tex:21,27,29 · P-glossary-mathematics",
      mkClosed "ExpectedInformationGainValue" "sec-glossary.tex:33 · P-glossary-mathematics",
      mkClosed "parameterInformationGain" "sec-glossary.tex:33 · P-glossary-mathematics",
      mkClosed "modelUncertaintyBonus" "sec-glossary.tex:33 · P-glossary-mathematics",
      mkClosed "generativeFactorMass" "sec-glossary.tex:7 · P-glossary-mathematics",
      mkClosed "wmCascadeDiffFixture" "P-validated-R5 §3e O1–O4"]
  ++ [mkWitnessedClosed "logMultivariateBeta" "sec-glossary.tex:62 · P-glossary-mathematics"
      "LogMultivariateBetaWitness" "value disagrees with the Dirichlet normaliser",
      mkWitnessedClosed "expectedFreeEnergy" "sec-glossary.tex:21,27,29 · P-glossary-mathematics"
      "ExpectedFreeEnergyWitness" "risk-plus-ambiguity disagrees with the kernel-derived value",
      mkWitnessedClosed "ambiguity" "sec-glossary.tex:21,29 · P-glossary-mathematics"
      "AmbiguityWitness" "expected observation entropy disagrees with the kernel-derived value",
      mkWitnessedClosed "HaveWantArrow" "sec-glossary.tex:78 · P-glossary-mathematics"
      "HaveWantArrowWitness" "a composition whose left want differs from the right have elaborates",
      mkWitnessedClosed "Fold" "sec-glossary.tex:68 · P-glossary-mathematics"
      "FoldWitness" "a fold without explicit policy holes elaborates",
      mkWitnessedClosed "FoldEscrowRecord" "sec-glossary.tex:68 · P-glossary-mathematics"
      "FoldEscrowRecordWitness" "a reconstructible prompt/digest pair is admitted to the non-reconstructible quarantine",
      mkClosed "FoldEscrowRecord.reconstructible" "sec-glossary.tex:68 · P-glossary-mathematics",
      mkWitnessedClosed "BeliefState" "sec-glossary.tex:9 · P-glossary-mathematics"
      "BeliefStateWitness" "a declared channel lacks its mean or nonnegative variance",
      mkWitnessedClosed "variationalFreeEnergy" "sec-glossary.tex:19 · P-glossary-mathematics"
      "VariationalFreeEnergyWitness" "the Gaussian reference value disagrees, or expected free energy is accepted as variational F",
      mkWitnessedClosed "PrecisionMap" "sec-glossary.tex:17 · P-glossary-mathematics"
      "PrecisionWitness" "swapping precision with its signed prediction error preserves variational F, or a signed error map is accepted as precision",
      mkWitnessedClosed "predictionError" "sec-glossary.tex:15 · P-glossary-mathematics"
      "PredictionErrorWitness" "prediction error equals either operand or uses the reversed sign",
      mkWitnessedClosed "softmax" "sec-glossary.tex:35 · P-glossary-mathematics"
      "SoftmaxWitness" "weights fail to normalise or higher expected free energy receives higher probability at positive temperature",
      mkWitnessedClosed "bayesFactorThreshold" "sec-glossary.tex:64 · P-glossary-mathematics"
      "BayesFactorThresholdWitness" "a change above -3 passes, or a variational-free-energy value is accepted as BMR evidence",
      mkWitnessedClosed "bayesianModelReduction" "sec-glossary.tex:58 · P-glossary-mathematics"
      "BayesianModelReductionWitness" "the reduced posterior fails to preserve the accumulated count vector A-a under the new prior a'",
      mkWitnessedClosed "DirichletConcentrations" "sec-glossary.tex:60 · P-glossary-mathematics"
      "DirichletConcentrationsWitness" "an empty vector or a zero/negative concentration is accepted",
      mkWitnessedClosed "Channel" "P-R2 §solved 1 (Channel)"
      "ChannelWitness" "the declared names or order differ from the 14-channel record",
      mkWitnessedClosed "observationKernel" "sec-glossary.tex:31 · P-glossary-mathematics"
      "ObservationKernelWitness" "a row has negative mass or its declared masses do not sum to one",
      mkWitnessedClosed "predictiveOutcomeRisk" "sec-glossary.tex:21,27 · P-glossary-mathematics"
      "PredictiveOutcomeRiskWitness" "predictive support contains an outcome with zero preference mass, or KL disagrees with the reference",
      mkWitnessedClosed "PolicyPriorKernel" "sec-glossary.tex:41,7 · P-glossary-mathematics"
      "PolicyPriorKernelWitness" "the prior is conditioned on state rather than Unit, or its policy masses are not a distribution",
      mkWitnessedClosed "ControlVocabulary" "sec-glossary.tex:39 · P-glossary-mathematics"
      "ControlVocabularyWitness" "a policy containing a control outside its vocabulary elaborates",
      mkWitnessedClosed "aliveness" "sec-glossary.tex:54 · P-glossary-mathematics"
      "AlivenessWitness" "0.8 times 0.6 differs from 0.48, or a negative factor elaborates",
      mkWitnessedClosed "actGate" "sec-glossary.tex:70 · P-glossary-mathematics"
      "ActGateWitness" "a missing leg passes, or a non-improving complete gate passes",
      mkWitnessedClosed "Cohort" "sec-glossary.tex:82 · P-glossary-mathematics"
      "CohortWitness" "a zero-target or overfull preregistered cohort elaborates",
      mkWitnessedClosed "expectedInformationGain" "sec-glossary.tex:33 · P-glossary-mathematics"
      "ExpectedInformationGainWitness" "posterior-to-prior KL disagrees with recorded EIG",
      mkWitnessedClosed "GenerativeModel" "sec-glossary.tex:7 · P-glossary-mathematics"
      "GenerativeModelWitness" "joint does not factor into observation, transition, and policy prior",
      mkWitnessedClosed "modelUncertaintyAndEIG" "sec-glossary.tex:33 · P-glossary-mathematics"
      "proof term" "the normalized point-mass counterexample no longer elaborates, or the collapsed equality elaborates",
      mkWitnessedClosed "organiseO1NodesRecorded" "P-validated-R5 §3e O1"
      "CascadeDiff" "nodes mismatch or additions unrecorded",
      mkWitnessedClosed "organiseO2AuthoredReachability" "P-validated-R5 §3e O2"
      "CascadeDiff" "edge lacks authored reachability",
      mkWitnessedClosed "organiseO3FastForward" "P-validated-R5 §3e O3"
      "CascadeDiff" "edges differ from fast-forward",
      mkWitnessedClosed "organiseO4PrecedenceGovernance" "P-validated-R5 §3e O4 and S-G4"
      "CascadeDiff" "precedence changes neither order nor score",
      mkClosed "valueEvidenceRequiresL2" "P-R9 S1",
      ]

private def holeDeclarations : List Declaration :=
  [mkRefused "C" "P-validated-R5 §2a" "implementation; no observation selects C",
   mkClosedUnderCriterion "nonDegenerateAblationLaw" "P-validated-R5 §2a′" "ExactDyadicAblationTable" "recorded G and pragmatic minimizer sets overlap",
   mkRefused "find" "P-validated-R5 §3e find" "implementation, not a law",
   mkClosedUnderCriterion "findF1Containment" "P-validated-R5 §3e F1" "FindReceiptTable" "selection escapes repository or empty lacks absence",
   mkClosedUnderCriterion "findF2Receipted" "P-validated-R5 §3e F2" "FindReceiptTable" "selected pattern lacks receipt",
   mkClosedUnderCriterion "findF3NonSelfCertifying" "P-validated-R5 §3e F3" "FindReceiptTable" "receipt uses score alone",
   mkClosedUnderCriterion "findF4Falsifiable" "P-validated-R5 §3e F4" "FindReceiptTable" "a recorded zero-mass pattern is absent from the repository or selected",
   mkRefused "organise" "P-validated-R5 §3e organise" "implementation, not a law",
   mkWitnessedClosed "r9VerdictConsultsChecker" "P-R9 §solved 3" "proof term" "decision ignores checker",
   mkWitnessedClosed "wmVerdictsLedgerAlone" "P-R9 §solved 2" "VerdictTable" "a fixture row or verdict is absent",
   mkWitnessedClosed "wmVerdictsDeclared" "P-R9 §solved 2" "VerdictTable" "a fixture row or verdict is absent",
   mkWitnessedClosed "r9WmVerdictsSound" "P-R9 §solved 3" "VerdictTable" "self producer judged independent",
   mkWitnessedClosed "r9TwoRunCensus" "P-R9 §solved 2" "VerdictTable" "either thirteen-row census differs",
   mkWitnessedClosed "r9WmPerRowDeclarations" "P-R9 §solved 2 (per-row declarations)" "VerdictTable" "a named-agent row under the paper sentence, or an unnamed row under row text",
   mkWitnessedClosed "wmTraceR2" "P-R2 §solved 1" "List R2TickLit" "fixture digest differs",
   mkWitnessedClosed "r2ContractCensusWmTrace" "P-R2 §solved 1" "IllFormedList" "census is not 2",
   mkWitnessedClosed "wmTraceR8" "P-R8 §solved 1" "R8PinnedSnapshot" "fixture digest differs",
   mkWitnessedClosed "r8CensusWmTrace" "P-R8 §solved 1" "R8DispositionEvidence" "triple differs from (755,32,5)",
   mkWitnessedClosed "r8EraBoundary" "P-R8 §solved 1 (iii)" "EraTable" "a form is in neither era",
   mkHole "preferenceStackLiveRecorded" "P-R19-preferences-open §gate" "PreferenceStackWitness" "a C value in a live trace with no layer record behind it",
   mkHole "wmRunsOnce" "record: futon2:holes/problems/BUILD-packets/WM-RUN1.md · Joe 2026-08-31 · run-at-least-once" "TickRunWitness" "no tick-entry invocation completes with a TickRunRecord; amended 2026-08-31: original 'currently firing (selector-seam blocker)' is historical — a nine-hop declared-stub tick completed, while the production loop uses the Agency HTTP selector",
   mkHole "wmRunConformsToWiring" "record: futon2:holes/problems/BUILD-packets/WM-RUN2.md · Joe 2026-08-31 · organisation evidence" "TickRunRecord" "empty route or any hop absent from both original and measured Figure 4 layers",
   mkRefutedByRecord "enactedActionEqualsSelected" "wm-organization · TN-edge-review worklist H1 (refuted), H1b" "C460 over wm-trace-2026-07-04.edn and wm-trace-2026-07-05.edn: 50 comparable records, 50 differ, 0 agree" "a comparable record whose selection and enactment name the same mission",
   mkHole "enactedEqualsSelectedWhenRankOneGated" "wm-organization · TN-edge-review worklist H1b" "TickRunRecord" "a run in which the rank-1 selection passes its gate and a different action is enacted",
   mkHole "dirichletAccumulationImportAbsent" "wm-organization · TN-edge-review worklist H2" "DirichletConcentrations" "a code path from the tick model's o or mu into R17's concentrations",
   mkHole "policyPrecisionIsGammaFromBeta" "wm-organization · TN-edge-review worklist H3 (Joe's J1 ruling)" "TickRunRecord" "no run record carries tau together with the beta it was derived from — every persisted tick's tau produced by an engineering calibration law and none by carry-beta; corrected 2026-09-03 (Joe's J10 ruling, worklist :U47): the original field named the CONFIRMING observation, word for word what the evidence field asks for",
   mkHole "policyPosteriorImportsPolicyF" "wm-organization · TN-edge-review worklist H4 (Joe's J2 ruling)" "TickRunRecord" "no default-path run record's Q(pi) carries a per-policy F term — F_pi reaching the posterior only under FUTON_WM_FPI_POSTERIOR=1; corrected 2026-09-03 (Joe's J10 ruling, worklist :U47): the original field named the CONFIRMING observation, and the S4 record already satisfies it under the flag"]

def registry : Registry :=
  {schemaVersion := 1, contractId := "wm-holes", moduleName := "DarkTower.WarMachine.Holes",
   declarations := closedDeclarations ++ holeDeclarations}

end
end DarkTower.WarMachine.Holes

def main : IO Unit :=
  DarkTower.Contract.Emit.emit DarkTower.WarMachine.Holes.registry
