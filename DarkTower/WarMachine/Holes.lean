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

/-- HOLE · owner: P-validated-R5 §2a · holder: by-record · evidence: REFUSED — this is an implementation, not a law, and the record fixes no observation that selects C · falsifier: REFUSED for the same reason · Preferences are declared per PRAGMATIC vertex only. -/
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

/-- HOLE · owner: P-validated-R5 §2a′ · holder: by-record · evidence: AblationTable · falsifier: no prior has moved = true · For some declared prior, removing the epistemic term changes the selected minimiser. -/
def nonDegenerateAblationLaw {Prior Policy : Type*} (policies : List Policy)
    (grade pragmatic : Prior → Policy → ℝ) :
    ∃ prior πGrade πPragmatic,
      IsArgminOn policies (grade prior) πGrade ∧
      IsArgminOn policies (pragmatic prior) πPragmatic ∧
      πGrade ≠ πPragmatic := sorry

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

/-- HOLE · owner: P-validated-R5 §3e find · holder: by-record · evidence: REFUSED — this is an implementation, not a law · falsifier: REFUSED for the same reason · Find maps a structured tension and repository to selected patterns, receipts, or typed absence. -/
def find {State P : Type*} : Tension State → Repository P → FindResult P := sorry

/-- HOLE · owner: P-validated-R5 §3e F1 · holder: by-record · evidence: FindReceiptTable · falsifier: a selected pattern is outside the repository, or empty selection has no typed absence · Find returns only repository patterns and records typed absence when selection is empty. -/
def findF1Containment :
  ∀ {State P : Type*} (tension : Tension State) (repo : Repository P),
    (find tension repo).selected ⊆ repo.patterns ∧
    ((find tension repo).selected = ∅ →
      (find tension repo).absence = some .noPatternAddressesThisTension) := sorry

/-- HOLE · owner: P-validated-R5 §3e F2 · holder: by-record · evidence: FindReceiptTable · falsifier: a selected pattern has no receipt · Every selected pattern carries a receipt. -/
def findF2Receipted :
  ∀ {State P : Type*} (tension : Tension State) (repo : Repository P) p,
    p ∈ (find tension repo).selected →
      ∃ receipt, (find tension repo).receipts p = some receipt := sorry

/-- HOLE · owner: P-validated-R5 §3e F3 · holder: by-record · evidence: FindReceiptTable · falsifier: a selected pattern has only score evidence · Every receipt cites text or authored edges and is never justified by a score alone. -/
def findF3NonSelfCertifying :
  ∀ {State P : Type*} (tension : Tension State) (repo : Repository P) p,
    p ∈ (find tension repo).selected →
      ∃ receipt, (find tension repo).receipts p = some receipt ∧
        receipt.nonSelfCertifying := sorry

/-- HOLE · owner: P-validated-R5 §3e F4 · holder: by-record · evidence: FindReceiptTable · falsifier: a scenario has no zero-mass repository pattern · Every tension has a repository pattern that find does not return. -/
def findF4Falsifiable :
  ∀ {State P : Type*} (tension : Tension State) (repo : Repository P),
    ∃ p, p ∈ repo.patterns ∧ p ∉ (find tension repo).selected := sorry

inductive ReachOutside {P : Type*} (selected : Set P) (standsOn : P → P → Prop) : P → P → Prop
  | direct {u v} : standsOn u v → ReachOutside selected standsOn u v
  | through {u x v} : ReachOutside selected standsOn u x → x ∉ selected →
      standsOn x v → ReachOutside selected standsOn u v

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O3 · holder: by-record · Fast-forward connects selected endpoints through authored paths whose intermediate vertices are unselected. -/
def fastForward {P : Type*} (selected : Set P) (standsOn : P → P → Prop)
    (u v : P) : Prop :=
  u ∈ selected ∧ v ∈ selected ∧ ReachOutside selected standsOn u v

structure CascadeDiff (P Score : Type*) where
  selected : Set P
  nodes : Set P
  addedByOrganise : Set P
  authoredEdges : P → P → Prop
  organisedEdges : P → P → Prop
  precedenceBefore : List P
  precedenceAfter : List P
  actingOrderBefore : List P
  actingOrderAfter : List P
  scoreBefore : Score
  scoreAfter : Score

/-- HOLE · owner: P-validated-R5 §3e organise · holder: by-record · evidence: REFUSED — this is an implementation, not a law · falsifier: REFUSED for the same reason · Organise turns selected patterns and authored relations into a cascade. -/
def organise {P : Type*} : Set P → Repository P → Cascade P := sorry

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

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O1 · holder: by-record · evidence: CascadeDiff · falsifier: nodes differ from selected union recorded additions · SCOPE AMENDMENT 2026-08-31: formerly a universal claim about refused `organise`; now the witnessed C59 instance only. -/
def organiseO1NodesRecorded :
    wmCascadeDiffFixture.nodes =
      wmCascadeDiffFixture.selected ∪ wmCascadeDiffFixture.addedByOrganise := by
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

/-- HOLE · owner: P-R9 §solved 3 (claude-13's load-bearing lemma, ratified 2026-08-30) · holder: by-record · evidence: a proof term · falsifier: `independenceVerdict` decides membership itself and ignores `decide?` · The checker argument is load-bearing: there is an UNSOUND `decide?` under which a self-producer is judged `independent` — so a wrong checker can be detected, and the Lean definition does not bypass its own argument. -/
def r9VerdictConsultsChecker :
  ∀ {Part : Type*} [DecidableEq Part] (claim : Claim Part) (w : Witness Part),
    w.producer ∈ claim.producingPart →
    ∃ decide? : Part → Set Part → Bool,
      ¬ (∀ p S, decide? p S = true ↔ p ∈ S) ∧
      independenceVerdict (some claim) w decide? = .independent := sorry

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

/-- HOLE · owner: P-R9 §solved 3 (falsifier) · holder: by-record · evidence: wmVerdictsDeclared · falsifier: a row with inDeclaredPart = true judged independent · The shipped checker's recorded verdicts are sound. Moves by `decide` once the table is transcribed; false if the checker is broken. -/
def r9WmVerdictsSound : r9VerdictsSound wmVerdictsDeclared := sorry

/-- HOLE · owner: P-R9 §solved 2 (per-row declarations) · holder: by-record · evidence: wmVerdictsDeclared · falsifier: a named-agent row under the paper's sentence, or an unnamed row under row text · The run-(ii) table's declaration sources are per-row in fact. -/
def r9WmPerRowDeclarations : r9PerRowDeclarations wmVerdictsDeclared := sorry

/-- HOLE · owner: P-R9 §solved 2 (the two runs, R9-D1b) · holder: by-record · evidence: both tables · falsifier: run (i) not all `unknown`; run (ii) any row ≠ `self` under the declaration that places commissioned agents inside the author's part — the three named-agent rows (O7, O14, O15) are where this can fail · Registered: 13 unknown / 13 self. -/
def r9TwoRunCensus :
    wmVerdictsLedgerAlone.length = 13 ∧ wmVerdictsDeclared.length = 13 ∧
    (∀ r ∈ wmVerdictsLedgerAlone, r.verdict = .unknown) ∧
    (∀ r ∈ wmVerdictsDeclared, r.verdict = .self) := sorry

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

/-- CLOSED-BY-RECORD · owner: P-R2 §solved 1 (Channel) · holder: by-record · The fourteen declared channels as NAMED constructors in declaration order (`observation.clj:18–32`) — identity and order, not arity (claude-13's R2-D2 read via claude-20, ratified 2026-08-30: `Fin 14` could not say "these names in this order"; falsifier: a fifteenth key in any tick). -/
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

/-- HOLE · owner: P-R2 §solved 1 (fixture) · holder: by-record · evidence: the corpus itself, transcribed · falsifier: digest ≠ the content pin stated in P-R8/P-R2 · The 792 wm-trace forms as a Lean literal — filled by the adapter from the run, never by hand. -/
def wmTraceR2 : List R2TickLit := sorry

/-- HOLE · owner: P-R2 §solved 1 · holder: by-record · evidence: IllFormedList (the failing tick ids) · falsifier: the census over the transcribed corpus is not 2 · Against the declared 14 channels the census is 2 (the two 05-18 records). Stated about the FIXTURE CONSTANT, not a universally bound corpus (family fix, 2026-08-30: a ∀-corpus form is false for every other list). Moves by `decide` once `wmTraceR2` is transcribed. -/
def r2ContractCensusWmTrace :
    r2ContractCensus wmTraceR2 (fun tick => Channel.all.all (fun c => (tick.observation c).isSome)) = 2 := sorry

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

/-- HOLE · owner: P-R8 §solved 1 (fixture) · holder: by-record · evidence: the corpus itself, transcribed · falsifier: the digest recomputed by the method stated in P-R8 §content-pin (`:sha256-over-newline-joined-sorted-form-sha256`, published by `checks/r8_f_contract.clj`) differs from the value recorded there for the same 53 files / 792 forms — today `c9add16a…`; a value without its method is not a pin (claude-20 / codex-12, 2026-08-30) · The 792 forms as a Lean literal — filled by the adapter from the run. -/
def wmTraceR8 : List R8TickLit := sorry

/-- HOLE · owner: P-R8 §solved 1 (census) · holder: by-record · evidence: the triple with tick ids per disposition · falsifier: the census over the transcribed corpus is not (755, 32, 5) · Stated about the fixture constant (family fix, 2026-08-30). Moves by `decide` once `wmTraceR8` is transcribed. -/
def r8CensusWmTrace : r8Census wmTraceR8 = (755, 32, 5) := sorry

/-- HOLE · owner: P-R8 §solved 1 (iii), by era · holder: by-record · evidence: EraTable · falsifier: a post-boundary form without stored F, or a pre-boundary form with one (non-interleaving fails) · CORRECTED 2026-08-30 (claude-13 via claude-20): `:free-energy`, `:variational-free-energy` and `:selection-gain` are three keys of ONE unconditional map literal (`war_machine.clj:4664–4687`), so conjuncts 1–2 are a write-site identity, not two facts; the only CONTINGENT conjunct is 3 — the stored-F forms are a contiguous date suffix (non-interleaving), and since the boundary 20260714 was read off the data, "0 violations at that boundary" tests contiguity, not the date. Precision scale remains the proximate driver of the F gap; cause untested. -/
def r8EraBoundary :
    ∀ t ∈ wmTraceR8,
      (t.storedF.isSome ↔ t.selectionGain.isSome) ∧
      (t.storedF.isSome ↔ t.freeEnergyShape = .controllerMap) ∧
      (t.storedF.isSome ↔ 20260714 ≤ t.fileDate) := sorry

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

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:21–29 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · `Q(o∣π)` is a normalized finite-support predictive distribution over vertex-tagged outcomes for each policy. -/
abbrev PredictiveOutcomeKernel (PolicyIndex : Type*) (Obs : Vertex → Type*) :=
  ProbabilityKernel PolicyIndex (Outcome Obs)

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:29 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · `Q(θ∣π)` is the normalized parameter prior predicted by a policy. -/
abbrev ParameterPriorKernel (PolicyIndex Parameter : Type*) :=
  ProbabilityKernel PolicyIndex Parameter

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:29 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · `Q(θ∣o,π)` is the normalized parameter posterior conditioned jointly on the observed outcome and policy. -/
abbrev ParameterPosteriorKernel (PolicyIndex : Type*) (Obs : Vertex → Type*)
    (Parameter : Type*) :=
  ProbabilityKernel (PolicyIndex × Outcome Obs) Parameter

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:7 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · The controlled state transition `B : S×U ⇝ S`. -/
abbrev TransitionKernel (State Action : Type*) :=
  ProbabilityKernel (State × Action) State

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:7,37 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · The normalized policy prior `E : 1 ⇝ Π`. -/
abbrev PolicyPriorKernel (PolicyIndex : Type*) :=
  ProbabilityKernel Unit PolicyIndex

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:21–23 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · Preferred outcomes `C` as a normalized distribution, distinct from the existing vertex-local pragmatic cost function. -/
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

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:27 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · The observation model is a finite-support Markov kernel A : S ⇝ O; normalisation is a field, not an external shape check. -/
abbrev observationKernel (State Observation : Type*) := ProbabilityKernel State Observation

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:9 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · Every channel carries both its posterior mean and a nonnegative variance. -/
structure BeliefState where
  mean : Channel → ℝ
  variance : Channel → NonnegativeReal

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:15 · P-glossary-mathematics · holder: by-record · Prediction error is ε_k := o_k - μ_k. -/
def predictionError (observation beliefMean : Channel → ℝ) : Channel → ℝ :=
  fun k => observation k - beliefMean k

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:17 · P-glossary-mathematics · holder: by-record · Precision is a nonnegative channel-indexed weight. -/
abbrev PrecisionMap := Channel → NonnegativeReal

/-- Per-tick precision-weighted prediction error.  This is not expected free
energy and is not the evidence change used by Bayesian model reduction. -/
structure VariationalFreeEnergyValue where
  value : ℝ

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:19 · P-glossary-mathematics · holder: by-record · F = ½ · mean_k (Π_k · ε_k²), over Channel.all. -/
def variationalFreeEnergy (precision error : Channel → ℝ) : VariationalFreeEnergyValue :=
  ⟨(1 / 2 : ℝ) *
    ((Channel.all.map fun k => precision k * (error k) ^ 2).foldl (· + ·) 0 /
      Channel.all.length)⟩

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:27 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · The computed mass of a kernel row; `ProbabilityKernel.normalised` proves it is one. -/
def observationKernelRowMass {State Observation : Type*}
    (A : observationKernel State Observation) (s : State) : ℝ :=
  ((A.support s).map (A.mass s)).sum

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:9,15,17,19,27 · P-glossary-mathematics · holder: by-record · decided 2026-08-31 · The posterior applies the precision-weighted prediction-error correction and an evidence-weighted EMA of squared error plus sensor-noise floor. `none` is loud unknown provenance: both mean and variance pass through. Defaults remain external parameters recorded by C32. -/
def beliefUpdate (learningRate sensorNoiseFloor : NonnegativeReal)
    (evidenceWeight : Channel → Option NonnegativeReal)
    (A : observationKernel Channel Channel) (prior : BeliefState)
    (observation : Channel → ℝ) (precision : PrecisionMap)
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

/-- The risk term `KL[Q(o∣π)‖C]`, over the predictive kernel's declared finite
support.  Strict positivity of `C` on that support keeps the real-valued formula
inside its domain; a zero preferred mass would require an extended-real score. -/
def predictiveOutcomeRisk {PolicyIndex : Type*} {Obs : Vertex → Type*}
    (Q : PredictiveOutcomeKernel PolicyIndex Obs) (Cdist : PreferenceDistribution Obs)
    (_positivePreference : ∀ π o, o ∈ Q.support π → 0 < Cdist.mass () o)
    (π : PolicyIndex) : ℝ :=
  (Q.support π).map (fun o => Q.mass π o * Real.log (Q.mass π o / Cdist.mass () o)) |>.sum

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:21–25 · P-glossary-mathematics · holder: by-record · evidence: ExpectedFreeEnergyWitness · falsifier: the supplied risk-plus-ambiguity value disagrees with the kernel-derived value · Expected free energy is predictive-outcome risk plus expected ambiguity. -/
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

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:29 · P-glossary-mathematics · holder: by-record · evidence: ExpectedInformationGainWitness · falsifier: posterior-to-prior KL disagrees with recorded EIG · Canonical EIG is the predictive-outcome expectation of posterior-to-prior parameter KL. -/
def expectedInformationGain {PolicyIndex Parameter : Type*} {Obs : Vertex → Type*}
    (Q : PredictiveOutcomeKernel PolicyIndex Obs)
    (prior : ParameterPriorKernel PolicyIndex Parameter)
    (posterior : ParameterPosteriorKernel PolicyIndex Obs Parameter)
    (positivePrior : ∀ π o θ, θ ∈ posterior.support (π, o) → 0 < prior.mass π θ)
    (π : PolicyIndex) : ExpectedInformationGainValue :=
  ⟨(Q.support π).map (fun o =>
      Q.mass π o * parameterInformationGain prior posterior positivePrior π o) |>.sum⟩

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:58 · P-glossary-mathematics · holder: by-record · evidence: LogMultivariateBetaWitness · falsifier: the analytic value disagrees with the Dirichlet normaliser · The logarithm of the Dirichlet normaliser.  Its subtype excludes an empty vector and every zero or negative concentration, where the Dirichlet distribution is not defined. -/
def logMultivariateBeta
    (concentrations : {xs : List ℝ // xs ≠ [] ∧ ∀ x ∈ xs, 0 < x}) : ℝ :=
  (concentrations.val.map fun x => Real.log (Real.Gamma x)).sum -
    Real.log (Real.Gamma concentrations.val.sum)

/-- BMR evidence change between a full and reduced Dirichlet model.  The name
and wrapper prevent composition with per-tick variational F by shared `ℝ`. -/
structure ModelReductionFreeEnergyChange where
  value : ℝ

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:58 · P-glossary-mathematics · holder: by-record · BMR ΔF = ln B(A) + ln B(a′) - ln B(a) - ln B(A′). -/
def modelReductionFreeEnergyChange
    (A aPrime a APrime : {xs : List ℝ // xs ≠ [] ∧ ∀ x ∈ xs, 0 < x}) :
    ModelReductionFreeEnergyChange :=
  ⟨logMultivariateBeta A + logMultivariateBeta aPrime -
    logMultivariateBeta a - logMultivariateBeta APrime⟩

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:60 · P-glossary-mathematics · holder: by-record · A reduction passes exactly when ΔF ≤ -3. -/
def bayesFactorThreshold (change : ModelReductionFreeEnergyChange) : Prop := change.value ≤ -3

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:39 · P-glossary-mathematics · holder: by-record · Q(π) ∝ exp(ln E(π) − G(π)/τ): both the log habit prior and grade term are retained. -/
def softmax {PolicyIndex : Type*} (exp log : ℝ → ℝ)
    (habit : PolicyIndex → ℝ) (grade : PolicyIndex → ExpectedFreeEnergyValue) (tau : ℝ)
    (policies : List PolicyIndex) : List ℝ :=
  let weights := policies.map fun π => exp (log (habit π) - (grade π).value / tau)
  let total := weights.foldl (· + ·) 0
  weights.map fun weight => weight / total

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:54 · P-glossary-mathematics · holder: by-record · BMR re-expresses the old counts under the reduced prior: A′ = A + a′ - a, componentwise. -/
def bayesianModelReduction (A aPrime a : List ℝ) : List ℝ :=
  (A.zip (aPrime.zip a)).map fun x => x.1 + x.2.1 - x.2.2

/-- HOLE · owner: sec-glossary.tex:29 · P-glossary-mathematics · holder: by-record · evidence: REFUSED — canonical EIG is now defined, but no theorem identifies the live aggregate posterior-spread bonus with it · falsifier: REFUSED unless the live bonus is shown equal to outcome-weighted posterior-to-prior KL · The live posterior-spread bonus may not be promoted to canonical EIG. -/
def modelUncertaintyAndEIG : Prop := sorry

/-- CLOSED-BY-RECORD · owner: sec-glossary.tex:48 · P-glossary-mathematics · holder: by-record · π is the pattern-language cascade scored as one policy; the state-to-action result of inference is `DecisionRule`. -/
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

/-- HOLE · owner: P-R19-preferences-open §gate · holder: by-record · evidence: PreferenceStackWitness · falsifier: a C value in a live trace with no layer record behind it · Every running instance's C is the fold of a recorded stack. -/
def preferenceStackLiveRecorded : Prop := sorry

/-- HOLE · owner: P-R19-preferences-open §principle · holder: by-record · evidence: REFUSED — a meta-claim about the spine's definition; no in-language census of free preference constants exists yet · falsifier: REFUSED for the same reason · No preference value is free in the spine; C is a parameter everywhere. -/
def machineHasNoC : Prop := sorry

/-- CLOSED-BY-RECORD · owner: Joe 2026-08-31 ("we should specify that it should be able to run at least once, and then we should get evidence of that") · holder: by-record · What one completed tick leaves behind: the receipt is the evidence, and each field is one of the standing invariants made concrete for a single run. On-demand ticks (run one, like the APM machine's clicks) are first-class; a scheduler is one caller among others. -/
structure TickRunRecord where
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

/-- HOLE · owner: Joe 2026-08-31 · holder: by-record · evidence: TickRunWitness · falsifier: no invocation of the tick entry point completes end-to-end with a TickRunRecord — CURRENTLY FIRING: the standalone entry throws "War Machine requires the shared reason-bearing selector" (AUD-D3 gate blocker), so the machine cannot yet demonstrate one unattended tick · The machine can run at least once on demand, leaving a receipt. -/
def wmRunsOnce : Prop := sorry

/-- CLOSED-BY-RECORD · owner: Joe 2026-08-31 ("a map that assembles and joins appropriately, so we can see exactly what happened as the machine ran, and get evidence that that matched the specification") · holder: by-record · One hop of the route a tick actually took: the tracer tag conj'd onto the flowing map at a node boundary, reassembled pairwise into hops. The wiring diagram (control-map-edges.edn, Figure 4 as data) is the specification the route is judged against. -/
structure RouteHop where
  fromNode : String
  toNode : String
  via : String        -- the function at the boundary
  at_ : String
  deriving DecidableEq

/-- HOLE · owner: Joe 2026-08-31 · holder: by-record · evidence: REFUSED — the measured WM-RUN2 route has six hops absent from Figure 4; naming them `route-measured-undrawn` records disagreement but does not establish conformance · falsifier: the existing non-empty route with undrawn hops · A completed tick's reassembled route is non-empty and every hop is an edge of the wiring specification. -/
def wmRunConformsToWiring : Prop := sorry

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

private def mkRefused (name owner reason : String) : Declaration :=
  {name, kind := .hole, signature := s!"see {name} in the source module", owner,
   holder := "by-record", decided := "2026-08-30", falsifier := some s!"REFUSED: {reason}"}

private def closedDeclarations : List Declaration :=
  ([("predictionError", "sec-glossary.tex:15 · P-glossary-mathematics"),
   ("PrecisionMap", "sec-glossary.tex:17 · P-glossary-mathematics"),
   ("variationalFreeEnergy", "sec-glossary.tex:19 · P-glossary-mathematics"),
   ("modelReductionFreeEnergyChange", "sec-glossary.tex:58 · P-glossary-mathematics"),
   ("bayesFactorThreshold", "sec-glossary.tex:60 · P-glossary-mathematics"),
   ("softmax", "sec-glossary.tex:39 · P-glossary-mathematics"),
   ("bayesianModelReduction", "sec-glossary.tex:54 · P-glossary-mathematics"),
   ("Channel", "P-R2 §solved 1 (Channel)"), ("Pattern", "P-validated-R5 §2.1d"), ("Cascade", "P-validated-R5 §3e"),
   ("Tension", "P-validated-R5 §3e"), ("InformationState", "P-validated-R5 §3d"),
   ("DecisionRule", "P-validated-R5 §3"), ("Outcome", "P-validated-R5 §2a"),
   ("G", "P-validated-R5 §2a′"), ("nonDegenerate", "P-validated-R5 §2a′"),
   ("fastForward", "P-validated-R5 §3e O3"), ("independent", "P-R9 S1"),
   ("IndependenceVerdict", "P-R9 §solved 2"), ("independenceVerdict", "P-R9 §solved 1–2"),
   ("r9CheckerSound", "P-R9 §solved 3"), ("r9VerdictsSound", "P-R9 §solved 3"), ("ShapeTally", "P-R8 §solved 1 (iii) evidence"), ("EraSummary.meanPrecision", "P-R8 §solved 1 (iii) evidence"), ("EraSummary.uniform", "P-R8 §solved 1 (iii) evidence"), ("DeclarationSource", "P-R9 §solved 2 (declaration source)"), ("r9PerRowDeclarations", "P-R9 §solved 2 (per-row declarations)"),
   ("TickRunRecord", "Joe 2026-08-31 · runs-once receipt"), ("RouteHop", "Joe 2026-08-31 · route tracer"),
   ("PreferenceSource", "P-R19-preferences-open §principle"), ("PreferenceLayerRecord", "P-R19-preferences-open §tetrahedron"),
   ("wmPreferenceStack2026_08_30", "R19-preference-stack.edn @ dc1dac8"), ("wmStackDeclaredPurpose", "R19-preference-stack.edn @ dc1dac8"),
   ("preferenceStackRecorded", "P-R19-preferences-open §gate"), ("PreferenceLayer", "P-R19-preferences-open §principle"),
   ("foldC", "P-R19-preferences-open §principle"), ("PreferenceStack", "P-R19-preferences-open §tetrahedron"),
   ("Delivery", "delivery-lifecycle §0.6"), ("Handoff", "delivery-lifecycle §0.10"),
   ("Workflow", "delivery-lifecycle §0.10"), ("r2WellFormed", "P-R2 §solved 1"),
   ("r2ContractCensus", "P-R2 §solved 1"), ("r8Disposition", "P-R8 §solved 1"),
   ("r8Census", "P-R8 §solved 1"),
   ("cascadeGrainPi", "sec-glossary.tex:48 · P-glossary-mathematics"),
   ("observationKernel", "sec-glossary.tex:27 · P-glossary-mathematics"),
   ("BeliefState", "sec-glossary.tex:9 · P-glossary-mathematics"),
   ("observationKernelRowMass", "sec-glossary.tex:27 · P-glossary-mathematics"),
   ("beliefUpdate", "sec-glossary.tex:9,15,17,19,27 · P-glossary-mathematics")].map fun p => mkClosed p.1 p.2)
  ++ [mkClosed "PredictiveOutcomeKernel" "sec-glossary.tex:21–29 · P-glossary-mathematics",
      mkClosed "ParameterPriorKernel" "sec-glossary.tex:29 · P-glossary-mathematics",
      mkClosed "ParameterPosteriorKernel" "sec-glossary.tex:29 · P-glossary-mathematics",
      mkClosed "TransitionKernel" "sec-glossary.tex:7 · P-glossary-mathematics",
      mkClosed "PolicyPriorKernel" "sec-glossary.tex:7,37 · P-glossary-mathematics",
      mkClosed "PreferenceDistribution" "sec-glossary.tex:21–23 · P-glossary-mathematics"]
  ++ [mkClosed "predictiveOutcomeRisk" "sec-glossary.tex:21–23 · P-glossary-mathematics",
      mkClosed "G_eq_expectedFreeEnergy" "sec-glossary.tex:21–25 · P-glossary-mathematics",
      mkClosed "ExpectedInformationGainValue" "sec-glossary.tex:29 · P-glossary-mathematics",
      mkClosed "parameterInformationGain" "sec-glossary.tex:29 · P-glossary-mathematics",
      mkClosed "generativeFactorMass" "sec-glossary.tex:7 · P-glossary-mathematics",
      mkClosed "wmCascadeDiffFixture" "P-validated-R5 §3e O1–O4"]
  ++ [mkWitnessedClosed "logMultivariateBeta" "sec-glossary.tex:58 · P-glossary-mathematics"
      "LogMultivariateBetaWitness" "value disagrees with the Dirichlet normaliser",
      mkWitnessedClosed "expectedFreeEnergy" "sec-glossary.tex:21–25 · P-glossary-mathematics"
      "ExpectedFreeEnergyWitness" "risk-plus-ambiguity disagrees with the kernel-derived value",
      mkWitnessedClosed "expectedInformationGain" "sec-glossary.tex:29 · P-glossary-mathematics"
      "ExpectedInformationGainWitness" "posterior-to-prior KL disagrees with recorded EIG",
      mkWitnessedClosed "GenerativeModel" "sec-glossary.tex:7 · P-glossary-mathematics"
      "GenerativeModelWitness" "joint does not factor into observation, transition, and policy prior",
      mkWitnessedClosed "organiseO1NodesRecorded" "P-validated-R5 §3e O1"
      "CascadeDiff" "nodes mismatch or additions unrecorded",
      mkWitnessedClosed "organiseO2AuthoredReachability" "P-validated-R5 §3e O2"
      "CascadeDiff" "edge lacks authored reachability",
      mkWitnessedClosed "organiseO3FastForward" "P-validated-R5 §3e O3"
      "CascadeDiff" "edges differ from fast-forward",
      mkWitnessedClosed "organiseO4PrecedenceGovernance" "P-validated-R5 §3e O4 and S-G4"
      "CascadeDiff" "precedence changes neither order nor score",
      mkClosed "valueEvidenceRequiresL2" "P-R9 S1"]

private def holeDeclarations : List Declaration :=
  [mkRefused "modelUncertaintyAndEIG" "sec-glossary.tex:29 · P-glossary-mathematics" "no theorem identifies the live aggregate posterior-spread bonus with canonical outcome-weighted posterior-to-prior KL",
   mkRefused "C" "P-validated-R5 §2a" "implementation; no observation selects C",
   mkHole "nonDegenerateAblationLaw" "P-validated-R5 §2a′" "AblationTable" "no prior has moved = true",
   mkRefused "find" "P-validated-R5 §3e find" "implementation, not a law",
   mkHole "findF1Containment" "P-validated-R5 §3e F1" "FindReceiptTable" "selection escapes repository or empty lacks absence",
   mkHole "findF2Receipted" "P-validated-R5 §3e F2" "FindReceiptTable" "selected pattern lacks receipt",
   mkHole "findF3NonSelfCertifying" "P-validated-R5 §3e F3" "FindReceiptTable" "receipt uses score alone",
   mkHole "findF4Falsifiable" "P-validated-R5 §3e F4" "FindReceiptTable" "no zero-mass pattern",
   mkRefused "organise" "P-validated-R5 §3e organise" "implementation, not a law",
   mkHole "r9VerdictConsultsChecker" "P-R9 §solved 3" "proof term" "decision ignores checker",
   mkWitnessedClosed "wmVerdictsLedgerAlone" "P-R9 §solved 2" "VerdictTable" "a fixture row or verdict is absent",
   mkWitnessedClosed "wmVerdictsDeclared" "P-R9 §solved 2" "VerdictTable" "a fixture row or verdict is absent",
   mkHole "r9WmVerdictsSound" "P-R9 §solved 3" "VerdictTable" "self producer judged independent",
   mkHole "r9TwoRunCensus" "P-R9 §solved 2" "VerdictTable" "either thirteen-row census differs",
   mkHole "r9WmPerRowDeclarations" "P-R9 §solved 2 (per-row declarations)" "VerdictTable" "a named-agent row under the paper sentence, or an unnamed row under row text",
   mkHole "wmTraceR2" "P-R2 §solved 1" "List R2TickLit" "fixture digest differs",
   mkHole "r2ContractCensusWmTrace" "P-R2 §solved 1" "IllFormedList" "census is not 2",
   mkHole "wmTraceR8" "P-R8 §solved 1" "List R8TickLit" "fixture digest differs",
   mkHole "r8CensusWmTrace" "P-R8 §solved 1" "R8DispositionEvidence" "triple differs from (755,32,5)",
   mkHole "r8EraBoundary" "P-R8 §solved 1 (iii)" "EraTable" "a form is in neither era",
   mkHole "preferenceStackLiveRecorded" "P-R19-preferences-open §gate" "PreferenceStackWitness" "a C value in a live trace with no layer record behind it",
   mkRefused "machineHasNoC" "P-R19-preferences-open §principle" "meta-claim about the spine; no in-language census of free preference constants yet",
   mkHole "wmRunsOnce" "Joe 2026-08-31 · run-at-least-once" "TickRunWitness" "no tick-entry invocation completes with a TickRunRecord; currently firing (selector-seam blocker)",
   mkRefused "wmRunConformsToWiring" "Joe 2026-08-31 · organisation evidence" "WM-RUN2 contains six measured-undrawn hops, so the existing route refutes conformance"]

def registry : Registry :=
  {schemaVersion := 1, contractId := "wm-holes", moduleName := "DarkTower.WarMachine.Holes",
   declarations := closedDeclarations ++ holeDeclarations}

end
end DarkTower.WarMachine.Holes

def main : IO Unit :=
  DarkTower.Contract.Emit.emit DarkTower.WarMachine.Holes.registry
