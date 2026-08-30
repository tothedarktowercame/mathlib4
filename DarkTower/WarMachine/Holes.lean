import Mathlib.Data.Real.Basic
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

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §2.1d · holder: claude-15 · decided 2026-08-30 · A pattern has an antecedent and a guarded consequent. -/
structure Pattern (State Action : Type*) where
  fires : State → Prop
  «then» : State → Option Action

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e · holder: claude-15 · decided 2026-08-30 · A cascade records its nodes, authored organisation additions, edges, acyclicity, and precedence. -/
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

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e · holder: claude-15 · A tension is a context with a want and a however (review fix: D1b had only the context). -/
structure Tension (State : Type*) where
  context : State
  want : Prop
  however : Prop

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3d · holder: claude-15 · decided 2026-08-30 · Information state is exactly state, history, repository, and tension. -/
structure InformationState (State History Repo Tension : Type*) where
  state : State
  history : History
  repo : Repo
  tension : Tension

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3 · holder: claude-15 · A policy reads an information state and chooses an action. -/
abbrev Policy (InformationState Action : Type*) := InformationState → Action

inductive Vertex where
  | people
  | money
  | organisations
  | evidence
  deriving DecidableEq, Repr

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §2a · holder: claude-15 · An outcome is an observation indexed by its vertex. -/
abbrev Outcome (Obs : Vertex → Type*) := Sigma Obs

/-- HOLE · owner: P-validated-R5 §2a · holder: claude-15 · evidence: REFUSED — this is an implementation, not a law, and the record fixes no observation that selects C · falsifier: REFUSED for the same reason · Preferences are declared per PRAGMATIC vertex only. -/
def C {Obs : Vertex → Type*} (v : Vertex) (_pragmatic : v ≠ Vertex.evidence) : Obs v → ℝ := sorry

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §2a′ · holder: claude-15 · Policy grade is pragmatic risk minus epistemic gain. -/
def G {Policy : Type*} (risk eig : Policy → ℝ) : Policy → ℝ :=
  fun π => risk π - eig π

def IsArgminOn {Policy : Type*} (policies : List Policy)
    (score : Policy → ℝ) (π : Policy) : Prop :=
  π ∈ policies ∧ ∀ ρ ∈ policies, score π ≤ score ρ

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §2a′ · holder: claude-15 · Non-degeneracy requires disagreement between the terms and a changed minimiser after ablation. -/
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

/-- HOLE · owner: P-validated-R5 §2a′ · holder: claude-15 · evidence: AblationTable · falsifier: no prior has moved = true · For some declared prior, removing the epistemic term changes the selected minimiser. -/
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

/-- HOLE · owner: P-validated-R5 §3e find · holder: claude-15 · evidence: REFUSED — this is an implementation, not a law · falsifier: REFUSED for the same reason · Find maps a structured tension and repository to selected patterns, receipts, or typed absence. -/
def find {State P : Type*} : Tension State → Repository P → FindResult P := sorry

/-- HOLE · owner: P-validated-R5 §3e F1 · holder: claude-15 · evidence: FindReceiptTable · falsifier: a selected pattern is outside the repository, or empty selection has no typed absence · Find returns only repository patterns and records typed absence when selection is empty. -/
def findF1Containment :
  ∀ {State P : Type*} (tension : Tension State) (repo : Repository P),
    (find tension repo).selected ⊆ repo.patterns ∧
    ((find tension repo).selected = ∅ →
      (find tension repo).absence = some .noPatternAddressesThisTension) := sorry

/-- HOLE · owner: P-validated-R5 §3e F2 · holder: claude-15 · evidence: FindReceiptTable · falsifier: a selected pattern has no receipt · Every selected pattern carries a receipt. -/
def findF2Receipted :
  ∀ {State P : Type*} (tension : Tension State) (repo : Repository P) p,
    p ∈ (find tension repo).selected →
      ∃ receipt, (find tension repo).receipts p = some receipt := sorry

/-- HOLE · owner: P-validated-R5 §3e F3 · holder: claude-15 · evidence: FindReceiptTable · falsifier: a selected pattern has only score evidence · Every receipt cites text or authored edges and is never justified by a score alone. -/
def findF3NonSelfCertifying :
  ∀ {State P : Type*} (tension : Tension State) (repo : Repository P) p,
    p ∈ (find tension repo).selected →
      ∃ receipt, (find tension repo).receipts p = some receipt ∧
        receipt.nonSelfCertifying := sorry

/-- HOLE · owner: P-validated-R5 §3e F4 · holder: claude-15 · evidence: FindReceiptTable · falsifier: a scenario has no zero-mass repository pattern · Every tension has a repository pattern that find does not return. -/
def findF4Falsifiable :
  ∀ {State P : Type*} (tension : Tension State) (repo : Repository P),
    ∃ p, p ∈ repo.patterns ∧ p ∉ (find tension repo).selected := sorry

inductive ReachOutside {P : Type*} (selected : Set P) (standsOn : P → P → Prop) : P → P → Prop
  | direct {u v} : standsOn u v → ReachOutside selected standsOn u v
  | through {u x v} : ReachOutside selected standsOn u x → x ∉ selected →
      standsOn x v → ReachOutside selected standsOn u v

/-- CLOSED-BY-RECORD · owner: P-validated-R5 §3e O3 · holder: claude-15 · Fast-forward connects selected endpoints through authored paths whose intermediate vertices are unselected. -/
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

/-- HOLE · owner: P-validated-R5 §3e organise · holder: claude-15 · evidence: REFUSED — this is an implementation, not a law · falsifier: REFUSED for the same reason · Organise turns selected patterns and authored relations into a cascade. -/
def organise {P : Type*} : Set P → Repository P → Cascade P := sorry

/-- HOLE · owner: P-validated-R5 §3e O1 · holder: claude-15 · evidence: CascadeDiff · falsifier: nodes differ from selected union recorded additions · Cascade nodes are exactly selected nodes plus the separately recorded additions. -/
def organiseO1NodesRecorded :
  ∀ {P : Type*} (selected : Set P) (repo : Repository P),
    (organise selected repo).nodes =
      selected ∪ (organise selected repo).addedByOrganise := sorry

/-- HOLE · owner: P-validated-R5 §3e O2 · holder: claude-15 · evidence: CascadeDiff · falsifier: an organised edge lacks authored reachability · Every organised edge is supported by authored reachability. -/
def organiseO2AuthoredReachability :
  ∀ {P : Type*} (selected : Set P) (repo : Repository P) u v,
    (organise selected repo).edges u v → Reach repo.standsOn u v := sorry

/-- HOLE · owner: P-validated-R5 §3e O3 · holder: claude-15 · evidence: CascadeDiff · falsifier: organised edges differ from selected-endpoint fast-forwards · Organised edges are exactly fast-forwards between selected nodes. -/
def organiseO3FastForward :
  ∀ {P : Type*} (selected : Set P) (repo : Repository P) u v,
    (organise selected repo).edges u v ↔ fastForward selected repo.standsOn u v := sorry

/-- HOLE · owner: P-validated-R5 §3e O4 and S-G4 · holder: claude-15 · evidence: CascadeDiff · falsifier: changed precedence changes neither acting order nor score · The same collection under different precedence changes acting order or score. -/
def organiseO4PrecedenceGovernance {P Score : Type*}
    (actingOrder : Cascade P → List P) (score : Cascade P → Score) :
    ∃ c₁ c₂ : Cascade P,
      c₁.nodes = c₂.nodes ∧ c₁.addedByOrganise = c₂.addedByOrganise ∧
      c₁.edges = c₂.edges ∧ c₁.precedence ≠ c₂.precedence ∧
      (actingOrder c₁ ≠ actingOrder c₂ ∨ score c₁ ≠ score c₂) := sorry

inductive Layer where
  | L1
  | L2
  deriving DecidableEq, Repr

structure Claim (Part : Type*) where
  producingPart : Set Part

structure Witness (Part : Type*) where
  producer : Part
  layer : Layer

/-- CLOSED-BY-RECORD · owner: P-R9 S1 · holder: claude-15 · Independence means the witness producer is outside the claim's producing part. -/
def independent {Part : Type*} (claim : Claim Part) (witness : Witness Part) : Prop :=
  witness.producer ∉ claim.producingPart

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 2 · holder: claude-15 · The verdict is three-valued: `unknown` is a value, not the absence of one (claude-20's proposal, ratified 2026-08-30 — run (i) against the ledger alone returns `unknown` for all thirteen). -/
inductive IndependenceVerdict where
  | independent
  | self
  | unknown
  deriving DecidableEq, Repr

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 1–2 · holder: claude-15 · The decision procedure: no declared producing part → `unknown`; producer inside it → `self`; outside → `independent`. `producingPart` is DECLARED (a cited declaration record), never inferred. -/
def independenceVerdict {Part : Type*} [DecidableEq Part]
    (declared : Option (Claim Part)) (witness : Witness Part)
    (decide? : Part → Set Part → Bool) : IndependenceVerdict :=
  match declared with
  | none => .unknown
  | some claim => if decide? witness.producer claim.producingPart then .self else .independent

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 3 · holder: claude-15 · What it means for a membership checker to be SOUND for verdicts: a witness whose producer is inside the declared part is never judged `independent`, and `independent` is returned only when the Prop holds. Stated as a predicate on a GIVEN checker — no soundness hypothesis, so it can be false of a broken one (review fix, same family as r2ContractCensus: the earlier form assumed `_sound` and could not fail). -/
def r9CheckerSound {Part : Type*} [DecidableEq Part] (decide? : Part → Set Part → Bool) : Prop :=
  ∀ (claim : Claim Part) (witness : Witness Part),
    (witness.producer ∈ claim.producingPart →
      independenceVerdict (some claim) witness decide? ≠ .independent) ∧
    (independenceVerdict (some claim) witness decide? = .independent → independent claim witness)

/-- HOLE · owner: P-R9 §solved 3 (claude-13's load-bearing lemma, ratified 2026-08-30) · holder: claude-15 · evidence: a proof term · falsifier: `independenceVerdict` decides membership itself and ignores `decide?` · The checker argument is load-bearing: there is an UNSOUND `decide?` under which a self-producer is judged `independent` — so a wrong checker can be detected, and the Lean definition does not bypass its own argument. -/
def r9VerdictConsultsChecker :
  ∀ {Part : Type*} [DecidableEq Part] (claim : Claim Part) (w : Witness Part),
    w.producer ∈ claim.producingPart →
    ∃ decide? : Part → Set Part → Bool,
      ¬ (∀ p S, decide? p S = true ↔ p ∈ S) ∧
      independenceVerdict (some claim) w decide? = .independent := sorry

/-- Fixture scaffolding: one recorded verdict row of the shipped checker — which row, which declaration source it was judged under, whether the closer named by that declaration is inside the declared producing part, and the verdict. -/
structure VerdictRow where
  row : String
  declarationSource : String      -- "paper:sec-discussion.tex:238" or "row-text:O14"
  inDeclaredPart : Bool
  verdict : IndependenceVerdict
  deriving DecidableEq, Repr

abbrev VerdictTable := List VerdictRow

/-- CLOSED-BY-RECORD · owner: P-R9 §solved 3 · holder: claude-15 · Soundness of a RECORDED table: no row whose closer is inside the declared part is judged `independent`; a row judged `independent` has its closer outside. Decidable; false exactly when the checker is broken. (Replaces r9WmCheckerSound, which quantified over every checker and was false for `fun _ _ => false` — claude-13, 2026-08-30, fourth member of the family.) -/
def r9VerdictsSound (table : VerdictTable) : Prop :=
  ∀ r ∈ table, (r.inDeclaredPart = true → r.verdict ≠ .independent) ∧
               (r.verdict = .independent → r.inDeclaredPart = false)

/-- HOLE · owner: P-R9 §solved 2 (fixture) · holder: claude-15 · evidence: the VerdictTable the R9-D2 run writes (run (i): 13 rows, ledger alone; run (ii): 13 rows, per-row declarations) · falsifier: a row missing or a verdict absent · Transcribed from the run by the adapter. -/
def wmVerdictsLedgerAlone : VerdictTable := sorry
/-- HOLE · owner: P-R9 §solved 2 (fixture) · holder: claude-15 · evidence: VerdictTable · falsifier: a row missing or a verdict absent · The declared-part run transcribed by the adapter. -/
def wmVerdictsDeclared : VerdictTable := sorry

/-- HOLE · owner: P-R9 §solved 3 (falsifier) · holder: claude-15 · evidence: wmVerdictsDeclared · falsifier: a row with inDeclaredPart = true judged independent · The shipped checker's recorded verdicts are sound. Moves by `decide` once the table is transcribed; false if the checker is broken. -/
def r9WmVerdictsSound : r9VerdictsSound wmVerdictsDeclared := sorry

/-- HOLE · owner: P-R9 §solved 2 (the two runs, R9-D1b) · holder: claude-15 · evidence: both tables · falsifier: run (i) not all `unknown`; run (ii) any row ≠ `self` under the declaration that places commissioned agents inside the author's part — the three named-agent rows (O7, O14, O15) are where this can fail · Registered: 13 unknown / 13 self. -/
def r9TwoRunCensus :
    wmVerdictsLedgerAlone.length = 13 ∧ wmVerdictsDeclared.length = 13 ∧
    (∀ r ∈ wmVerdictsLedgerAlone, r.verdict = .unknown) ∧
    (∀ r ∈ wmVerdictsDeclared, r.verdict = .self) := sorry

/-- HOLE · owner: P-R9 S1 · holder: claude-15 · Evidence used to value a policy must be an independent L2 witness. -/
def valueEvidenceRequiresL2 :
  ∀ {Part : Type*} (valueEvidence : Witness Part → Prop) (w : Witness Part),
    valueEvidence w → w.layer = Layer.L2 := sorry

inductive DeliveryGuarantee where
  | exactlyOnce
  | atLeastOnce
  deriving DecidableEq, Repr

structure Retry where
  cap : Nat
  sameIdentity : Bool

/-- CLOSED-BY-RECORD · owner: delivery-lifecycle §0.6 · holder: claude-15 · Delivery := {from, to, payload : Schema, guarantee, atomic-with, retry, timeout-ms, idem-key, receipt : Schema} (review fix: D1b's field list was not the record's). -/
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

/-- CLOSED-BY-RECORD · owner: delivery-lifecycle §0.10 · holder: claude-15 · Handoff := {artefact, from, to, at, iteration, awaiting, deadline, receipt} (review fix: D1b's field list was not the record's). -/
structure Handoff (Artefact Role Time JobId Deadline Receipt : Type*) where
  artefact : Artefact
  «from» : Role
  «to» : Role
  «at» : Time
  iteration : Nat
  awaiting : List JobId
  deadline : Deadline
  receipt : Receipt

/-- CLOSED-BY-RECORD · owner: delivery-lifecycle §0.10 · holder: claude-15 · Workflow := {holder : Role, iteration, history : List Handoff} — provenance is `history` (review fix: D1b had only the list). -/
structure Workflow (Role Handoff : Type*) where
  holder : Role
  iteration : Nat
  history : List Handoff

structure R2Tick (Channel Value : Type*) where
  observation : Channel → Option Value

/-- CLOSED-BY-RECORD · owner: P-R2 §solved 1 · holder: claude-15 · A tick is well-formed against the DECLARED channel list (declaration order, `observation.clj:18–32`) — never against the keys it happens to carry (review fix: the earlier `= Set.univ` form was vacuous or refuted depending on where `Channel` came from; claude-20 2026-08-30). -/
def r2WellFormed {Channel Value : Type*} (declared : List Channel)
    (tick : R2Tick Channel Value) : Prop :=
  ∀ channel, (tick.observation channel).isSome ↔ channel ∈ declared

/-- CLOSED-BY-RECORD · owner: P-R2 §solved 1 · holder: claude-15 · The census is a COMPUTED value: how many ticks of a corpus fail the declared list (review fix, codex-1 via claude-20 2026-08-30: the earlier form universally quantified the answer and was false for every instantiation). -/
def r2ContractCensus {Channel Value : Type*} (corpus : List (R2Tick Channel Value))
    (wellFormed? : R2Tick Channel Value → Bool) : Nat :=
  (corpus.filter (fun tick => !wellFormed? tick)).length

/-- CLOSED-BY-RECORD · owner: P-R2 §solved 1 (Channel) · holder: claude-15 · The fourteen declared channels as NAMED constructors in declaration order (`observation.clj:18–32`) — identity and order, not arity (claude-13's R2-D2 read via claude-20, ratified 2026-08-30: `Fin 14` could not say "these names in this order"; falsifier: a fifteenth key in any tick). -/
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

/-- HOLE · owner: P-R2 §solved 1 (fixture) · holder: claude-15 · evidence: the corpus itself, transcribed · falsifier: digest ≠ the content pin stated in P-R8/P-R2 · The 792 wm-trace forms as a Lean literal — filled by the adapter from the run, never by hand. -/
def wmTraceR2 : List R2TickLit := sorry

/-- HOLE · owner: P-R2 §solved 1 · holder: claude-15 · evidence: IllFormedList (the failing tick ids) · falsifier: the census over the transcribed corpus is not 2 · Against the declared 14 channels the census is 2 (the two 05-18 records). Stated about the FIXTURE CONSTANT, not a universally bound corpus (family fix, 2026-08-30: a ∀-corpus form is false for every other list). Moves by `decide` once `wmTraceR2` is transcribed. -/
def r2ContractCensusWmTrace :
    r2ContractCensus wmTraceR2 (fun tick => Channel.all.all (fun c => (tick.observation c).isSome)) = 2 := sorry

inductive FreeEnergyShape where
  | gMap          -- `:free-energy` holds {:G-total …}         (760 forms, files 05-18 … 07-09)
  | controllerMap -- `:free-energy` holds {:controller-score …} (32 forms, files 07-14 … 07-21, 08-30)
  deriving DecidableEq, Repr

/-- Field names follow the artefact's keys (`:prediction-errors`, `:precision-state`, `:variational-free-energy`, `:selection-gain`), so clause-2 signature comparison against the Clojure census is literal (review fix, claude-20 2026-08-30). -/
structure R8Tick (Errors Precision Gain : Type*) where
  predictionErrors : Option Errors
  precisionState : Option Precision
  storedF : Option ℝ
  selectionGain : Option Gain
  freeEnergyShape : FreeEnergyShape
  fileDate : Nat   -- YYYYMMDD of the trace file

inductive R8Disposition where
  | missingFComputable
  | storedF
  | insufficientInputs
  deriving DecidableEq, Repr

/-- CLOSED-BY-RECORD · owner: P-R8 §solved 1 · holder: claude-15 · R8 records exactly missing-computable, stored, or insufficient-inputs. -/
def r8Disposition {Errors Precision Gain : Type*}
    (tick : R8Tick Errors Precision Gain) : R8Disposition :=
  match tick.predictionErrors, tick.precisionState, tick.storedF with
  | some _, some _, none => .missingFComputable
  | some _, some _, some _ => .storedF
  | _, _, _ => .insufficientInputs

/-- CLOSED-BY-RECORD · owner: P-R8 §solved 1 (census) · holder: claude-15 · The three-disposition census as a COMPUTED triple (same review fix as r2ContractCensus). -/
def r8Census {Errors Precision Gain : Type*} (corpus : List (R8Tick Errors Precision Gain)) :
    Nat × Nat × Nat :=
  ((corpus.filter (fun t => decide (r8Disposition t = R8Disposition.missingFComputable))).length,
   (corpus.filter (fun t => decide (r8Disposition t = R8Disposition.storedF))).length,
   (corpus.filter (fun t => decide (r8Disposition t = R8Disposition.insufficientInputs))).length)

/-- Fixture scaffolding: a wm-trace form as a Lean literal with the fields the R8 laws read. -/
abbrev R8TickLit := R8Tick Unit Unit Unit

/-- HOLE · owner: P-R8 §solved 1 (fixture) · holder: claude-15 · evidence: the corpus itself, transcribed · falsifier: digest ≠ c434950f2e6a7e9b (53 files / 792 forms, content pin) · The 792 forms as a Lean literal — filled by the adapter from the run. -/
def wmTraceR8 : List R8TickLit := sorry

/-- HOLE · owner: P-R8 §solved 1 (census) · holder: claude-15 · evidence: the triple with tick ids per disposition · falsifier: the census over the transcribed corpus is not (755, 32, 5) · Stated about the fixture constant (family fix, 2026-08-30). Moves by `decide` once `wmTraceR8` is transcribed. -/
def r8CensusWmTrace : r8Census wmTraceR8 = (755, 32, 5) := sorry

/-- HOLE · owner: P-R8 §solved 1 (iii), by era · holder: claude-15 · evidence: EraTable · falsifier: a post-boundary form without stored F, or a pre-boundary form with one (non-interleaving fails) · CORRECTED 2026-08-30 (claude-13 via claude-20): `:free-energy`, `:variational-free-energy` and `:selection-gain` are three keys of ONE unconditional map literal (`war_machine.clj:4664–4687`), so conjuncts 1–2 are a write-site identity, not two facts; the only CONTINGENT conjunct is 3 — the stored-F forms are a contiguous date suffix (non-interleaving), and since the boundary 20260714 was read off the data, "0 violations at that boundary" tests contiguity, not the date. Precision scale remains the proximate driver of the F gap; cause untested. -/
def r8EraBoundary :
    ∀ t ∈ wmTraceR8,
      (t.storedF.isSome ↔ t.selectionGain.isSome) ∧
      (t.storedF.isSome ↔ t.freeEnergyShape = .controllerMap) ∧
      (t.storedF.isSome ↔ 20260714 ≤ t.fileDate) := sorry

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

structure EraSummary where
  count : Nat
  storedF : Bool
  selectionGain : Bool
  shape : FreeEnergyShape
  meanPrecision : ℝ

structure EraTable where
  boundary : Nat
  perEra : Era → EraSummary

private def mkClosed (name owner : String) : Declaration :=
  {name, kind := .closed, signature := s!"see {name} in the source module", owner,
   holder := "claude-15", decided := "2026-08-30"}

private def mkHole (name owner evidence falsifier : String) : Declaration :=
  {name, kind := .hole, signature := s!"see {name} in the source module", owner,
   holder := "claude-15", decided := "2026-08-30", evidence := some evidence,
   falsifier := some falsifier}

private def mkRefused (name owner reason : String) : Declaration :=
  {name, kind := .hole, signature := s!"see {name} in the source module", owner,
   holder := "claude-15", decided := "2026-08-30", falsifier := some s!"REFUSED: {reason}"}

private def closedDeclarations : List Declaration :=
  [("Channel", "P-R2 §solved 1 (Channel)"), ("Pattern", "P-validated-R5 §2.1d"), ("Cascade", "P-validated-R5 §3e"),
   ("Tension", "P-validated-R5 §3e"), ("InformationState", "P-validated-R5 §3d"),
   ("Policy", "P-validated-R5 §3"), ("Outcome", "P-validated-R5 §2a"),
   ("G", "P-validated-R5 §2a′"), ("nonDegenerate", "P-validated-R5 §2a′"),
   ("fastForward", "P-validated-R5 §3e O3"), ("independent", "P-R9 S1"),
   ("IndependenceVerdict", "P-R9 §solved 2"), ("independenceVerdict", "P-R9 §solved 1–2"),
   ("r9CheckerSound", "P-R9 §solved 3"), ("r9VerdictsSound", "P-R9 §solved 3"),
   ("Delivery", "delivery-lifecycle §0.6"), ("Handoff", "delivery-lifecycle §0.10"),
   ("Workflow", "delivery-lifecycle §0.10"), ("r2WellFormed", "P-R2 §solved 1"),
   ("r2ContractCensus", "P-R2 §solved 1"), ("r8Disposition", "P-R8 §solved 1"),
   ("r8Census", "P-R8 §solved 1")].map fun p => mkClosed p.1 p.2

private def holeDeclarations : List Declaration :=
  [mkRefused "C" "P-validated-R5 §2a" "implementation; no observation selects C",
   mkHole "nonDegenerateAblationLaw" "P-validated-R5 §2a′" "AblationTable" "no prior has moved = true",
   mkRefused "find" "P-validated-R5 §3e find" "implementation, not a law",
   mkHole "findF1Containment" "P-validated-R5 §3e F1" "FindReceiptTable" "selection escapes repository or empty lacks absence",
   mkHole "findF2Receipted" "P-validated-R5 §3e F2" "FindReceiptTable" "selected pattern lacks receipt",
   mkHole "findF3NonSelfCertifying" "P-validated-R5 §3e F3" "FindReceiptTable" "receipt uses score alone",
   mkHole "findF4Falsifiable" "P-validated-R5 §3e F4" "FindReceiptTable" "no zero-mass pattern",
   mkRefused "organise" "P-validated-R5 §3e organise" "implementation, not a law",
   mkHole "organiseO1NodesRecorded" "P-validated-R5 §3e O1" "CascadeDiff" "nodes mismatch or additions unrecorded",
   mkHole "organiseO2AuthoredReachability" "P-validated-R5 §3e O2" "CascadeDiff" "edge lacks authored reachability",
   mkHole "organiseO3FastForward" "P-validated-R5 §3e O3" "CascadeDiff" "edges differ from fast-forward",
   mkHole "organiseO4PrecedenceGovernance" "P-validated-R5 §3e O4 and S-G4" "CascadeDiff" "precedence changes neither order nor score",
   mkHole "r9VerdictConsultsChecker" "P-R9 §solved 3" "proof term" "decision ignores checker",
   mkHole "wmVerdictsLedgerAlone" "P-R9 §solved 2" "VerdictTable" "a fixture row or verdict is absent",
   mkHole "wmVerdictsDeclared" "P-R9 §solved 2" "VerdictTable" "a fixture row or verdict is absent",
   mkHole "r9WmVerdictsSound" "P-R9 §solved 3" "VerdictTable" "self producer judged independent",
   mkHole "r9TwoRunCensus" "P-R9 §solved 2" "VerdictTable" "either thirteen-row census differs",
   mkHole "valueEvidenceRequiresL2" "P-R9 S1" "WitnessLayerTable" "value evidence uses L1",
   mkHole "wmTraceR2" "P-R2 §solved 1" "List R2TickLit" "fixture digest differs",
   mkHole "r2ContractCensusWmTrace" "P-R2 §solved 1" "IllFormedList" "census is not 2",
   mkHole "wmTraceR8" "P-R8 §solved 1" "List R8TickLit" "fixture digest differs",
   mkHole "r8CensusWmTrace" "P-R8 §solved 1" "R8DispositionEvidence" "triple differs from (755,32,5)",
   mkHole "r8EraBoundary" "P-R8 §solved 1 (iii)" "EraTable" "a form is in neither era"]

def registry : Registry :=
  {schemaVersion := 1, contractId := "wm-holes", moduleName := "DarkTower.WarMachine.Holes",
   declarations := closedDeclarations ++ holeDeclarations}

end DarkTower.WarMachine.Holes

def main : IO Unit :=
  DarkTower.Contract.Emit.emit DarkTower.WarMachine.Holes.registry
