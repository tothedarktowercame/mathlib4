import Mathlib.Data.Real.Basic
import DarkTower.WarMachine.CascadeOrder

/-!
# War Machine formalisation holes

This module separates vocabulary fixed by the written records from laws that
remain unproved.  `CLOSED-BY-RECORD` declarations transcribe an agreed shape or
definition; `HOLE` declarations name an implementation or proof still owed.
-/

open Set

universe u v w

namespace DarkTower.WarMachine.Holes

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

/-- HOLE · owner: P-validated-R5 §2a · holder: claude-15 · Preferences are declared per PRAGMATIC vertex only — the evidence vertex has no C (review fix: D1b had dropped the vertex index). -/
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

/-- HOLE · owner: P-validated-R5 §2a′ · holder: claude-15 · For some declared prior, removing the epistemic term changes the selected minimiser. -/
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

/-- HOLE · owner: P-validated-R5 §3e find · holder: claude-15 · Find maps a structured tension and repository to selected patterns, receipts, or typed absence. -/
def find {State P : Type*} : Tension State → Repository P → FindResult P := sorry

/-- HOLE · owner: P-validated-R5 §3e F1 · holder: claude-15 · Find returns only repository patterns and records typed absence when selection is empty. -/
def findF1Containment :
  ∀ {State P : Type*} (tension : Tension State) (repo : Repository P),
    (find tension repo).selected ⊆ repo.patterns ∧
    ((find tension repo).selected = ∅ →
      (find tension repo).absence = some .noPatternAddressesThisTension) := sorry

/-- HOLE · owner: P-validated-R5 §3e F2 · holder: claude-15 · Every selected pattern carries a receipt. -/
def findF2Receipted :
  ∀ {State P : Type*} (tension : Tension State) (repo : Repository P) p,
    p ∈ (find tension repo).selected →
      ∃ receipt, (find tension repo).receipts p = some receipt := sorry

/-- HOLE · owner: P-validated-R5 §3e F3 · holder: claude-15 · Every receipt cites text or authored edges and is never justified by a score alone. -/
def findF3NonSelfCertifying :
  ∀ {State P : Type*} (tension : Tension State) (repo : Repository P) p,
    p ∈ (find tension repo).selected →
      ∃ receipt, (find tension repo).receipts p = some receipt ∧
        receipt.nonSelfCertifying := sorry

/-- HOLE · owner: P-validated-R5 §3e F4 · holder: claude-15 · Every tension has a repository pattern that find does not return. -/
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

/-- HOLE · owner: P-validated-R5 §3e organise · holder: claude-15 · Organise turns selected patterns and authored relations into a cascade. -/
def organise {P : Type*} : Set P → Repository P → Cascade P := sorry

/-- HOLE · owner: P-validated-R5 §3e O1 · holder: claude-15 · Cascade nodes are exactly selected nodes plus the separately recorded additions. -/
def organiseO1NodesRecorded :
  ∀ {P : Type*} (selected : Set P) (repo : Repository P),
    (organise selected repo).nodes =
      selected ∪ (organise selected repo).addedByOrganise := sorry

/-- HOLE · owner: P-validated-R5 §3e O2 · holder: claude-15 · Every organised edge is supported by authored reachability. -/
def organiseO2AuthoredReachability :
  ∀ {P : Type*} (selected : Set P) (repo : Repository P) u v,
    (organise selected repo).edges u v → Reach repo.standsOn u v := sorry

/-- HOLE · owner: P-validated-R5 §3e O3 · holder: claude-15 · Organised edges are exactly fast-forwards between selected nodes. -/
def organiseO3FastForward :
  ∀ {P : Type*} (selected : Set P) (repo : Repository P) u v,
    (organise selected repo).edges u v ↔ fastForward selected repo.standsOn u v := sorry

/-- HOLE · owner: P-validated-R5 §3e O4 and S-G4 · holder: claude-15 · The same collection under different precedence changes acting order or score. -/
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

/-- HOLE · owner: P-R9 §solved 3 (falsifier) · holder: claude-15 · evidence: VerdictTable (row, declaration, verdict) · falsifier: some row with producer inside the declared part receives `independent` · The Clojure checker R9-D2 ships is sound in the sense above; if its recorded verdicts show a self-producer judged independent, the checker is broken. -/
def r9WmCheckerSound :
  ∀ {Part : Type*} [DecidableEq Part] (clojureDecide : Part → Set Part → Bool),
    r9CheckerSound clojureDecide := sorry

/-- HOLE · owner: P-R9 §solved 3 (claude-13's load-bearing lemma, ratified 2026-08-30) · holder: claude-15 · evidence: a proof term · falsifier: `independenceVerdict` decides membership itself and ignores `decide?` · The checker argument is load-bearing: there is an UNSOUND `decide?` under which a self-producer is judged `independent` — so a wrong checker can be detected, and the Lean definition does not bypass its own argument. -/
def r9VerdictConsultsChecker :
  ∀ {Part : Type*} [DecidableEq Part] (claim : Claim Part) (w : Witness Part),
    w.producer ∈ claim.producingPart →
    ∃ decide? : Part → Set Part → Bool,
      ¬ (∀ p S, decide? p S = true ↔ p ∈ S) ∧
      independenceVerdict (some claim) w decide? = .independent := sorry

/-- HOLE · owner: P-R9 §solved 2 (the two runs, R9-D1b) · holder: claude-15 · Over the thirteen closed rows of OBLIGATIONS.md@6c288174: run (i), ledger alone (no declaration) → all `unknown`; run (ii), the paper's own admission as the declaration (sec-discussion.tex:238) → all `self`. The gap is the node's finding. -/
def r9TwoRunCensus :
  ∀ {Part : Type*} [DecidableEq Part] (rows : List (Witness Part))
    (paperDeclaration : Claim Part) (decide? : Part → Set Part → Bool),
    rows.length = 13 →
    (∀ w ∈ rows, independenceVerdict none w decide? = .unknown) ∧
    (∀ w ∈ rows, independenceVerdict (some paperDeclaration) w decide? = .self) := sorry

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

/-- HOLE · owner: P-R2 §solved 1 · holder: claude-15 · evidence: IllFormedList (the failing tick ids) · falsifier: the census is not 2 · On wm-trace (53 files, 792 forms, filter stated in P-R2) the census against the declared 14-channel list is 2 — the two 05-18 records; the run is the fixture and this CAN be false. -/
def r2ContractCensusWmTrace :
  ∀ {Channel Value : Type*} (declared : List Channel) (wmTrace : List (R2Tick Channel Value))
    (wellFormed? : R2Tick Channel Value → Bool)
    (_sound : ∀ tick, wellFormed? tick = true ↔ r2WellFormed declared tick),
    r2ContractCensus wmTrace wellFormed? = 2 := sorry

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

/-- HOLE · owner: P-R8 §solved 1 (census) · holder: claude-15 · evidence: the triple with tick ids per disposition · falsifier: the triple is not (755, 32, 5) · On wm-trace (filter stated in P-R8) the census is 755 / 32 / 5 over 792 forms; the run is the fixture and this CAN be false. -/
def r8CensusWmTrace :
  ∀ {Errors Precision Gain : Type*} (wmTrace : List (R8Tick Errors Precision Gain)),
    wmTrace.length = 792 → r8Census wmTrace = (755, 32, 5) := sorry

/-- HOLE · owner: P-R8 §solved 1 (iii), by era · holder: claude-15 · Four facts co-move at one boundary: a form stores F ↔ it carries `:selection-gain` ↔ its `:free-energy` is the controller map ↔ its file date ≥ the boundary (2026-07-14). Precision scale is the proximate driver of the F gap and is NOT stated here; cause is untested. The stored-F recompute identity (the earlier hole here) is tautological on this corpus and was retired as evidence on 2026-08-30. -/
def r8EraBoundary :
  ∀ {Errors Precision Gain : Type*} (corpus : List (R8Tick Errors Precision Gain)) (boundary : Nat),
    ∀ t ∈ corpus,
      (t.storedF.isSome ↔ t.selectionGain.isSome) ∧
      (t.storedF.isSome ↔ t.freeEnergyShape = .controllerMap) ∧
      (t.storedF.isSome ↔ boundary ≤ t.fileDate) := sorry

end DarkTower.WarMachine.Holes
