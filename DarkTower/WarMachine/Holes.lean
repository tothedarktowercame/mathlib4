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

/-- HOLE · owner: P-R2 §solved 1 · holder: claude-15 · Every tick observation has exactly the declared channel keys. -/
def r2ObservationKeysAreChannels :
  ∀ {Channel Value : Type*} (tick : R2Tick Channel Value),
    {channel | (tick.observation channel).isSome} = Set.univ := sorry

inductive R8Disposition where
  | missingFComputable
  | storedF
  | insufficientInputs
  deriving DecidableEq, Repr

structure R8Tick (Belief Observation Precision : Type*) where
  muPre : Option Belief
  observation : Option Observation
  precision : Option Precision
  storedF : Option ℝ

/-- CLOSED-BY-RECORD · owner: P-R8 §solved 1 · holder: claude-15 · R8 records exactly missing-computable, stored, or insufficient-inputs. -/
def r8Disposition {Belief Observation Precision : Type*}
    (tick : R8Tick Belief Observation Precision) : R8Disposition :=
  match tick.muPre, tick.observation, tick.precision, tick.storedF with
  | some _, some _, some _, none => .missingFComputable
  | some _, some _, some _, some _ => .storedF
  | _, _, _, _ => .insufficientInputs

/-- HOLE · owner: P-R8 §solved 1 · holder: claude-15 · With inputs, stored F agrees with recomputation within epsilon; otherwise the typed disposition says why. -/
def r8StoredFRecomputes :
  ∀ {Belief Observation Precision : Type*}
    (F : Belief → Observation → Precision → ℝ) (ε : ℝ)
    (tick : R8Tick Belief Observation Precision),
    0 ≤ ε →
    match tick.muPre, tick.observation, tick.precision, tick.storedF with
    | some belief, some observation, some precision, some stored =>
        r8Disposition tick = .storedF ∧
          |stored - F belief observation precision| ≤ ε
    | some _, some _, some _, none => r8Disposition tick = .missingFComputable
    | _, _, _, _ => r8Disposition tick = .insufficientInputs := sorry

end DarkTower.WarMachine.Holes
