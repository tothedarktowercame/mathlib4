import Mathlib.Data.Real.Basic
import DarkTower.WarMachine.CascadeOrder
import DarkTower.WarMachine.GainChain

/-!
# Declared holes in the War Machine model

These declarations state decided interfaces without proving or implementing
them.  Supporting records contain only field lists fixed by the cited records.
-/

open Set

universe u v w

namespace DarkTower.WarMachine.Holes

inductive Vertex where
  | people | money | organisations | evidence
  deriving DecidableEq, Repr

inductive Layer where
  | L1 | L2
  deriving DecidableEq, Repr

inductive DeliveryGuarantee where
  | exactlyOnce | atLeastOnce
  deriving DecidableEq, Repr

structure Retry where
  cap : Nat
  sameIdentity : Bool

structure FindResult (Pattern Receipt Absence : Type*) where
  selected : Set Pattern
  receipts : Pattern → Option Receipt
  absence : Option Absence

/-- HOLE · owner: P-validated-R5 §2b Pattern · holder: claude-15 · decided 2026-08-30 · A pattern is a partial production rule from state to an optional action. -/
def Pattern (State Action : Type*) : Type := sorry

/-- HOLE · owner: P-validated-R5 §2b Cascade · holder: claude-15 · decided 2026-08-30 · A cascade is a finite acyclic authored descent graph over patterns. -/
def Cascade (Pattern : Type*) : Type := sorry

/-- HOLE · owner: P-validated-R5 §3d InformationState · holder: claude-15 · decided 2026-08-30 · Information state contains state, history, repository, and tension. -/
def InformationState (State Event Repository Tension : Type*) : Type := sorry

/-- HOLE · owner: P-validated-R5 §3 Policy · holder: claude-15 · decided 2026-08-30 · A policy reads an information state and returns an action. -/
def Policy (InformationState Action : Type*) : Type := sorry

/-- HOLE · owner: P-validated-R5 §2a Outcome · holder: claude-15 · decided 2026-08-30 · An outcome is the vertex-tagged sum of that vertex's observations. -/
def Outcome (Obs : Vertex → Type*) : Type := sorry

/-- HOLE · owner: P-validated-R5 §2a C · holder: claude-15 · decided 2026-08-30 · C assigns a probability distribution only at a pragmatic vertex. -/
def C (Dist : (α : Type u) → Type v) (Obs : Vertex → Type u) (v : Vertex) :
    Dist (Obs v) := sorry

/-- HOLE · owner: P-validated-R5 §2a′ G · holder: claude-15 · decided 2026-08-30 · Policy grade is pragmatic risk minus expected information gain. -/
def G (Policy : Type*) (risk eig : Policy → ℝ) : Policy → ℝ := sorry

/-- HOLE · owner: P-validated-R5 §2a′ nonDegenerate · holder: claude-15 · decided 2026-08-30 · Pragmatic and epistemic rankings disagree and epistemic ablation changes a winner. -/
def nonDegenerate (Policy : Type*) (pragmatic epistemic grade : Policy → ℝ)
    (policies : List Policy) : Prop := sorry

/-- HOLE · owner: P-validated-R5 §3e F1–F4 · holder: claude-15 · decided 2026-08-30 · Find returns only receipted repository patterns, has typed absence, independent warrants, and a zero-mass refusal. -/
def find (Tension Repository Pattern Receipt Absence : Type*) :
    Tension → Repository → FindResult Pattern Receipt Absence := sorry

/-- HOLE · owner: P-validated-R5 §3e O3 · holder: claude-15 · decided 2026-08-30 · Fast-forward restricts authored reachability to selected endpoints while skipped interiors remain unselected. -/
def fastForward {Pattern : Type*} (selected : Set Pattern)
    (standsOn : Pattern → Pattern → Prop) : Pattern → Pattern → Prop := sorry

/-- HOLE · owner: P-validated-R5 §3e O1–O4 · holder: claude-15 · decided 2026-08-30 · Organise records input and added nodes, authored fast-forward edges, acyclicity, and collection-level precedence. -/
def organise (Pattern Repository : Type*) :
    Set Pattern → Repository → Cascade Pattern := sorry

structure Claim (Producer : Type*) where
  producingPart : Set Producer

structure Witness (Producer : Type*) where
  producer : Producer
  layer : Layer

/-- HOLE · owner: P-R9 S1 independent/Layer · holder: claude-15 · decided 2026-08-30 · A witness is independent exactly outside the claim's producing part, and value evidence must be L2. -/
def independent (Producer : Type*) : Claim Producer → Witness Producer → Prop := sorry

structure DeliveryShape (Role Schema Write Key : Type*) where
  «from» : Role
  «to» : Role
  payload : Schema
  guarantee : DeliveryGuarantee
  atomicWith : List Write
  retry : Retry
  timeoutMs : Nat
  idemKey : Key
  receipt : Schema

/-- HOLE · owner: delivery-lifecycle §0.6 Delivery · holder: claude-15 · decided 2026-08-30 · A delivery types sender, receiver, payload, guarantee, atomic writes, retry, timeout, idempotency, and receipt. -/
def Delivery (Role Schema Write Key : Type*) : Type := sorry

structure HandoffShape (Artefact Role Time JobId Deadline Receipt : Type*) where
  artefact : Artefact
  «from» : Role
  «to» : Role
  «at» : Time
  iteration : Nat
  awaiting : List JobId
  deadline : Deadline
  receipt : Receipt

/-- HOLE · owner: delivery-lifecycle §0.10 Handoff · holder: claude-15 · decided 2026-08-30 · A handoff records the artefact, roles, time, iteration, awaited jobs, deadline, and receipt. -/
def Handoff (Artefact Role Time JobId Deadline Receipt : Type*) : Type := sorry

structure WorkflowShape (Role Handoff : Type*) where
  holder : Role
  iteration : Nat
  history : List Handoff

/-- HOLE · owner: delivery-lifecycle §0.10 Workflow · holder: claude-15 · decided 2026-08-30 · Workflow records the present holder and iteration with the complete handoff history. -/
def Workflow (Role Handoff : Type*) : Type := sorry

end DarkTower.WarMachine.Holes
