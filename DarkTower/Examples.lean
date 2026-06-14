import Mathlib
import DarkTower.TypedHole
import DarkTower.Fill
import DarkTower.Comb
import DarkTower.Discharge
import DarkTower.ScopeQuery
import DarkTower.BV

/-!
# DarkTower examples

This file records the by-example payoff for typed holes: the same
`TypedHole`/`Fill` machinery types both a mission and a paper.  These are two
instantiations of one small interface, not two separate theories.

Grounding:
* Mission exemplar: `futon3c/holes/missions/E-mission-head.md`, whose lifecycle
  is read below as a BV sequence of phases and whose scope/organism readings are
  held together by `BV.copar`.
* Paper exemplar: the golden graph for arXiv `0809.2517`, especially the binder
  pattern around "Let `H` be a Hopf algebra".  The ungrounded symbol `H` is a
  typed hole whose answer is the concept `HopfAlgebra`.
* The M-first-flights cascade-to-temporary-gap-to-wiring fold is a useful third
  example for a later file; this pass only records the mission and paper domains.
-/

namespace DarkTower

open CategoryTheory

namespace MissionExample

/-- Phases in the E-mission-head lifecycle. -/
inductive Phase where
  | head
  | identify
  | map
  | derive
  | argue
  | verify
  | instantiate
  | document
  deriving DecidableEq, Repr

/-- The full lifecycle as a BV sequence chain. -/
def lifecycle : BV Phase :=
  BV.seq (BV.atom Phase.head)
    (BV.seq (BV.atom Phase.identify)
      (BV.seq (BV.atom Phase.map)
        (BV.seq (BV.atom Phase.derive)
          (BV.seq (BV.atom Phase.argue)
            (BV.seq (BV.atom Phase.verify)
              (BV.seq (BV.atom Phase.instantiate) (BV.atom Phase.document)))))))

/-- A local three-phase prefix used to witness BV reassociation directly. -/
def headIdentifyMapLeft : BV Phase :=
  BV.seq (BV.seq (BV.atom Phase.head) (BV.atom Phase.identify)) (BV.atom Phase.map)

/-- The reassociated form of `headIdentifyMapLeft`. -/
def headIdentifyMapRight : BV Phase :=
  BV.seq (BV.atom Phase.head) (BV.seq (BV.atom Phase.identify) (BV.atom Phase.map))

/-- The two mission readings held together: scope and organism. -/
inductive Reading where
  | scope
  | organism
  deriving DecidableEq, Repr

/-- Scope and organism are simultaneous readings of the same mission object. -/
def readings : BV Reading :=
  BV.copar (BV.atom Reading.scope) (BV.atom Reading.organism)

/-- The action needed to write an unwritten mission phase. -/
inductive GhostDirection where
  | write
  deriving DecidableEq, Repr

/--
The mission as a typed-hole interface: each phase is a position, and the ghost
phase exposes a direction asking to be written.
-/
def ghostPhaseHole : TypedHole where
  poly :=
    { A := Phase
      B := fun _ => GhostDirection }
  satiety := fun phase =>
    if phase = Phase.document then SatietyGrade.payoff else SatietyGrade.parse

/-- The lifecycle prefix reassociates by BV structural congruence. -/
example : BV.Cong headIdentifyMapLeft headIdentifyMapRight :=
  BV.Cong.seq_assoc (BV.atom Phase.head) (BV.atom Phase.identify) (BV.atom Phase.map)

/-- The ghost document phase is a typed hole. -/
example : ghostPhaseHole.holeType Phase.document = GhostDirection :=
  rfl

/-- The ghost document phase is marked with the hungry/payoff satiety grade. -/
example : ghostPhaseHole.satiety Phase.document = SatietyGrade.payoff := by
  decide

/-- Writing a phase can be read as a one-step structural move. -/
example :
    BV.Step headIdentifyMapLeft headIdentifyMapRight :=
  BV.Step.cong
    (BV.Cong.seq_assoc (BV.atom Phase.head) (BV.atom Phase.identify) (BV.atom Phase.map))

end MissionExample

namespace PaperExample

/-- Symbols appearing in the paper fragment. -/
inductive Symbol where
  | H
  deriving DecidableEq, Repr

/-- Concepts that may ground paper symbols. -/
inductive Concept where
  | HopfAlgebra
  deriving DecidableEq, Repr

/-- Roles in the tiny binder hyperedge. -/
inductive Role where
  | symbol
  | concept
  deriving DecidableEq, Repr

/-- Kinds in the tiny binder store. -/
inductive Kind where
  | binder
  deriving DecidableEq, Repr

/-- Query variables for the paper example. -/
inductive Var where
  | concept
  deriving DecidableEq, Repr

/-- The paper binder signature. -/
def sig : ScopeQuery.Sig where
  Kind := Kind
  Role := Role

instance : DecidableEq sig.Kind := by
  dsimp [sig]
  infer_instance

instance : DecidableEq sig.Role := by
  dsimp [sig]
  infer_instance

/-- The ungrounded paper symbol as a typed hole hungry for a concept. -/
def symbolHole : TypedHole where
  poly :=
    { A := Symbol
      B := fun _ => Concept }
  satiety := fun _ => SatietyGrade.role

/-- The one-edge binder store: the symbol `H` is bound to `HopfAlgebra`. -/
def binderStore : ScopeQuery.Store sig Concept :=
  [⟨Kind.binder,
    [(Role.symbol, Concept.HopfAlgebra), (Role.concept, Concept.HopfAlgebra)]⟩]

/--
The question "which concept grounds `H`?" as a role-keyed query.  Both ends live
in the concept-valued store here; the first end fixes the symbol's current
ungrounded concept slot, and the second asks for the binder concept.
-/
def binderQuery : ScopeQuery.Query sig Concept Var :=
  ⟨Kind.binder,
    [(Role.symbol, Sum.inr Concept.HopfAlgebra), (Role.concept, Sum.inl Var.concept)]⟩

/-- The expected answer binding: `?concept = HopfAlgebra`. -/
def expectedBinding : ScopeQuery.Binding Var Concept
  | Var.concept => some Concept.HopfAlgebra

/-- The discharge polarity for grounding an ungrounded symbol by a binder. -/
def groundingPolarity : DischargeKind :=
  DischargeKind.ungroundedBinder

/-- The symbol `H` is an open typed hole whose direction type is the concept it needs. -/
example : symbolHole.holeType Symbol.H = Concept :=
  rfl

/-- The paper fragment uses the ungrounded-symbol/binder discharge polarity. -/
example : groundingPolarity = DischargeKind.ungroundedBinder :=
  rfl

/-- Filling the identity polynomial with the concept gives the grounded concept back. -/
example : Fill.I.get (Fill.I.mk Concept.HopfAlgebra) = Concept.HopfAlgebra :=
  rfl

/-- The binder-store query returns the expected grounding concept by computation. -/
example : (ScopeQuery.answers binderQuery binderStore).map (fun ρ => ρ Var.concept) =
    [some Concept.HopfAlgebra] :=
  rfl

/-- Equivalently, the single returned binding is the expected fill. -/
example : ScopeQuery.answers binderQuery binderStore = [expectedBinding] :=
  rfl

end PaperExample

end DarkTower
