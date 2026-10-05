import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

/-!
# Runtime construction-receipt correspondence

This is the Lean-side carrier for PROOF-2b's runtime receipt.  It deliberately
models the executable claim, not EDN syntax: an adapter must map the pinned
runtime unit and token identities to `Nat`, then prove this predicate for the
decoded value.
-/

namespace DarkTower.WarMachine.ConstructionReceipt

structure UnitSemantics where
  produces : Finset Nat
  needs : Finset Nat
  deriving DecidableEq

structure EdgeWitness where
  source : Nat
  target : Nat
  tokens : Finset Nat
  deriving DecidableEq

structure MeetWitness where
  left : Nat
  right : Nat
  meet : Nat
  leftPath : List EdgeWitness
  rightPath : List EdgeWitness
  deriving DecidableEq

structure Receipt where
  order : List Nat
  support : List EdgeWitness
  meets : List MeetWitness
  precedence : List EdgeWitness
  linearExtension : List Nat
  precedenceViolations : List (Nat × Nat)
  deriving DecidableEq

def position? (order : List Nat) (unit : Nat) : Option Nat :=
  order.idxOf? unit

def edgeValid (semantics : Nat → UnitSemantics) (order : List Nat)
    (edge : EdgeWitness) : Bool :=
  edge.tokens == (semantics edge.source).produces ∩ (semantics edge.target).needs &&
  decide (edge.tokens ≠ ∅) &&
  match position? order edge.source, position? order edge.target with
  | some fromPos, some toPos => fromPos < toPos
  | _, _ => false

def pathConnected (source target : Nat) : List EdgeWitness → Bool
  | [] => source == target
  | first :: rest =>
      first.source == source &&
      ((first :: rest).zipWith (fun left right => left.target == right.source) rest).all id &&
      (rest.getLast?.map (·.target) |>.getD first.target) == target

def pathValid (semantics : Nat → UnitSemantics) (order : List Nat)
    (source target : Nat) (path : List EdgeWitness) : Bool :=
  pathConnected source target path && path.all (edgeValid semantics order)

def meetValid (semantics : Nat → UnitSemantics) (order : List Nat)
    (witness : MeetWitness) : Bool :=
  pathValid semantics order witness.left witness.meet witness.leftPath &&
  pathValid semantics order witness.right witness.meet witness.rightPath

def valid (semantics : Nat → UnitSemantics) (receipt : Receipt) : Bool :=
  decide receipt.order.Nodup &&
  receipt.support.all (edgeValid semantics receipt.order) &&
  receipt.meets.all (meetValid semantics receipt.order) &&
  receipt.precedence == receipt.support &&
  receipt.linearExtension == receipt.order &&
  receipt.precedenceViolations.isEmpty

/- The two-unit example is the exact semantic projection of the Clojure
   `interpretation-construction-test` fixture: P produces q; Q needs q. -/
def exampleSemantics : Nat → UnitSemantics
  | 0 => ⟨{0}, ∅⟩
  | 1 => ⟨∅, {0}⟩
  | _ => ⟨∅, ∅⟩

def exampleEdge : EdgeWitness := ⟨0, 1, {0}⟩

def exampleReceipt : Receipt :=
  { order := [0, 1]
    support := [exampleEdge]
    meets := [⟨0, 1, 1, [exampleEdge], []⟩]
    precedence := [exampleEdge]
    linearExtension := [0, 1]
    precedenceViolations := [] }

theorem exampleReceipt_valid : valid exampleSemantics exampleReceipt = true := by
  native_decide

def forgedTokenReceipt : Receipt :=
  { exampleReceipt with
    support := [⟨0, 1, {1}⟩]
    precedence := [⟨0, 1, {1}⟩] }

theorem forgedTokenReceipt_invalid : valid exampleSemantics forgedTokenReceipt = false := by
  native_decide

def disconnectedPathReceipt : Receipt :=
  { exampleReceipt with
    meets := [⟨0, 1, 1, [⟨0, 0, {0}⟩], []⟩] }

theorem disconnectedPathReceipt_invalid :
    valid exampleSemantics disconnectedPathReceipt = false := by
  native_decide

/-! ## The outer-loop diamond

`futon3/library/meta/meta-outer-policy-cascade.edn` (2026-10-02) is a
four-unit cascade: observe → {fill, injury} → minimise.  Units and tokens
are numbered as in `NOTE-outer-cascade-as-pasted-blends-2026-10-05.md` §3:

  units  0 observe, 1 fill, 2 injury, 3 minimise
  tokens 0 field-observation, 1 injury-observation, 2 filled-candidates,
         3 typed-exclusions, 4 admitted-support, 5 rearm-slot,
         6 selected-meta-policy

`fill` and `injury` are incomparable; `minimise` is their meet.  The diamond
has two linear extensions, and both validate the same support: the order is
a parse of the formation, not part of it.  A chain adds an edge between
`fill` and `injury` that no token supports, and `valid` rejects it. -/

def diamondSemantics : Nat → UnitSemantics
  | 0 => ⟨{0, 1}, ∅⟩
  | 1 => ⟨{2, 3}, {0}⟩
  | 2 => ⟨{4, 5}, {0, 1}⟩
  | 3 => ⟨{6}, {2, 3, 4, 5}⟩
  | _ => ⟨∅, ∅⟩

def observeFill : EdgeWitness := ⟨0, 1, {0}⟩
def observeInjury : EdgeWitness := ⟨0, 2, {0, 1}⟩
def fillMinimise : EdgeWitness := ⟨1, 3, {2, 3}⟩
def injuryMinimise : EdgeWitness := ⟨2, 3, {4, 5}⟩

def diamondSupport : List EdgeWitness :=
  [observeFill, observeInjury, fillMinimise, injuryMinimise]

def diamondReceipt : Receipt :=
  { order := [0, 1, 2, 3]
    support := diamondSupport
    meets := [⟨1, 2, 3, [fillMinimise], [injuryMinimise]⟩]
    precedence := diamondSupport
    linearExtension := [0, 1, 2, 3]
    precedenceViolations := [] }

theorem diamondReceipt_valid : valid diamondSemantics diamondReceipt = true := by
  native_decide

/-- The other linear extension, injury before fill, over the same support. -/
def diamondReceiptInjuryFirst : Receipt :=
  { diamondReceipt with order := [0, 2, 1, 3], linearExtension := [0, 2, 1, 3] }

theorem diamondReceiptInjuryFirst_valid :
    valid diamondSemantics diamondReceiptInjuryFirst = true := by
  native_decide

/-- The chain O F I M: the recipe's fill → injury step as a precedence edge.
`produces fill ∩ needs injury = ∅`, so no token carries it. -/
def chainReceipt : Receipt :=
  { diamondReceipt with
    support := [observeFill, ⟨1, 2, ∅⟩, injuryMinimise]
    precedence := [observeFill, ⟨1, 2, ∅⟩, injuryMinimise] }

theorem chainReceipt_invalid : valid diamondSemantics chainReceipt = false := by
  native_decide

/-- Forging a token onto that step does not help: the token set must equal
the intersection. -/
def chainReceiptForgedToken : Receipt :=
  { chainReceipt with
    support := [observeFill, ⟨1, 2, {0}⟩, injuryMinimise]
    precedence := [observeFill, ⟨1, 2, {0}⟩, injuryMinimise] }

theorem chainReceiptForgedToken_invalid :
    valid diamondSemantics chainReceiptForgedToken = false := by
  native_decide

end DarkTower.WarMachine.ConstructionReceipt
