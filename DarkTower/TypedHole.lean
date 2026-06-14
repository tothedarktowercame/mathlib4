import Mathlib

/-!
# Typed holes as polynomial positions

This file gives the first DarkTower wrapper for typed holes.  A polynomial
functor `P` has positions `P.A` and, at each position `a`, a dependent family
`P.B a` of directions.  We read a position as a node and the directions at that
node as the typed holes available at that node.

Grounding:
* Paper: Niu--Spivak, *Polynomial Functors*, arXiv:2312.00990, treats
  polynomial functors as interaction interfaces with positions and directions.
* Scope: nLab page "polynomial functor" presents a polynomial as shapes with
  positions over each shape; mathlib's `PFunctor` uses fields `A` and `B`.
* Mathlib scope: `Mathlib/Data/PFunctor/Univariate/Basic.lean` defines
  `PFunctor` with `A : Type` and `B : A -> Type`.  `Mathlib/CategoryTheory/
  GradedObject.lean` defines a graded object as a function from grades to
  objects, used here to project nodes by satiety grade.
-/

namespace DarkTower

open CategoryTheory

universe uA uB

/--
Finite tags for the kind of satiety a typed-hole position currently exposes.

The tags correspond to the corpus-facing buckets `:parse`, `:payoff`, `:canon`,
`:bundling`, and `:role`.
-/
inductive SatietyGrade where
  | parse
  | payoff
  | canon
  | bundling
  | role
  deriving DecidableEq, Fintype, Repr

/--
A typed-hole interface is a polynomial functor together with a satiety grading
of its positions.

Positions `poly.A` are nodes.  Directions `poly.B a` are the typed holes accepted
at the node `a`.
-/
structure TypedHole where
  /-- The underlying polynomial functor of positions and typed directions. -/
  poly : PFunctor.{uA, uB}
  /-- A finite satiety grade assigned to each position/node. -/
  satiety : poly.A -> SatietyGrade

namespace TypedHole

/-- The type of holes/directions accepted at a node. -/
def holeType (T : TypedHole.{uA, uB}) (a : T.poly.A) : Type uB :=
  T.poly.B a

/-- The graded object of nodes, indexed by satiety grade. -/
def nodesBySatiety (T : TypedHole.{uA, uB}) :
    GradedObject SatietyGrade (Type uA) :=
  fun grade => { a : T.poly.A // T.satiety a = grade }

/-- The holes at a node after projecting to a satiety component. -/
def gradedHoleType (T : TypedHole.{uA, uB}) (grade : SatietyGrade)
    (a : T.nodesBySatiety grade) : Type uB :=
  T.holeType a.1

/--
Projecting a graded node keeps exactly the hole type supplied by the underlying
polynomial direction family.
-/
@[simp]
theorem gradedHoleType_eq_holeType (T : TypedHole.{uA, uB})
    (grade : SatietyGrade) (a : T.nodesBySatiety grade) :
    T.gradedHoleType grade a = T.holeType a.1 :=
  rfl

/-- A one-node example whose only node has Boolean typed holes. -/
def booleanExample : TypedHole where
  poly :=
    { A := Unit
      B := fun _ => Bool }
  satiety := fun _ => SatietyGrade.parse

#check TypedHole.holeType
#check TypedHole.nodesBySatiety
#check TypedHole.gradedHoleType

example : booleanExample.holeType () = Bool :=
  rfl

example : booleanExample.satiety () = SatietyGrade.parse :=
  rfl

end TypedHole

end DarkTower
