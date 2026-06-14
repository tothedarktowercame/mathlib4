import Mathlib

/-!
# Combs as dependent lenses

This file adds the DarkTower base object for a comb: a dependent lens, equivalently
a morphism of polynomial functors.  For polynomial functors `P` and `Q`, the map
is forward on positions and backward on directions:

* `onPos : P.A -> Q.A`;
* `onDir : (a : P.A) -> Q.B (onPos a) -> P.B a`.

Grounding:
* Niu--Spivak, *Polynomial Functors: A Mathematical Theory of Interaction*
  (arXiv:2312.00990), uses polynomial functors as interaction interfaces and
  treats Poly morphisms as dependent lenses.
* Spivak, *Generalized Lens Categories via functors C^op -> Cat*
  (arXiv:1908.02202), develops dependent lenses as morphisms.
* Riley, *Categories of Optics* (arXiv:1809.00738), places lenses inside the
  general optic construction; the dependent-lens data here is the cartesian/Poly
  base.
* nLab pages "dependent lens" and "polynomial functor" give the same
  forward-position/backward-direction shape.

The n-hole comb shape proper, such as `<A;-;B;-;C>`, is the coend/open-diagram
generalisation discussed by Roman, *Open Diagrams via Coend Calculus*
(arXiv:2004.07353), and Roman, *Comb Diagrams for Discrete-Time Feedback*
(arXiv:2003.06214).  This file intentionally does not build that layer yet.
-/

namespace DarkTower

open CategoryTheory

universe uAP uBP uAQ uBQ uAR uBR uAS uBS

/--
A comb from `P` to `Q` is the dependent-lens morphism of polynomial functors:
positions move forward, while directions are pulled back from the target
position to the source position.
-/
structure Comb (P : PFunctor.{uAP, uBP}) (Q : PFunctor.{uAQ, uBQ}) where
  /-- The forward map on positions/nodes. -/
  onPos : P.A -> Q.A
  /--
  The backward map on directions: a direction accepted by `Q` at the image
  position determines a direction accepted by `P` at the original position.
  -/
  onDir : (a : P.A) -> Q.B (onPos a) -> P.B a

namespace Comb

variable {P : PFunctor.{uAP, uBP}} {Q : PFunctor.{uAQ, uBQ}}
variable {R : PFunctor.{uAR, uBR}} {S : PFunctor.{uAS, uBS}}

/-- The identity dependent lens on a polynomial functor. -/
def id (P : PFunctor.{uAP, uBP}) : Comb P P where
  onPos := fun a => a
  onDir := fun _ dir => dir

/--
Composition of dependent lenses.  Positions compose forwards; directions compose
backwards, pulling an `R`-direction first through `g` and then through `f`.
-/
def comp (f : Comb P Q) (g : Comb Q R) : Comb P R where
  onPos := fun a => g.onPos (f.onPos a)
  onDir := fun a dir => f.onDir a (g.onDir (f.onPos a) dir)

/-- Left identity law for dependent-lens composition. -/
@[simp]
theorem id_comp (f : Comb P Q) : comp (id P) f = f := by
  cases f
  rfl

/-- Right identity law for dependent-lens composition. -/
@[simp]
theorem comp_id (f : Comb P Q) : comp f (id Q) = f := by
  cases f
  rfl

/-- Associativity law for dependent-lens composition. -/
@[simp]
theorem comp_assoc (f : Comb P Q) (g : Comb Q R) (h : Comb R S) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f
  cases g
  cases h
  rfl

/-- The position part of a composite is ordinary function composition. -/
@[simp]
theorem comp_onPos (f : Comb P Q) (g : Comb Q R) (a : P.A) :
    (comp f g).onPos a = g.onPos (f.onPos a) :=
  rfl

/-- The direction part of a composite is contravariant in directions. -/
@[simp]
theorem comp_onDir (f : Comb P Q) (g : Comb Q R) (a : P.A)
    (dir : R.B (g.onPos (f.onPos a))) :
    (comp f g).onDir a dir = f.onDir a (g.onDir (f.onPos a) dir) :=
  rfl

/-- A one-position example of a comb from Boolean holes to unit holes. -/
def booleanToUnitExample :
    Comb
      ({ A := Unit, B := fun _ => Bool } : PFunctor)
      ({ A := Unit, B := fun _ => Unit } : PFunctor) where
  onPos := fun _ => ()
  onDir := fun _ _ => false

#check Comb.id
#check Comb.comp
#check Comb.comp_onDir

end Comb

end DarkTower
