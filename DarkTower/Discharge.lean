import Mathlib

/-!
# Discharge duality

This file records the DarkTower interface for a hole and its discharge:
sorry/proof, query/answer, and ungrounded symbol/binder.  The categorical
shape is the Eilenberg--Moore coalgebra of a comonad.  A position opens by its
coalgebra map `A ⟶ G A`; the comonad counit `ε : G A ⟶ A` discharges it back
to the filled position.

Grounding:
* Paper: Eilenberg--Moore, *Adjoint functors and triples*, Illinois J. Math. 9
  (1965), for algebras and coalgebras associated to monads/comonads.
* Scope: nLab pages "comonad" and "coalgebra over a comonad" describe the
  counit and coalgebra equations used here.
* Mathlib anchors: `CategoryTheory.Comonad` supplies the counit `ε`, and
  `CategoryTheory.Comonad.Coalgebra` supplies the coalgebra object, structure
  map, counit law, and coalgebra morphisms.
-/

universe u v

namespace DarkTower

open CategoryTheory

/--
The three DarkTower readings of the same discharge polarity: a missing proof
filled by a proof, a query filled by an answer, and an ungrounded symbol filled
by a binder.
-/
inductive DischargeKind where
  /-- A `sorry` hole discharged by an actual proof. -/
  | sorryProof
  /-- A routed query discharged by an answer. -/
  | queryAnswer
  /-- An ungrounded symbol discharged by a binder. -/
  | ungroundedBinder
deriving DecidableEq

/--
A discharge over a comonad is a coalgebra at one position, together with the
DarkTower reading of what is being discharged.
-/
structure Discharge {C : Type u} [Category.{v} C] (G : Comonad C) where
  /-- Which operational reading this coalgebraic discharge carries. -/
  kind : DischargeKind
  /-- The Eilenberg--Moore coalgebra located at the position. -/
  carrier : Comonad.Coalgebra G

namespace Discharge

variable {C : Type u} [Category.{v} C] {G : Comonad C}

/-- The underlying position at which the hole/query/ungrounded symbol lives. -/
abbrev position (D : Discharge G) : C :=
  D.carrier.A

/-- The coalgebra map that opens a position into its discharge context. -/
def opened (D : Discharge G) : D.carrier.A ⟶ (G : C ⥤ C).obj D.carrier.A :=
  D.carrier.a

/-- The comonad counit that discharges the context back to the filled position. -/
def filled (D : Discharge G) : (G : C ⥤ C).obj D.carrier.A ⟶ D.carrier.A :=
  G.ε.app D.carrier.A

/-- The bundled mathlib coalgebra behind a DarkTower discharge. -/
def coalgebra (D : Discharge G) : Comonad.Coalgebra G :=
  D.carrier

/-- Opening a position and then applying the counit is the identity discharge. -/
@[simp]
theorem open_filled (D : Discharge G) :
    D.opened ≫ D.filled = 𝟙 D.carrier.A :=
  D.carrier.counit

/-- A map of discharges is exactly a morphism of the underlying coalgebras. -/
structure Hom (D E : Discharge G) where
  /-- The coalgebra morphism preserving the discharge structure. -/
  map : D.carrier ⟶ E.carrier

/-- Identity map of a discharge. -/
def id (D : Discharge G) : Hom D D where
  map := 𝟙 D.carrier

/-- Composition of discharge maps. -/
def comp {D E F : Discharge G} (f : Hom D E) (g : Hom E F) : Hom D F where
  map := f.map ≫ g.map

/--
Interface for a fill step while `DarkTower/Fill.lean` is not part of this
module: filling commutes with discharge when the fill step is a coalgebra
morphism.
-/
structure FillStep (D E : Discharge G) where
  /-- The coalgebra morphism induced by filling the position. -/
  hom : D.carrier ⟶ E.carrier

/--
Discharge commutes with fill: opening, transporting along the filled map, and
then applying the counit is the same as filling the position directly.
-/
theorem fill_commutes_with_discharge {D E : Discharge G} (f : FillStep D E) :
    D.opened ≫ (G : C ⥤ C).map f.hom.f ≫ E.filled = f.hom.f := by
  dsimp [opened, filled]
  rw [← Category.assoc, f.hom.h]
  have h := congrArg (fun k => f.hom.f ≫ k) E.carrier.counit
  simpa [Category.assoc] using h

#print axioms DarkTower.Discharge.open_filled
#print axioms DarkTower.Discharge.fill_commutes_with_discharge
#print axioms DarkTower.Discharge.id
#print axioms DarkTower.Discharge.comp

end Discharge

end DarkTower
