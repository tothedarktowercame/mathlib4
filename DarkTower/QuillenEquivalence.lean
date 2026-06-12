import DarkTower.QuillenAdjunction
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Quillen equivalences

This file records the DarkTower formalization step for Quillen equivalences.

Grounding:
* Paper: Hovey, *Model Categories*, Definition 1.3.12: a Quillen adjunction is
  a Quillen equivalence when, equivalently, for cofibrant `X` and fibrant `Y`, a
  map `F X ⟶ Y` is a weak equivalence iff its adjunct `X ⟶ G Y` is.
* Corpus arXiv anchor: arXiv:1410.5675 says "the corresponding Quillen
  adjunction between the categories of algebras is a Quillen equivalence".
* Mathlib scope: `Mathlib/AlgebraicTopology/ModelCategory/IsCofibrant.lean`
  defines `IsCofibrant` and `IsFibrant`; `CategoryWithCofibrations.lean`
  defines `WeakEquivalence`; `Mathlib/CategoryTheory/Adjunction/Basic.lean`
  defines `Adjunction.homEquiv`.

The homotopy-category equivalence formulation is not proved here.  Instead this
uses Hovey's cofibrant/fibrant weak-equivalence criterion as the defining field,
which is equivalent in the literature and avoids a fake placeholder for the
localized homotopy-category proof.
-/

namespace DarkTower

open CategoryTheory HomotopicalAlgebra

universe v₁ v₂ u₁ u₂

/--
A Quillen equivalence, stated by Hovey's cofibrant/fibrant adjunct weak-equivalence
criterion.
-/
structure QuillenEquivalence {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [ModelCategory C] [ModelCategory D]
    (F : C ⥤ D) (G : D ⥤ C) where
  toQuillenAdjunction : QuillenAdjunction F G
  weakEquivalence_iff_adjunct :
    ∀ {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y] (f : F.obj X ⟶ Y),
      WeakEquivalence f ↔
        WeakEquivalence (toQuillenAdjunction.adjunction.homEquiv X Y f)

namespace QuillenEquivalence

/-- The identity Quillen adjunction is a Quillen equivalence. -/
def id (C : Type u₁) [Category.{v₁} C] [ModelCategory C] :
    QuillenEquivalence (𝟭 C) (𝟭 C) where
  toQuillenAdjunction := QuillenAdjunction.id C
  weakEquivalence_iff_adjunct := by
    intro X Y _ _ f
    change WeakEquivalence f ↔ WeakEquivalence (𝟙 X ≫ f)
    simp

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D] [ModelCategory C] [ModelCategory D]
variable {F : C ⥤ D} {G : D ⥤ C}

/-- A Quillen equivalence includes a Quillen adjunction. -/
theorem nonempty_quillenAdjunction (h : QuillenEquivalence F G) :
    Nonempty (QuillenAdjunction F G) :=
  ⟨h.toQuillenAdjunction⟩

/--
For a Quillen equivalence, a map out of the left adjoint on a cofibrant object
and into a fibrant object is a weak equivalence iff its adjunct is.
-/
theorem weakEquivalence_iff_adjunct_apply (h : QuillenEquivalence F G)
    {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y] (f : F.obj X ⟶ Y) :
    WeakEquivalence f ↔
      WeakEquivalence (h.toQuillenAdjunction.adjunction.homEquiv X Y f) :=
  h.weakEquivalence_iff_adjunct f

#print axioms DarkTower.QuillenEquivalence.id
#print axioms DarkTower.QuillenEquivalence.nonempty_quillenAdjunction
#print axioms DarkTower.QuillenEquivalence.weakEquivalence_iff_adjunct_apply

end QuillenEquivalence

end DarkTower
