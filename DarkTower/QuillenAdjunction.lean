import Mathlib

/-!
# Quillen adjunctions

This file gives the DarkTower stub for a Quillen adjunction between model categories.

Grounding:
* Paper: Quillen, *Homotopical Algebra*, Lecture Notes in Mathematics 43.
* Corpus arXiv anchor: Gutiérrez, arXiv:1104.0584, Section 2.1
  "Quillen functors", says an adjoint pair between model categories is a
  Quillen adjunction iff the left adjoint "preserves cofibrations and trivial
  cofibrations" or equivalently the right adjoint preserves fibrations and
  trivial fibrations.
* Scope: nLab page "Quillen adjunction" says a left Quillen functor preserves
  "cofibrations and acyclic cofibrations".
* Mathlib scope: `Mathlib/AlgebraicTopology/ModelCategory/Basic.lean` defines
  `HomotopicalAlgebra.ModelCategory`; `CategoryWithCofibrations.lean` defines
  `Cofibration`, `WeakEquivalence`, and `trivialCofibrations`;
  `Mathlib/CategoryTheory/Adjunction/Basic.lean` defines `CategoryTheory.Adjunction`.

This is only the left-adjoint preservation formulation.  The equivalent right-adjoint
formulation is intentionally left for a later collaborative step.
-/

namespace DarkTower

open CategoryTheory HomotopicalAlgebra

universe v₁ v₂ u₁ u₂

/-- A Quillen adjunction, in the left-adjoint preservation formulation. -/
structure QuillenAdjunction {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [ModelCategory C] [ModelCategory D]
    (F : C ⥤ D) (G : D ⥤ C) where
  adjunction : F ⊣ G
  left_preserves_cofibrations :
    ∀ {X Y : C} (f : X ⟶ Y), Cofibration f → Cofibration (F.map f)
  left_preserves_trivial_cofibrations :
    ∀ {X Y : C} (f : X ⟶ Y), Cofibration f → WeakEquivalence f →
      Cofibration (F.map f) ∧ WeakEquivalence (F.map f)

namespace QuillenAdjunction

/-- The identity adjunction is a Quillen adjunction. -/
def id (C : Type u₁) [Category.{v₁} C] [ModelCategory C] :
    QuillenAdjunction (𝟭 C) (𝟭 C) where
  adjunction := Adjunction.id
  left_preserves_cofibrations := by
    intro X Y f hf
    simpa using hf
  left_preserves_trivial_cofibrations := by
    intro X Y f hf hw
    exact ⟨by simpa using hf, by simpa using hw⟩

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D] [ModelCategory C] [ModelCategory D]
variable {F : C ⥤ D} {G : D ⥤ C}

/-- The left adjoint in a Quillen adjunction preserves cofibrations. -/
theorem preserves_cofibration (h : QuillenAdjunction F G)
    {X Y : C} (f : X ⟶ Y) [Cofibration f] : Cofibration (F.map f) :=
  h.left_preserves_cofibrations f inferInstance

/-- The left adjoint in a Quillen adjunction preserves trivial cofibrations. -/
theorem preserves_trivial_cofibration (h : QuillenAdjunction F G)
    {X Y : C} (f : X ⟶ Y) [Cofibration f] [WeakEquivalence f] :
    Cofibration (F.map f) ∧ WeakEquivalence (F.map f) :=
  h.left_preserves_trivial_cofibrations f inferInstance inferInstance

#print axioms DarkTower.QuillenAdjunction.preserves_cofibration
#print axioms DarkTower.QuillenAdjunction.preserves_trivial_cofibration
#print axioms DarkTower.QuillenAdjunction.id

end QuillenAdjunction

end DarkTower
