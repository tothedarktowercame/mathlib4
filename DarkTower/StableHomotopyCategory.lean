import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Axiomatic stable homotopy categories

This file records the first DarkTower formalization step for an axiomatic stable
homotopy category.

Grounding:
* Paper: Hovey--Palmieri--Strickland, *Axiomatic Stable Homotopy Theory*
  (Memoirs AMS 1997; arXiv:math/9704207).
* Scope: mathlib anchors the triangulated part at
  `Mathlib/CategoryTheory/Triangulated/Triangulated.lean`, where
  `CategoryTheory.IsTriangulated` is "a pretriangulated category which satisfies
  the octahedron axiom (TR 4)".
* Scope: mathlib anchors the closed monoidal part at
  `Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean`, where
  `CategoryTheory.MonoidalClosed` is "A monoidal category `C` is (right)
  monoidal closed if every object is (right) closed."
* Scope: mathlib anchors the symmetric monoidal part at
  `Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean` via
  `CategoryTheory.SymmetricCategory`.
* Scope: mathlib anchors dualizability at
  `Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean`, where `HasRightDual`
  and `HasLeftDual` are "class[es] of objects" with right and left duals.
* Scope: mathlib anchors additive Hom functors at
  `Mathlib/CategoryTheory/Preadditive/Yoneda/Basic.lean`, where
  `preadditiveCoyoneda` sends an object to the additive represented Hom functor.

HPS Definition 1.1.4 requires a set of small weak generators; Sec. 1.2 adds
strong dualizability in the monoidal setting.  In this file "small" is
formalized directly as preservation of coproduct-shaped colimits by the graded
additive functors `[g, -[n]]`.
-/

noncomputable section

universe u v

namespace DarkTower

open CategoryTheory
open CategoryTheory.Limits
open Opposite

/--
HPS smallness/compactness: each graded additive Hom functor `[X, -[n]]`
preserves coproduct-shaped colimits.
-/
def HpsSmall {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
    (X : C) : Prop :=
  ∀ (n : ℤ) (J : Type u),
    PreservesColimitsOfShape (Discrete J)
      (shiftFunctor C n ⋙ preadditiveCoyoneda.obj (op X))

/--
HPS strong dualizability, expressed using mathlib's left and right dual classes.
In a symmetric monoidal category these are equivalent data, but requiring both
keeps this first formalization explicit.
-/
def HpsStronglyDualizable {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (X : C) : Prop :=
  Nonempty (HasLeftDual X) ∧ Nonempty (HasRightDual X)

/--
HPS weak generation: an object is zero iff all graded maps from the generators
to it vanish.
-/
def HpsWeaklyGenerates {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] [HasShift C ℤ] (S : Set C) : Prop :=
  ∀ X : C, IsZero X ↔
    ∀ g : C, g ∈ S → ∀ n : ℤ, ∀ f : g ⟶ (shiftFunctor C n).obj X, f = 0

/-- A set satisfying the Hovey--Palmieri--Strickland generator conditions. -/
structure HpsGeneratorSet {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [MonoidalCategory C] (S : Set C) : Prop where
  small : ∀ g : C, g ∈ S → HpsSmall g
  strongly_dualizable : ∀ g : C, g ∈ S → HpsStronglyDualizable g
  weakly_generates : HpsWeaklyGenerates S

/--
An axiomatic stable homotopy category is a triangulated closed symmetric
monoidal category together with an HPS set of small, strongly dualizable, weak
generators.
-/
class IsStableHomotopyCategory (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasCoproducts.{u} C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
    [Pretriangulated C] [IsTriangulated C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] : Prop where
  /-- The HPS generator set with smallness, dualizability, and weak generation. -/
  exists_hpsGenerators : ∃ generators : Set C, HpsGeneratorSet generators

/-- A stable homotopy category is triangulated, by the axiomatic wrapper. -/
theorem stableHomotopyCategory_isTriangulated (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasCoproducts.{u} C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
    [IsTriangulated C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [IsStableHomotopyCategory C] : IsTriangulated C := by
  infer_instance

/-- A stable homotopy category has closed monoidal structure, by the axiomatic wrapper. -/
theorem stableHomotopyCategory_nonempty_monoidalClosed (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasCoproducts.{u} C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
    [IsTriangulated C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [IsStableHomotopyCategory C] : Nonempty (MonoidalClosed C) :=
  ⟨inferInstance⟩

/-- The axiomatic wrapper carries a genuine HPS generator set. -/
theorem stableHomotopyCategory_exists_hpsGenerators (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasCoproducts.{u} C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
    [IsTriangulated C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [hC : IsStableHomotopyCategory C] :
    ∃ generators : Set C, HpsGeneratorSet generators :=
  hC.exists_hpsGenerators

/-- The HPS generator set weakly generates in the shifted Hom-vanishing sense. -/
theorem stableHomotopyCategory_exists_hpsWeakGenerators (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasCoproducts.{u} C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
    [IsTriangulated C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [hC : IsStableHomotopyCategory C] :
    ∃ generators : Set C, HpsWeaklyGenerates generators := by
  rcases hC.exists_hpsGenerators with ⟨generators, hgenerators⟩
  exact ⟨generators, hgenerators.weakly_generates⟩

#print axioms DarkTower.stableHomotopyCategory_isTriangulated
#print axioms DarkTower.stableHomotopyCategory_nonempty_monoidalClosed
#print axioms DarkTower.stableHomotopyCategory_exists_hpsGenerators
#print axioms DarkTower.stableHomotopyCategory_exists_hpsWeakGenerators

end DarkTower
