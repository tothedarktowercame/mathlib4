import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
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

HPS also require a set of small/strongly-dualizable generators.  This first step
records only the existence of a candidate set, and deliberately does not assert
smallness or strong dualizability until those notions are fixed against existing
mathlib definitions.
-/

noncomputable section

universe u v

namespace DarkTower

open CategoryTheory
open CategoryTheory.Limits

/--
An axiomatic stable homotopy category, at this stage, is a triangulated closed
symmetric monoidal category together with an HPS generator-set placeholder.

This first collaborative step is intentionally conservative: it records the
existence of a candidate generator set, while formalizing the HPS
small/strongly-dualizable generator axioms is deferred rather than encoded by an
ungrounded placeholder.
-/
class IsStableHomotopyCategory (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
    [Pretriangulated C] [IsTriangulated C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] : Prop where
  /-- A candidate HPS generator set; its smallness/dualizability is deferred. -/
  exists_hpsGenerators : ∃ _generators : Set C, True

/-- A stable homotopy category is triangulated, by the axiomatic wrapper. -/
theorem stableHomotopyCategory_isTriangulated (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
    [IsTriangulated C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [IsStableHomotopyCategory C] : IsTriangulated C := by
  infer_instance

/-- A stable homotopy category has closed monoidal structure, by the axiomatic wrapper. -/
theorem stableHomotopyCategory_nonempty_monoidalClosed (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
    [IsTriangulated C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [IsStableHomotopyCategory C] : Nonempty (MonoidalClosed C) :=
  ⟨inferInstance⟩

/-- The axiomatic wrapper carries a candidate HPS generator set. -/
theorem stableHomotopyCategory_exists_hpsGenerators (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
    [IsTriangulated C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [hC : IsStableHomotopyCategory C] : ∃ _generators : Set C, True :=
  hC.exists_hpsGenerators

#print axioms DarkTower.stableHomotopyCategory_isTriangulated
#print axioms DarkTower.stableHomotopyCategory_nonempty_monoidalClosed
#print axioms DarkTower.stableHomotopyCategory_exists_hpsGenerators

end DarkTower
