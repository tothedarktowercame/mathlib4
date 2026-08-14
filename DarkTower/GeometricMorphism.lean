import Mathlib

/-!
# Geometric morphisms

This file adds the DarkTower wrapper for geometric morphisms between
Grothendieck topoi.
-/

universe uE vE uF vF uG vG uC uS

namespace DarkTower

open CategoryTheory
open CategoryTheory.Limits

/--
A geometric morphism `E ⟶ F` between Grothendieck topoi is an adjoint pair
`f^* ⊣ f_*` whose inverse-image functor `f^* : F ⥤ E` is left exact, i.e. it
preserves finite limits.

Literature grounding: Mac Lane--Moerdijk, *Sheaves in Geometry and Logic*, ch. VII,
and Johnstone, *Sketches of an Elephant*, A4.1.1, use this inverse/direct image
adjunction with left-exact inverse image. The local nLab page `geometric morphism`
phrases the definition as: "a geometric morphism f:E→F consists of a pair of
adjoint functors"; the same page states that `f^*` is the inverse image and that
geometric morphisms are characterized by finite-limit preservation of `f^*`.
-/
structure GeometricMorphism (E : Type uE) (F : Type uF)
    [CategoryTheory.Category.{vE} E] [CategoryTheory.Category.{vF} F] where
  /-- The inverse-image functor `f^*`. -/
  inverseImage : F ⥤ E
  /-- The direct-image functor `f_*`. -/
  directImage : E ⥤ F
  /-- The defining adjunction `f^* ⊣ f_*`. -/
  adjunction : inverseImage ⊣ directImage
  /-- Geometric inverse image is left exact. -/
  leftExact : PreservesFiniteLimits inverseImage

namespace GeometricMorphism

/-- The identity geometric morphism on any category, hence on any topos. -/
def id (E : Type uE) [CategoryTheory.Category.{vE} E] :
    GeometricMorphism E E where
  inverseImage := 𝟭 E
  directImage := 𝟭 E
  adjunction := CategoryTheory.Adjunction.id
  leftExact := inferInstance

/-- Composite geometric morphism; left exactness is closed under functor composition. -/
def comp {E : Type uE} {F : Type uF} {G : Type uG}
    [CategoryTheory.Category.{vE} E] [CategoryTheory.Category.{vF} F]
    [CategoryTheory.Category.{vG} G]
    (f : GeometricMorphism E F)
    (g : GeometricMorphism F G) :
    GeometricMorphism E G where
  inverseImage := g.inverseImage ⋙ f.inverseImage
  directImage := f.directImage ⋙ g.directImage
  adjunction := g.adjunction.comp f.adjunction
  leftExact := by
    letI : PreservesFiniteLimits g.inverseImage := g.leftExact
    letI : PreservesFiniteLimits f.inverseImage := f.leftExact
    exact Limits.comp_preservesFiniteLimits g.inverseImage f.inverseImage

#print axioms DarkTower.GeometricMorphism.id
#print axioms DarkTower.GeometricMorphism.comp

end GeometricMorphism

end DarkTower
