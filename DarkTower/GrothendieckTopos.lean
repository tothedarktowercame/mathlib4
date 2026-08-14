import Mathlib

/-!
# Grothendieck topoi

This file starts the DarkTower category-theory vocabulary by packaging the
standard site/sheaf definition of a Grothendieck topos.
-/

universe uE vE uF vF uC uS

namespace DarkTower

open CategoryTheory

/--
A category `E` is a Grothendieck topos if it is equivalent to the category of
sheaves of types on a small site `(C, J)`.

Literature grounding: this follows the standard site definition used by
Mac Lane--Moerdijk, *Sheaves in Geometry and Logic*, and Johnstone, *Sketches of
an Elephant*. The local nLab page `Grothendieck topos` phrases the same point as:
"This is equivalently the category of sheaves ... over a small site."

The definition is intentionally a `Prop`: it records existence of a presentation,
not a chosen site or a chosen equivalence.
-/
class IsGrothendieckTopos (E : Type uE) [CategoryTheory.Category.{vE} E] : Prop where
  exists_site :
    ∃ (C : Type uC) (_ : CategoryTheory.SmallCategory C) (J : CategoryTheory.GrothendieckTopology C),
      Nonempty (E ≌ CategoryTheory.Sheaf J (Type uS))

/--
The canonical anti-vacuity witness: for any small site `(C, J)`, the category of
`Type`-valued sheaves on that site is a Grothendieck topos by definition.
-/
instance sheaf_isGrothendieckTopos (C : Type uC) [CategoryTheory.SmallCategory C]
    (J : CategoryTheory.GrothendieckTopology C) :
    IsGrothendieckTopos.{_, _, uC, uS} (CategoryTheory.Sheaf J (Type uS)) where
  exists_site := ⟨C, inferInstance, J, ⟨(CategoryTheory.Equivalence.refl :
      CategoryTheory.Sheaf J (Type uS) ≌ CategoryTheory.Sheaf J (Type uS))⟩⟩

/--
Grothendieck-topos structure is invariant under equivalence of categories.
If `E` has a site/sheaf presentation and `E ≌ F`, then `F` has the transported
presentation by composing the inverse equivalence `F ≌ E` with `E ≌ Sheaf J`.
-/
theorem isGrothendieckTopos_of_equivalence {E : Type uE} {F : Type uF}
    [CategoryTheory.Category.{vE} E] [CategoryTheory.Category.{vF} F]
    (hE : IsGrothendieckTopos.{uE, vE, uC, uS} E) (e : E ≌ F) :
    IsGrothendieckTopos.{uF, vF, uC, uS} F := by
  rcases hE.exists_site with ⟨C, hC, J, hEq⟩
  letI : CategoryTheory.SmallCategory C := hC
  rcases hEq with ⟨eqv⟩
  exact ⟨⟨C, hC, J, ⟨e.symm.trans eqv⟩⟩⟩

/-- Equivalent categories are Grothendieck topoi simultaneously. -/
theorem isGrothendieckTopos_iff_of_equivalence {E : Type uE} {F : Type uF}
    [CategoryTheory.Category.{vE} E] [CategoryTheory.Category.{vF} F] (e : E ≌ F) :
    IsGrothendieckTopos.{uE, vE, uC, uS} E ↔
      IsGrothendieckTopos.{uF, vF, uC, uS} F :=
  ⟨fun hE => isGrothendieckTopos_of_equivalence hE e,
   fun hF => isGrothendieckTopos_of_equivalence hF e.symm⟩

#print axioms DarkTower.sheaf_isGrothendieckTopos
#print axioms DarkTower.isGrothendieckTopos_of_equivalence
#print axioms DarkTower.isGrothendieckTopos_iff_of_equivalence

end DarkTower
