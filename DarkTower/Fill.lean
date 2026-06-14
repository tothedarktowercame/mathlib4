import Mathlib

/-!
# Fills for typed holes

This file gives the DarkTower stub for filling a typed hole by polynomial
substitution.

Grounding:
* Paper: Gambino and Kock, *Polynomial functors and polynomial monads*,
  Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013).
* Scope: nLab page "polynomial functor" describes substitution/composition of
  polynomial functors.
* Lean reference: mathlib's `PFunctor.comp`, `PFunctor.comp.mk`, and
  `PFunctor.comp.get` implement univariate polynomial composition.
* Lean comparison point: `sinhp/Poly`
  (https://github.com/sinhp/Poly) develops the monoidal/composition structure
  for polynomial functors.  This file keeps only the small object-level unit and
  associativity equivalences needed by DarkTower.
-/

namespace DarkTower

open CategoryTheory

universe uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ v

namespace Fill

/-- Filling a typed hole is polynomial substitution/composition. -/
def fill (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) :
    PFunctor.{max uA₁ uA₂ uB₂, max uB₁ uB₂} :=
  PFunctor.comp P₂ P₁

/-- The identity polynomial, representing one unfilled variable. -/
def I : PFunctor :=
  ⟨PUnit, fun _ => PUnit⟩

/-- Insert an object into the identity polynomial. -/
def I.mk {α : Type v} (x : α) : I α :=
  ⟨PUnit.unit, fun _ => x⟩

/-- Extract the object carried by the identity polynomial. -/
def I.get {α : Type v} (x : I α) : α :=
  x.2 PUnit.unit

@[simp]
theorem I.get_mk {α : Type v} (x : α) : I.get (I.mk x) = x :=
  rfl

@[simp]
theorem I.mk_get {α : Type v} (x : I α) : I.mk (I.get x) = x := by
  cases x with
  | mk a f =>
      cases a
      congr

variable (P₁ : PFunctor.{uA₁, uB₁})
variable (P₂ : PFunctor.{uA₂, uB₂})
variable (P₃ : PFunctor.{uA₃, uB₃})

/-- Left unit law for filling: substituting into the identity polynomial changes nothing. -/
def leftUnitEquiv (α : Type v) : fill I P₁ α ≃ P₁ α where
  toFun x :=
    ⟨x.1.2 PUnit.unit, fun b => x.2 ⟨PUnit.unit, b⟩⟩
  invFun x :=
    ⟨⟨PUnit.unit, fun _ => x.1⟩, fun b => x.2 b.2⟩
  left_inv x := by
    cases x with
    | mk a f =>
        cases a with
        | mk a g =>
            cases a
            congr
  right_inv x := by
    cases x
    rfl

/-- Right unit law for filling: filling every direction by one variable changes nothing. -/
def rightUnitEquiv (α : Type v) : fill P₁ I α ≃ P₁ α where
  toFun x :=
    ⟨x.1.1, fun b => x.2 ⟨b, PUnit.unit⟩⟩
  invFun x :=
    ⟨⟨x.1, fun _ => PUnit.unit⟩, fun b => x.2 b.1⟩
  left_inv x := by
    cases x with
    | mk a f =>
        cases a with
        | mk a g =>
            congr
  right_inv x := by
    cases x
    rfl

/-- Associativity law for filling, as the standard reassociation of nested substitutions. -/
def assocEquiv (α : Type v) :
    fill (fill P₃ P₂) P₁ α ≃ fill P₃ (fill P₂ P₁) α where
  toFun x :=
    ⟨⟨x.1.1.1, fun b₃ => ⟨x.1.1.2 b₃, fun b₂ => x.1.2 ⟨b₃, b₂⟩⟩⟩,
      fun b => x.2 ⟨⟨b.1, b.2.1⟩, b.2.2⟩⟩
  invFun x :=
    ⟨⟨⟨x.1.1, fun b₃ => (x.1.2 b₃).1⟩,
      fun b => (x.1.2 b.1).2 b.2⟩,
      fun b => x.2 ⟨b.1.1, ⟨b.1.2, b.2⟩⟩⟩
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl

/-- The `PFunctor.comp` constructor and destructor are inverse in the forward direction. -/
@[simp]
theorem comp_get_mk {α : Type v} (x : P₂ (P₁ α)) :
    PFunctor.comp.get P₂ P₁ (PFunctor.comp.mk P₂ P₁ x) = x := by
  cases x
  rfl

/-- The `PFunctor.comp` constructor and destructor are inverse in the backward direction. -/
@[simp]
theorem comp_mk_get {α : Type v} (x : fill P₂ P₁ α) :
    PFunctor.comp.mk P₂ P₁ (PFunctor.comp.get P₂ P₁ x) = x := by
  cases x
  rfl

#check PFunctor.comp
#check PFunctor.comp.mk
#check PFunctor.comp.get
#check leftUnitEquiv
#check rightUnitEquiv
#check assocEquiv

end Fill

end DarkTower
