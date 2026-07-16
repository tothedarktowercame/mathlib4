import Mathlib

/-!
# Propagators as morphisms of endo-sets

A propagator recipe is a pair of maps `s : N → N` and `ν : P → P`.  Its
elementary update at `k` replaces the value at `s k` by `ν (g k)`.  This file
keeps `s` an arbitrary map: the non-injective 2014 Emacs map is a central
example, not a permutation.

The fixed rules are exactly the morphisms `(N, s) ⟶ (P, ν)` in the category of
sets equipped with one endomorphism.  A bespoke `EndoHom` is used instead of a
`MulActionHom`: there is only one distinguished generator here, and the direct
definition retains arbitrary, noninvertible `s` without irrelevant action
machinery.
-/

namespace DarkTower.Patterns.Propagator

universe u v u' v'

/-- A set equipped with one distinguished endomorphism. -/
structure EndoSet where
  Carrier : Type u
  step : Carrier → Carrier

/-- A morphism of endo-sets is an equivariant map. -/
structure EndoHom (A : EndoSet.{u}) (B : EndoSet.{v}) where
  toFun : A.Carrier → B.Carrier
  comm : ∀ x, toFun (A.step x) = B.step (toFun x)

instance {A : EndoSet.{u}} {B : EndoSet.{v}} : FunLike (EndoHom A B) A.Carrier B.Carrier where
  coe := EndoHom.toFun
  coe_injective' f g h := by cases f; cases g; cases h; rfl

@[ext]
theorem EndoHom.ext {A : EndoSet.{u}} {B : EndoSet.{v}} {f g : EndoHom A B}
    (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- An isomorphism of endo-sets. -/
structure EndoEquiv (A : EndoSet.{u}) (B : EndoSet.{v}) where
  toEquiv : A.Carrier ≃ B.Carrier
  comm : ∀ x, toEquiv (A.step x) = B.step (toEquiv x)

/-- The shape/value recipe, with no reference to an encoding of `P ^ N`. -/
structure Recipe (N : Type u) (P : Type v) where
  shape : N → N
  value : P → P

/-- The elementary operation: pick `k`, then write `ν (g k)` at `s k`. -/
def update [DecidableEq N] (r : Recipe N P) (k : N) (g : N → P) : N → P :=
  Function.update g (r.shape k) (r.value (g k))

/-- A rule is fixed by the propagator when every elementary update leaves it unchanged. -/
def IsFixed [DecidableEq N] (r : Recipe N P) (g : N → P) : Prop :=
  ∀ k, update r k g = g

/-- The endo-set carried by the recipe's shape map. -/
def Recipe.source (r : Recipe N P) : EndoSet := ⟨N, r.shape⟩

/-- The endo-set carried by the recipe's value map. -/
def Recipe.target (r : Recipe N P) : EndoSet := ⟨P, r.value⟩

theorem isFixed_iff_equivariant [DecidableEq N] (r : Recipe N P) (g : N → P) :
    IsFixed r g ↔ ∀ k, g (r.shape k) = r.value (g k) := by
  constructor
  · intro h k
    have := congrFun (h k) (r.shape k)
    simpa [update] using this.symm
  · intro h k
    funext j
    by_cases hj : j = r.shape k
    · subst j
      simp [update, h k]
    · simp [update, hj]

/-- **Central theorem.** Fixed rules are the hom-set of endo-sets. -/
def fixedEquivHom [DecidableEq N] (r : Recipe N P) :
    {g : N → P // IsFixed r g} ≃ EndoHom r.source r.target where
  toFun g := ⟨g.val, (isFixed_iff_equivariant r g.val).mp g.property⟩
  invFun f := ⟨f, (isFixed_iff_equivariant r f).mpr f.comm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Boolean negation and alternating colourings

**Naming caveat (claude-2 review, 2026-07-16).**  This section previously called
`HasAlternatingColouring` by the name `EveryCycleEven`, and stated the theorem
below as “fixed rules exist iff every cycle is even”.  That name promised what
the definition withholds: the predicate below is *definitionally* “an equivariant
two-colouring exists”, so the theorem was `A ↔ A`, provable by unfolding, and
nothing here mentions cycles, orbits, or parity.  Renamed to say what it means.

**The real cycle theorem is NOT proved here, and is worth proving.**  It is:

    HasAlternatingColouring s ↔ ∀ c ∈ s.cycleType, Even c

Follow a cycle of length `L`: equivariance forces `g k = (Bool.not)^[L] (g k)`,
and `(Bool.not)^[L] = id` exactly when `L` is even; conversely, colour each orbit
by the parity of the distance from a chosen representative.  Verified numerically
before it was ever stated in Lean: of the 40320 permutations of eight positions,
exactly **11025** admit an equivariant Boolean rule, and that set is *identical*
to the set whose cycles are all even.  Proving it wants `Equiv.Perm.cycleType` and
`Equiv.Perm.sameCycle` from mathlib; it is a genuine slice, not a rename.

Note the corollaries below (`identity_has_no_fixed`, `emacsBug_has_no_fixed`) do
**not** route through this section — they prove `IsEmpty` directly — so they stand
on their own regardless. -/

/-- There is a two-colouring of `N` that flips at every `s`-step.

This is exactly the shape of an equivariant map `(N, s) → (Bool, not)`, and is
stated here only to name that shape.  It is **not** a statement about cycles; see
the section docstring for the cycle-parity theorem this does not prove. -/
def HasAlternatingColouring (s : Equiv.Perm N) : Prop :=
  ∃ colour : N → Bool, ∀ k, colour (s k) = !colour k

/-- Boolean-negating fixed rules are exactly the alternating colourings.

Honest content: this unfolds `IsFixed` through `isFixed_iff_equivariant`.  It
carries no cycle-parity content — that is the open theorem in the section
docstring. -/
theorem bool_fixed_exists_iff_hasAlternatingColouring
    [DecidableEq N] (s : Equiv.Perm N) :
    Nonempty {g : N → Bool // IsFixed ⟨s, Bool.not⟩ g} ↔ HasAlternatingColouring s := by
  rw [nonempty_subtype]
  exact exists_congr fun g ↦ isFixed_iff_equivariant ⟨s, Bool.not⟩ g

/-- Identity propagation has no fixed Boolean rule: every point is a one-cycle. -/
theorem identity_has_no_fixed [Nonempty N] [DecidableEq N] :
    IsEmpty {g : N → Bool // IsFixed (⟨id, Bool.not⟩ : Recipe N Bool) g} := by
  constructor
  intro g
  let k : N := Classical.choice inferInstance
  have h := (isFixed_iff_equivariant (⟨id, Bool.not⟩ : Recipe N Bool) g.val).mp
    g.property k
  cases hg : g.val k <;> simp [hg] at h

/-! ## The actual non-permutation bug and its scaffold -/

/-- The 2014 Emacs destination map `k ↦ max (k - 1) 0`, on eight positions. -/
def emacsShift (k : Fin 8) : Fin 8 :=
  ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le k.val 1) k.isLt⟩

theorem emacsShift_zero : emacsShift 0 = 0 := rfl

/-- The parenthetical “permutation” in the source note does not apply to the Emacs bug. -/
theorem emacsShift_not_injective : ¬Function.Injective emacsShift := by
  intro h
  have hz : emacsShift 0 = emacsShift 1 := by decide
  have := h hz
  norm_num at this

/-- Bit seven has no preimage, so the Emacs map is not surjective either. -/
theorem emacsShift_not_surjective : ¬Function.Surjective emacsShift := by
  intro h
  obtain ⟨k, hk⟩ := h 7
  have hv := congrArg Fin.val hk
  change k.val - 1 = 7 at hv
  omega

/-- The fixed point at zero makes the Boolean constraint inconsistent. -/
theorem emacsBug_has_no_fixed :
    IsEmpty {g : Fin 8 → Bool // IsFixed (⟨emacsShift, Bool.not⟩ : Recipe (Fin 8) Bool) g} := by
  constructor
  intro g
  have h := (isFixed_iff_equivariant (⟨emacsShift, Bool.not⟩ : Recipe (Fin 8) Bool) g).mp
    g.property 0
  simp [emacsShift] at h

/-- Positions outside the image of `s` are never written, hence free. -/
def Free (s : N → N) : Set N := (Set.range s)ᶜ

theorem mem_free_iff_not_in_image (s : N → N) (x : N) :
    x ∈ Free s ↔ x ∉ Set.range s :=
  Iff.rfl

/-- For the Emacs bug the unique free position is bit seven. -/
theorem emacsShift_free : Free emacsShift = ({7} : Set (Fin 8)) := by
  classical
  ext k
  fin_cases k
  · simp [Free, emacsShift, Set.mem_range]
    exact ⟨0, rfl⟩
  · simp [Free, emacsShift, Set.mem_range]
    exact ⟨2, rfl⟩
  · simp [Free, emacsShift, Set.mem_range]
    exact ⟨3, rfl⟩
  · simp [Free, emacsShift, Set.mem_range]
    exact ⟨4, rfl⟩
  · simp [Free, emacsShift, Set.mem_range]
    exact ⟨5, rfl⟩
  · simp [Free, emacsShift, Set.mem_range]
    exact ⟨6, rfl⟩
  · simp [Free, emacsShift, Set.mem_range]
    exact ⟨7, rfl⟩
  · simp [Free, emacsShift, Set.mem_range]
    intro x h
    have hv := congrArg Fin.val h
    simp at hv
    exact (Nat.ne_of_lt x.isLt) hv

/-- A surjective shape map has no scaffold. -/
theorem free_eq_empty_of_surjective {s : N → N} (hs : Function.Surjective s) :
    Free s = ∅ := by
  ext x
  simp [Free, hs x]

/-- In particular, a permutation never has a free position. -/
theorem permutation_free_eq_empty (s : Equiv.Perm N) : Free s = ∅ :=
  free_eq_empty_of_surjective s.surjective

/-! ## Isomorphism invariance and the conjugate twins -/

/-- Precomposition by an endo-set isomorphism bijects the corresponding hom-sets. -/
def precompEquiv {A : EndoSet.{u}} {B : EndoSet.{v}} {P : EndoSet.{v'}}
    (e : EndoEquiv A B) : EndoHom A P ≃ EndoHom B P where
  toFun f :=
    ⟨fun b ↦ f (e.toEquiv.symm b), fun b ↦ by
      have hs : e.toEquiv.symm (B.step b) = A.step (e.toEquiv.symm b) := by
        apply e.toEquiv.injective
        simp [e.comm]
      rw [hs]
      exact f.comm (e.toEquiv.symm b)⟩
  invFun f := ⟨fun a ↦ f (e.toEquiv a), fun a ↦ by
    rw [e.comm]
    exact f.comm (e.toEquiv a)⟩
  left_inv f := by ext x; exact congrArg f (e.toEquiv.symm_apply_apply x)
  right_inv f := by ext x; exact congrArg f (e.toEquiv.apply_symm_apply x)

/-- Isomorphic shape endo-sets have bijective propagator fixed-point sets. -/
def fixedEquivOfShapeEquiv {A : EndoSet.{u}} {B : EndoSet.{u'}}
    [DecidableEq A.Carrier] [DecidableEq B.Carrier]
    (e : EndoEquiv A B) (ν : P → P) :
    {g : A.Carrier → P // IsFixed ⟨A.step, ν⟩ g} ≃
      {g : B.Carrier → P // IsFixed ⟨B.step, ν⟩ g} :=
  fixedEquivHom ⟨A.step, ν⟩ |>.trans
    ((precompEquiv e).trans (fixedEquivHom ⟨B.step, ν⟩).symm)

def liveTwin : Fin 8 → Fin 8 := ![2, 3, 4, 5, 6, 7, 0, 1]
def deadTwin : Fin 8 → Fin 8 := ![1, 2, 3, 0, 5, 6, 7, 4]
def twinRebase : Fin 8 → Fin 8 := ![0, 4, 1, 5, 2, 6, 3, 7]

noncomputable def twinRebaseEquiv : Fin 8 ≃ Fin 8 :=
  Equiv.ofBijective twinRebase (by native_decide)

theorem twinRebase_conjugates (k : Fin 8) :
    twinRebaseEquiv (liveTwin k) = deadTwin (twinRebaseEquiv k) := by
  fin_cases k <;> decide

/-- The live and dead conjugate twins have bijective fixed-point sets for every value map. -/
noncomputable def twinFixedPointEquiv (ν : P → P) :
    {g : Fin 8 → P // IsFixed ⟨liveTwin, ν⟩ g} ≃
      {g : Fin 8 → P // IsFixed ⟨deadTwin, ν⟩ g} :=
  fixedEquivOfShapeEquiv
    (A := ⟨Fin 8, liveTwin⟩) (B := ⟨Fin 8, deadTwin⟩)
    { toEquiv := twinRebaseEquiv
      comm := twinRebase_conjugates }
    ν

/-! ## Transfer eligibility -/

/-- An encoded operator is transfer-eligible only when it is induced by a shape/value recipe. -/
def TransferEligible [DecidableEq N] (op : N → (N → P) → (N → P)) : Prop :=
  ∃ r : Recipe N P, op = fun k g ↦ update r k g

/-- Transport a recipe along changes of shape and value coordinates. -/
def Recipe.transport (r : Recipe N P) (eN : N ≃ N') (eP : P ≃ P') : Recipe N' P' where
  shape := eN ∘ r.shape ∘ eN.symm
  value := eP ∘ r.value ∘ eP.symm

/-- Transport a rule in the exponential by rebasing its input and output coordinates. -/
def transportRule (eN : N ≃ N') (eP : P ≃ P') (g : N → P) : N' → P' :=
  eP ∘ g ∘ eN.symm

/-- Elementary propagator updates commute with transport to the new exponential. -/
theorem transport_update [DecidableEq N] [DecidableEq N']
    (r : Recipe N P) (eN : N ≃ N') (eP : P ≃ P') (k : N) (g : N → P) :
    transportRule eN eP (update r k g) =
      update (r.transport eN eP) (eN k) (transportRule eN eP g) := by
  funext j
  by_cases hj : j = eN (r.shape k)
  · subst j
    simp [transportRule, Recipe.transport, update]
  · have hj' : eN.symm j ≠ r.shape k := by
      intro h
      apply hj
      exact (eN.apply_symm_apply j).symm.trans (congrArg eN h)
    simp [transportRule, Recipe.transport, update, hj, hj']

/-- The same shape/value recipe remains eligible on the transported exponential. -/
theorem transported_is_eligible [DecidableEq N'] (r : Recipe N P) (eN : N ≃ N') (eP : P ≃ P') :
    TransferEligible (fun k g ↦ update (r.transport eN eP) k g) :=
  ⟨r.transport eN eP, rfl⟩

end DarkTower.Patterns.Propagator
