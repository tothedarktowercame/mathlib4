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

The signed-cycle fixed-point theorem specialized to this action is proved below:

    HasAlternatingColouring s ↔
      s.support = Finset.univ ∧ ∀ c ∈ s.cycleType, Even c

Follow a cycle of length `L`: equivariance forces `g k = (Bool.not)^[L] (g k)`,
and `(Bool.not)^[L] = id` exactly when `L` is even; conversely, colour each orbit
by the parity of the distance from a chosen representative.  Verified numerically
before it was ever stated in Lean: of the 40320 permutations of eight positions,
exactly **11025** admit an equivariant Boolean rule.  Since mathlib's `cycleType`
omits one-cycles, the support condition is essential: it excludes fixed points,
while `cycleType` records the parity of every remaining cycle.  The proof uses
`Equiv.Perm.cycleType` and `Equiv.Perm.SameCycle`; it is a genuine cycle argument,
not a rename.

Note the corollaries below (`identity_has_no_fixed`, `emacsBug_has_no_fixed`) do
**not** route through this section — they prove `IsEmpty` directly — so they stand
on their own regardless. -/

/-- There is a two-colouring of `N` that flips at every `s`-step.

This is exactly the shape of an equivariant map `(N, s) → (Bool, not)`, and is
stated here only to name that shape.  The theorem below gives its cycle-parity
characterization. -/
def HasAlternatingColouring (s : Equiv.Perm N) : Prop :=
  ∃ colour : N → Bool, ∀ k, colour (s k) = !colour k

private lemma iterate_not_eq_self_iff_even (n : ℕ) (b : Bool) :
    (Bool.not^[n]) b = b ↔ Even n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => cases b <;> simp
  | more n ih0 _ =>
      rw [show Bool.not^[n + 2] b = Bool.not^[n] b by
        rw [show n + 2 = n + 1 + 1 by omega, Function.iterate_succ_apply,
          Function.iterate_succ_apply, Bool.not_not]]
      apply ih0.trans
      rw [Nat.even_iff, Nat.even_iff]
      omega

private lemma iterate_not_apply_not (n : ℕ) (b : Bool) :
    (Bool.not^[n]) (!b) = !(Bool.not^[n]) b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, Bool.not_not, ih]

private lemma alternating_pow (s : Equiv.Perm N) (colour : N → Bool)
    (h : ∀ k, colour (s k) = !colour k) (n : ℕ) (k : N) :
    colour ((s ^ n) k) = (Bool.not^[n]) (colour k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, h, Function.iterate_succ_apply, ih,
        iterate_not_apply_not]

private lemma even_of_alternating_pow_fixed (s : Equiv.Perm N) (colour : N → Bool)
    (h : ∀ k, colour (s k) = !colour k) {n : ℕ} {k : N}
    (hfix : (s ^ n) k = k) : Even n := by
  have hi := alternating_pow s colour h n k
  rw [hfix] at hi
  exact (iterate_not_eq_self_iff_even n (colour k)).mp hi.symm

private noncomputable def cycleRep [Fintype N] [DecidableEq N]
    (s : Equiv.Perm N) (_hfree : s.support = Finset.univ) (k : N) : N :=
  if h : (s.cycleOf k).support.Nonempty then Classical.choose h else k

private lemma cycleRep_mem [Fintype N] [DecidableEq N]
    (s : Equiv.Perm N) (hfree : s.support = Finset.univ) (k : N) :
    cycleRep s hfree k ∈ (s.cycleOf k).support := by
  have hne : (s.cycleOf k).support.Nonempty := Equiv.Perm.support_cycleOf_nonempty.mpr <| by
    rw [← Equiv.Perm.mem_support, hfree]
    exact Finset.mem_univ k
  simp only [cycleRep, dif_pos hne]
  exact Classical.choose_spec hne

private lemma cycleRep_apply [Fintype N] [DecidableEq N]
    (s : Equiv.Perm N) (hfree : s.support = Finset.univ) (k : N) :
    cycleRep s hfree (s k) = cycleRep s hfree k := by
  have hc := s.cycleOf_self_apply k
  have hk : (s.cycleOf k).support.Nonempty := Equiv.Perm.support_cycleOf_nonempty.mpr <| by
    rw [← Equiv.Perm.mem_support, hfree]
    exact Finset.mem_univ k
  simp only [cycleRep, hc, dif_pos hk]

private lemma mem_toList_cycleRep [Fintype N] [DecidableEq N]
    (s : Equiv.Perm N) (hfree : s.support = Finset.univ) (k : N) :
    k ∈ s.toList (cycleRep s hfree k) := by
  rw [Equiv.Perm.mem_toList_iff]
  have hk : k ∈ s.support := by simp [hfree]
  have hr := cycleRep_mem s hfree k
  have hsame : s.SameCycle k (cycleRep s hfree k) :=
    (Equiv.Perm.mem_support_cycleOf_iff' (f := s) (x := k) (y := cycleRep s hfree k)
      (by simpa [Equiv.Perm.mem_support] using hk)).mp hr
  exact ⟨hsame.symm, hsame.mem_support_iff.mp hk⟩

private lemma cycleRep_length_even [Fintype N] [DecidableEq N]
    (s : Equiv.Perm N) (hfree : s.support = Finset.univ)
    (heven : ∀ c ∈ s.cycleType, Even c) (k : N) :
    Even (s.toList (cycleRep s hfree k)).length := by
  rw [Equiv.Perm.length_toList]
  apply heven
  rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
  refine ⟨s.cycleOf (cycleRep s hfree k), ?_, rfl⟩
  rw [← Finset.mem_def, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
    show s.support = Finset.univ from hfree]
  exact Finset.mem_univ _

private lemma cycleRep_idx_apply [Fintype N] [DecidableEq N]
    (s : Equiv.Perm N) (hfree : s.support = Finset.univ) (k : N) :
    List.idxOf (s k) (s.toList (cycleRep s hfree k)) =
      (List.idxOf k (s.toList (cycleRep s hfree k)) + 1) %
        (s.toList (cycleRep s hfree k)).length := by
  let l := s.toList (cycleRep s hfree k)
  have hk : k ∈ l := mem_toList_cycleRep s hfree k
  have hsnext : s k = l.next k hk := (Equiv.Perm.next_toList_eq_apply _ _ _ hk).symm
  rw [hsnext, List.next_eq_getElem]
  exact (Equiv.Perm.nodup_toList _ _).idxOf_getElem _ _

/-- A Lean formalization of the signed-cycle fixed-point criterion, specialized to
`bit[s k] = ¬bit[k]`: an alternating colouring exists exactly when there are no
fixed points and every nontrivial cycle has even length. -/
theorem hasAlternatingColouring_iff_cycleType_even [Fintype N] [DecidableEq N]
    (s : Equiv.Perm N) :
    HasAlternatingColouring s ↔
      s.support = Finset.univ ∧ ∀ c ∈ s.cycleType, Even c := by
  constructor
  · rintro ⟨colour, hcolour⟩
    constructor
    · ext k
      simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
      intro hfix
      have h := hcolour k
      rw [hfix] at h
      cases colour k <;> simp at h
    · intro c hc
      rw [Equiv.Perm.cycleType_def, Multiset.mem_map] at hc
      obtain ⟨d, hd, rfl⟩ := hc
      have hdf : d ∈ s.cycleFactorsFinset := Finset.mem_def.mpr hd
      have hdc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hdf).1
      obtain ⟨k, hk⟩ := hdc.nonempty_support
      apply even_of_alternating_pow_fixed s colour hcolour (k := k)
      change (s ^ d.support.card) k = k
      rw [← Equiv.Perm.cycleOf_pow_apply_self s k,
        ← s.cycle_is_cycleOf hk hdf, ← hdc.orderOf, pow_orderOf_eq_one,
        Equiv.Perm.one_apply]
  · rintro ⟨hfree, heven⟩
    let colour : N → Bool := fun k => decide (Odd <|
      List.idxOf k (s.toList (cycleRep s hfree k)))
    refine ⟨colour, fun k => ?_⟩
    have hrep := cycleRep_apply s hfree k
    have hidx := cycleRep_idx_apply s hfree k
    have hlen := cycleRep_length_even s hfree heven k
    have hlen' : Even (s.cycleOf (cycleRep s hfree k)).support.card := by
      simpa only [Equiv.Perm.length_toList] using hlen
    simp only [colour, hrep, hidx]
    rw [← decide_not]
    apply decide_eq_decide.mpr
    simpa only [Equiv.Perm.length_toList] using
      ((Odd.mod_even_iff hlen').trans Nat.odd_add_one)

/-- For the eight-bit specialization, every alternating colouring has four true
bits. Thus its Langton parameter is `4 / 8 = 1 / 2`. -/
theorem alternatingColouring_true_card_eq_four (s : Equiv.Perm (Fin 8))
    (colour : Fin 8 → Bool) (hcolour : ∀ k, colour (s k) = !colour k) :
    (Finset.univ.filter fun k => colour k).card = 4 := by
  have _hcycles : ∀ c ∈ s.cycleType, Even c :=
    (hasAlternatingColouring_iff_cycleType_even s).mp ⟨colour, hcolour⟩ |>.2
  let toFalse : {k : Fin 8 // colour k = true} → {k : Fin 8 // colour k = false} :=
    fun k => ⟨s k, by rw [hcolour k, k.property]; rfl⟩
  let toTrue : {k : Fin 8 // colour k = false} → {k : Fin 8 // colour k = true} :=
    fun k => ⟨s.symm k, by
      have h := hcolour (s.symm k)
      simp only [s.apply_symm_apply] at h
      cases hk : colour (s.symm k)
      · have ht : colour (k : Fin 8) = true := by simpa [hk] using h
        rw [k.property] at ht
        contradiction
      · rfl⟩
  let e : {k : Fin 8 // colour k = true} ≃ {k : Fin 8 // colour k = false} :=
    Equiv.mk toFalse toTrue
      (fun k => by apply Subtype.ext; exact s.symm_apply_apply k)
      (fun k => by apply Subtype.ext; exact s.apply_symm_apply k)
  have hcard : Fintype.card {k : Fin 8 // colour k = true} =
      Fintype.card {k : Fin 8 // colour k = false} := Fintype.card_congr e
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun k : Fin 8 => colour k)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hfalse : (Finset.univ.filter fun k : Fin 8 => ¬(colour k = true)) =
      Finset.univ.filter fun k : Fin 8 => colour k = false := by
    ext k
    cases colour k <;> simp
  rw [hfalse] at hsum
  rw [Fintype.card_subtype, Fintype.card_subtype] at hcard
  omega

/-- Alternating colourings, as a finite type for counting statements. -/
def AlternatingColouring [Fintype N] (s : Equiv.Perm N) :=
  {colour : N → Bool // ∀ k, colour (s k) = !colour k}

noncomputable instance alternatingColouringFintype [Fintype N]
    (s : Equiv.Perm N) : Fintype (AlternatingColouring s) :=
  Fintype.ofInjective (fun colour => colour.1) Subtype.val_injective

/-- The existence/zero part of the signed-cycle colouring count: the finite type
of alternating colourings is nonempty exactly under the corrected cycle condition.
The sharper cardinality `2 ^ s.cycleType.card` requires a separate orbit-choice
equivalence. -/
theorem alternatingColouring_card_pos_iff [Fintype N] [DecidableEq N]
    (s : Equiv.Perm N) :
    0 < Fintype.card (AlternatingColouring s) ↔
      s.support = Finset.univ ∧ ∀ c ∈ s.cycleType, Even c := by
  rw [Fintype.card_pos_iff]
  constructor
  · rintro ⟨⟨colour, hcolour⟩⟩
    exact (hasAlternatingColouring_iff_cycleType_even s).mp ⟨colour, hcolour⟩
  · intro hcycles
    obtain ⟨colour, hcolour⟩ :=
      (hasAlternatingColouring_iff_cycleType_even s).mpr hcycles
    exact ⟨⟨colour, hcolour⟩⟩

/-- A fixed point or a recorded odd cycle forces the alternating-colouring count
to be zero. This is the zero branch of the signed-cycle counting theorem. -/
theorem alternatingColouring_card_eq_zero_iff [Fintype N] [DecidableEq N]
    (s : Equiv.Perm N) :
    Fintype.card (AlternatingColouring s) = 0 ↔
      ¬(s.support = Finset.univ ∧ ∀ c ∈ s.cycleType, Even c) := by
  constructor
  · intro hzero hcycles
    have hpos := (alternatingColouring_card_pos_iff s).mpr hcycles
    omega
  · intro hcycles
    apply Nat.eq_zero_of_not_pos
    exact fun hpos => hcycles ((alternatingColouring_card_pos_iff s).mp hpos)

/-- Boolean-negating fixed rules are exactly the alternating colourings.

Honest content: this unfolds `IsFixed` through `isFixed_iff_equivariant`.  It
carries no cycle-parity content; that is supplied by
`hasAlternatingColouring_iff_cycleType_even`. -/
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

/-- **A propagator has a scaffold iff its shape map is not surjective.**

The forward direction alone was stated; the cascade reading (claude-6, 2026-07-16)
needs the biconditional, so that FREE stops being an observation repeated in three
places and becomes one theorem.  Non-surjectivity is not a side-condition on the
mechanism — it *is* the mechanism: `s` must miss something for anything to be held
still. -/
theorem free_eq_empty_iff_surjective {s : N → N} :
    Free s = ∅ ↔ Function.Surjective s := by
  constructor
  · intro h x
    by_contra hx
    have hmem : x ∈ Free s := hx
    rw [h] at hmem
    exact hmem
  · exact free_eq_empty_of_surjective

/-- The contrapositive — the form the cascade reading actually uses:
**there is a scaffold exactly when the shape map misses something.** -/
theorem free_nonempty_iff_not_surjective {s : N → N} :
    (Free s).Nonempty ↔ ¬ Function.Surjective s := by
  rw [Set.nonempty_iff_ne_empty, ne_eq, free_eq_empty_iff_surjective]

/-- In particular, a permutation never has a free position.

Read with `free_nonempty_iff_not_surjective`, this says the permutation family is
not merely a narrower case than `s : N → N` — it is **disjoint from the mechanism**.
Every permutation is onto, hence has `FREE = ∅`, hence no scaffold. A census over
`Equiv.Perm` is a census of exactly the maps that cannot exhibit the phenomenon. -/
theorem permutation_free_eq_empty (s : Equiv.Perm N) : Free s = ∅ :=
  free_eq_empty_of_surjective s.surjective

/-! ## What the value map must be

claude-6 (lucy) asked whether `TransferEligible` forces `nu` to be an involution.
It does not: `Recipe` asks for nothing but two endo-maps, and `TransferEligible`
only asks that an operator factor through *some* `Recipe`.  But that is the wrong
question.  The property that bites is **fixed-point-freeness**, and it bites hard:
one fixed point in `nu` kills the propagator for *every* shape map at once. -/

/-- **If `nu` has any fixed point, the propagator settles — whatever `s` is.**

The constant colouring at `p` satisfies the constraint for every shape map, so the
fixed-point set is never empty and the carrier always has somewhere to come to
rest.  A carrier that settles is dead (Figure 8 moves precisely because it has no
fixed point).  So the requirement on `nu` is not that it be an involution but that
it have no fixed point; `Bool.not` qualifies, which is why the MetaCA runs at all. -/
theorem settles_if_nu_has_fixed_point [DecidableEq N]
    (s : N → N) (nu : P → P) (p : P) (hfix : nu p = p) :
    IsFixed (⟨s, nu⟩ : Recipe N P) (fun _ => p) := by
  rw [isFixed_iff_equivariant]
  intro k
  simp [hfix]

/-- Contrapositive: a propagator with *no* solution forces `nu` to be
fixed-point-free.  This is the form the design reading uses — before building a
controlled vocabulary, test the candidate `nu` for fixed points; any term mapping
to itself is dead on arrival for every `s`. -/
theorem nu_fixed_point_free_of_isEmpty [DecidableEq N]
    (s : N → N) (nu : P → P)
    (h : IsEmpty {g : N → P // IsFixed (⟨s, nu⟩ : Recipe N P) g}) :
    ∀ p, nu p ≠ p := by
  intro p hp
  exact h.elim ⟨fun _ => p, settles_if_nu_has_fixed_point s nu p hp⟩

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
