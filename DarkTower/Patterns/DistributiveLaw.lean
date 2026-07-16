import Mathlib

/-!
# Context/writer distributive laws for pattern arrows

This is slice 1 of `N-patterns-as-arrows`.  It separates the full context
comonad `W A = S → A` from a finite radius-one window.  The shape `S` must be
a monoid: its unit is the ego position and multiplication composes shifts.

For the writer `M A = (J × Sigma) × A`, both `J` and `Sigma` must be monoids.
There is a lawful mixed distributive law, but it retains only the annotation
at the ego position.  The tempting finite, commutative construction which
multiplies annotations over the whole context is *not* a distributive law:
it violates the counit axiom whenever the context has a non-ego point.  Thus
finiteness and commutativity do not repair the collecting proposal in the
note; collecting neighbour signs belongs outside this writer distributive
law (for example in a separate emission/coalgebra layer).
-/

namespace DarkTower.Patterns

/-- The translation shape used by an unbounded one-dimensional CA.  Its
multiplication is integer addition, so duplication composes genuine shifts
rather than wrapping a three-cell window. -/
abbrev IntegerShift := Multiplicative Int

/-- The exponential context functor.  A radius-one window is what a local
rule reads from this full context; it is not itself the shift comonad. -/
def Context (S A : Type*) := S → A

/-- The ego position is the monoid unit. -/
def Context.extract [One S] (x : Context S A) : A := x 1

/-- Contexts of contexts compose their shifts using the shape monoid. -/
def Context.duplicate [Mul S] (x : Context S A) : Context S (Context S A) :=
  fun s t => x (s * t)

theorem Context.extract_duplicate [Monoid S] (x : Context S A) :
    Context.extract (Context.duplicate x) = x := by
  funext s
  simp [Context.extract, Context.duplicate]

theorem Context.map_extract_duplicate [Monoid S] (x : Context S A) :
    (fun s => Context.extract (Context.duplicate x s)) = x := by
  funext s
  simp [Context.extract, Context.duplicate]

theorem Context.duplicate_duplicate [Monoid S] (x : Context S A) :
    Context.duplicate (Context.duplicate x) =
      (fun s => Context.duplicate (Context.duplicate x s)) := by
  funext s t u
  simp [Context.duplicate, mul_assoc]

@[simp] theorem Context.duplicate_one [Monoid S] (x : Context S A) :
    Context.duplicate x 1 = x := by
  funext s
  simp [Context.duplicate]

@[simp] theorem Context.duplicate_shift [Monoid S]
    (x : Context S A) (s t : S) :
    Context.duplicate (Context.duplicate x s) t =
      Context.duplicate x (s * t) := by
  funext u
  simp [Context.duplicate, mul_assoc]

/-- Writer effects.  For the note's proposed writer take `K = J × Sigma`;
Lean supplies its monoid exactly when both factors have monoid structure. -/
def Writer (K A : Type*) := K × A

def Writer.map (f : A → B) (x : Writer K A) : Writer K B := (x.1, f x.2)

def Writer.pure [One K] (a : A) : Writer K A := (1, a)

def Writer.join [Mul K] (x : Writer K (Writer K A)) : Writer K A :=
  (x.1 * x.2.1, x.2.2)

theorem Writer.join_pure [Monoid K] (x : Writer K A) :
    Writer.join (Writer.pure x) = x := by
  simp [Writer.join, Writer.pure]

theorem Writer.join_map_pure [Monoid K] (x : Writer K A) :
    Writer.join (Writer.map Writer.pure x) = x := by
  simp [Writer.join, Writer.map, Writer.pure]

theorem Writer.join_join [Monoid K] (x : Writer K (Writer K (Writer K A))) :
    Writer.join (Writer.join x) =
      Writer.join (Writer.map Writer.join x) := by
  simp [Writer.join, Writer.map, mul_assoc]

/-- The lawful context-over-writer distributive law.  It can transport the
whole value context, but the comonad counit forces the emitted writer effect
to be the effect at ego. -/
def egoLambda [One S] (x : Context S (Writer K A)) :
    Writer K (Context S A) :=
  ((x 1).1, fun s => (x s).2)

/-! The four mixed distributive-law axioms. -/

theorem egoLambda_counit [Monoid S] (x : Context S (Writer K A)) :
    Writer.map Context.extract (egoLambda x) = Context.extract x := by
  rfl

theorem egoLambda_unit [Monoid S] [Monoid K] (x : Context S A) :
    egoLambda (S := S) (K := K)
        (fun s => Writer.pure (K := K) (x s)) =
      Writer.pure (K := K) x := by
  rfl

theorem egoLambda_multiplication [Monoid S] [Monoid K]
    (x : Context S (Writer K (Writer K A))) :
    egoLambda (S := S) (K := K) (fun s => Writer.join (x s)) =
      Writer.join
        (Writer.map (egoLambda (S := S) (K := K))
          (egoLambda (S := S) (K := K) x)) := by
  rfl

theorem egoLambda_comultiplication [Monoid S] [Monoid K]
    (x : Context S (Writer K A)) :
    Writer.map Context.duplicate (egoLambda x) =
      egoLambda (fun s => egoLambda (Context.duplicate x s)) := by
  apply Prod.ext
  · simp [Writer.map, egoLambda, Context.duplicate]
  · funext s t
    simp [Writer.map, egoLambda, Context.duplicate]

/-- A checked package of the four equations needed to compose the context
comonad with the writer monad. -/
structure MixedDistributiveLaw (S K : Type) [Monoid S] [Monoid K] where
  lambda : {A : Type*} → Context S (Writer K A) → Writer K (Context S A)
  counit : ∀ {A} (x : Context S (Writer K A)),
    Writer.map Context.extract (lambda x) = Context.extract x
  unit : ∀ {A} (x : Context S A),
    @lambda A (fun s => Writer.pure (K := K) (x s)) =
      Writer.pure (K := K) x
  multiplication : ∀ {A} (x : Context S (Writer K (Writer K A))),
    @lambda A (fun s => Writer.join (x s)) =
      Writer.join (Writer.map (@lambda A) (@lambda (Writer K A) x))
  comultiplication : ∀ {A} (x : Context S (Writer K A)),
    Writer.map Context.duplicate (@lambda A x) =
      @lambda (Context S A)
        (fun s => @lambda A (Context.duplicate x s))

def egoDistributiveLaw (S K : Type) [Monoid S] [Monoid K] :
    MixedDistributiveLaw S K where
  lambda := egoLambda
  counit := egoLambda_counit
  unit := egoLambda_unit
  multiplication := egoLambda_multiplication
  comultiplication := egoLambda_comultiplication

/-- The note's `M A = J × Sigma × A`, with the missing hypotheses exposed.
There is no writer monad of this form until both `J` and `Sigma` have chosen
monoid structures. -/
abbrev PatternWriter (J Sigma A : Type*) := Writer (J × Sigma) A

def patternDistributiveLaw (S J Sigma : Type)
    [Monoid S] [Monoid J] [Monoid Sigma] :
    MixedDistributiveLaw S (J × Sigma) :=
  egoDistributiveLaw S (J × Sigma)

/-! ## The resulting biKleisli category -/

/-- The identity pattern is writer unit after context extraction. -/
def biIdentity [One S] [One K] : Context S A → Writer K A :=
  fun x => Writer.pure (Context.extract x)

/-- Cascade composition induced by `egoLambda`. -/
def biComp [Monoid S] [Monoid K]
    (g : Context S B → Writer K C)
    (f : Context S A → Writer K B) :
    Context S A → Writer K C :=
  fun x =>
    Writer.join
      (Writer.map g
        (egoLambda (fun s => f (Context.duplicate x s))))

theorem biComp_identity_left [Monoid S] [Monoid K]
    (f : Context S A → Writer K B) :
    biComp f biIdentity = f := by
  funext x
  have ego_values : (fun s => Context.duplicate x s 1) = x := by
    funext s
    simp [Context.duplicate]
  apply Prod.ext
  · simp [biComp, biIdentity, Writer.join, Writer.map, Writer.pure,
      egoLambda, Context.extract, ego_values]
  · simp [biComp, biIdentity, Writer.join, Writer.map, Writer.pure,
      egoLambda, Context.extract, ego_values]

theorem biComp_identity_right [Monoid S] [Monoid K]
    (f : Context S A → Writer K B) :
    biComp biIdentity f = f := by
  funext x
  apply Prod.ext
  · simp [biComp, biIdentity, Writer.join, Writer.map, Writer.pure,
      egoLambda, Context.extract]
  · simp [biComp, biIdentity, Writer.join, Writer.map, Writer.pure,
      egoLambda, Context.extract]

theorem biComp_assoc [Monoid S] [Monoid K]
    (h : Context S C → Writer K D)
    (g : Context S B → Writer K C)
    (f : Context S A → Writer K B) :
    biComp h (biComp g f) = biComp (biComp h g) f := by
  funext x
  have shift_values (s : S) :
      (fun t => (f (Context.duplicate x (s * t))).2) =
        Context.duplicate (fun r => (f (Context.duplicate x r)).2) s := by
    rfl
  apply Prod.ext
  · simp [biComp, Writer.join, Writer.map, egoLambda, shift_values, mul_assoc]
  · simp [biComp, Writer.join, Writer.map, egoLambda, shift_values, mul_assoc]

/-- The map asserted in the note: multiply every annotation in a finite
context.  `CommMonoid K` makes the finite product independent of enumeration,
but does not make this map a distributive law. -/
def collectLambda [Fintype S] [CommMonoid K]
    (x : Context S (Writer K A)) : Writer K (Context S A) :=
  (∏ s, (x s).1, fun s => (x s).2)

/-- On every context with a non-ego point, collection fails the counit law,
already for the commutative writer monoid `Nat`.  This is the requested
counterexample to the note's proposed collecting `lambda`. -/
theorem collectLambda_counit_counterexample
    [Monoid S] [Fintype S] [DecidableEq S]
    (other : S) (hother : other ≠ 1) :
    let x : Context S (Writer Nat Unit) :=
      fun s => (if s = other then 0 else 1, ())
    Writer.map Context.extract (collectLambda x) ≠ Context.extract x := by
  dsimp
  intro equality
  have hproduct :
      (∏ s : S, if s = other then 0 else 1) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ other)
    simp
  have hego : (if (1 : S) = other then 0 else 1) = 1 := by
    simp [Ne.symm hother]
  have effects := congrArg Prod.fst equality
  simp only [Writer.map, collectLambda, Context.extract] at effects
  rw [hproduct, hego] at effects
  omega

/-- A fixed boundary value cannot be chosen naturally for every carrier in
`Type`: the empty carrier has no candidate.  Consequently a finite line with
a distinguished Rule-0/state-0 boundary is not this Set-level context comonad
without changing the ambient category to pointed types (and then proving that
the dynamics preserves the point). -/
theorem no_uniform_fixed_boundary : ¬ (∀ A : Type, Nonempty A) := by
  intro boundary
  rcases boundary Empty with ⟨value⟩
  exact nomatch value

end DarkTower.Patterns
