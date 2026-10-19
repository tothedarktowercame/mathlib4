import DarkTower.WarMachine.ThreeHalvesBlend

/-!
# Memory conflict as its own predicate (pattern M3)

First formal specification of pattern M3 of the memory-2026 working paper
("Contradiction as an Open Obligation"), in the same encoding the
3/2-blend carrier uses: claims are `Nat × Nat × Nat` axioms of a
`DarkTower.WarMachine.ThreeHalvesBlend.Theory`.

What this module states: a claim schema (functional relations, polarity
pairing), a decidable `conflict` predicate between two claims, and
`Theory.semanticallyConsistent` (no two axioms conflict), with theorems:
symmetry, irreflexivity, the corner-store witness, a non-functional
counterexample, the negation-pair witness, and downward monotonicity.

What it does NOT do: it does not touch cones or blends. `Cone.consistent`
still only checks that route maps are functional; binding semantic
consistency to the carrier's admissible cones is the next packet.

Source: minus40 `docs/SPEC-open-items.md` §6.3 (esp. the codex-68 finding
in §6.1 that `Cone.consistent` lets `located-at(store, 23rd St)` and
`located-at(store, 40th St)` blend without complaint); pattern M3 of the
p4ng memory-2026 working paper.
-/

namespace DarkTower.MemoryClaims

open DarkTower.WarMachine.ThreeHalvesBlend

/-- A claim schema: which relations are functional (at most one value per
subject), and a partial polarity pairing `negations` mapping a relation to
its negation, if it has one.

The pairing is symmetric **by hypothesis** (`neg_symm`) and irreflexive
(`neg_irrefl`): a relation never negates itself, so a claim can never
conflict with itself through the polarity clause. -/
structure Schema where
  functional : Finset Nat
  negations : Nat → Option Nat
  neg_symm : ∀ r r', negations r = some r' → negations r' = some r
  neg_irrefl : ∀ r r', negations r = some r' → r ≠ r'

/-- The underlying proposition of `conflict`: two claims are jointly
unsatisfiable under the schema. -/
@[reducible]
def conflictClaim (S : Schema) (a b : Nat × Nat × Nat) : Prop :=
  -- same functional relation, same subject, different values
  (a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 ≠ b.2.2 ∧ a.1 ∈ S.functional)
  ∨
  -- negation of the relation, same subject and value
  (S.negations a.1 = some b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 = b.2.2)

/-- `conflict S a b` is `true` exactly when the two claims are jointly
unsatisfiable under the schema (see `conflictClaim`). -/
def conflict (S : Schema) (a b : Nat × Nat × Nat) : Bool :=
  decide (conflictClaim S a b)

/-- A theory is semantically consistent when no two of its axioms
conflict. This is the §6.3 predicate that `Cone.consistent` is missing. -/
def Theory.semanticallyConsistent (S : Schema) (T : Theory) : Bool :=
  decide (∀ a ∈ T.axioms, ∀ b ∈ T.axioms, ¬ conflictClaim S a b)

/-! ## Basic properties -/

theorem conflictClaim_symm (S : Schema) (a b : Nat × Nat × Nat) (h : conflictClaim S a b) :
    conflictClaim S b a := by
  obtain ⟨r, x, y⟩ := a
  obtain ⟨r', x', y'⟩ := b
  simp only [conflictClaim] at h ⊢
  rcases h with ⟨rfl, rfl, hy, hf⟩ | ⟨hn, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, Ne.symm hy, hf⟩
  · exact Or.inr ⟨S.neg_symm _ _ hn, rfl, rfl⟩

/-- `conflict` is symmetric. -/
theorem conflict_symm (S : Schema) (a b : Nat × Nat × Nat) :
    conflict S a b = conflict S b a := by
  by_cases h1 : conflictClaim S a b <;> by_cases h2 : conflictClaim S b a
  · simp [conflict, h1, h2]
  · exact absurd (conflictClaim_symm S a b h1) h2
  · exact absurd (conflictClaim_symm S b a h2) h1
  · simp [conflict, h1, h2]

/-- An axiom never conflicts with itself. -/
theorem conflict_irrefl (S : Schema) (a : Nat × Nat × Nat) :
    conflict S a a = false := by
  rw [conflict, Bool.eq_false_iff, ne_eq, decide_eq_true_eq]
  rintro (⟨_, _, hy, _⟩ | ⟨hn, _, _⟩)
  · exact hy rfl
  · exact S.neg_irrefl _ _ hn rfl

/-! ## The corner store (SPEC §6.1 / §6.3) -/

/-- Relation ids and entities for the corner-store witnesses:
`locatedAt = 0`, `store = 1`, `street23 = 2`, `street40 = 3`, `sells = 4`,
`coffee = 5`, `negLocatedAt = 6`, `candy = 7`. -/
def locatedAt : Nat := 0
def store : Nat := 1
def street23 : Nat := 2
def street40 : Nat := 3
def sells : Nat := 4
def coffee : Nat := 5
def negLocatedAt : Nat := 6
def candy : Nat := 7

/-- The polarity pairing of the corner-store schema: only `locatedAt` and
its negation are paired. -/
def negStore : Nat → Option Nat
  | 0 => some 6
  | 6 => some 0
  | _ => none

/-- The corner-store schema: `located-at` functional, `sells` not; only
`locatedAt` has a negation. -/
def S_store : Schema where
  functional := {locatedAt}
  negations := negStore
  neg_symm := by
    intro r r' h
    by_cases h0 : r = 0 <;> by_cases h6 : r = 6 <;>
      by_cases h0' : r' = 0 <;> by_cases h6' : r' = 6 <;>
      simp_all [negStore]
  neg_irrefl := by
    intro r r' h
    by_cases h0 : r = 0 <;> by_cases h6 : r = 6 <;>
      by_cases h0' : r' = 0 <;> by_cases h6' : r' = 6 <;>
      simp_all [negStore]

/-- §6.1's witness: with `located-at` functional, a theory holding both
`located-at(store, 23rd)` and `located-at(store, 40th)` is NOT
semantically consistent, even though every route map stays functional. -/
theorem corner_store_inconsistent :
    Theory.semanticallyConsistent S_store
        { elems := {locatedAt, negLocatedAt, store, street23, street40}
          axioms := {(locatedAt, store, street23), (locatedAt, store, street40)} } = false := by
  decide

/-- A non-functional relation (§6.3 "predicates declare cardinality"):
`sells(store, coffee)` and `sells(store, candy)` do not conflict. -/
theorem nonfunctional_two_values_consistent :
    Theory.semanticallyConsistent S_store
        { elems := {sells, store, coffee, candy}
          axioms := {(sells, store, coffee), (sells, store, candy)} } = true := by
  decide

/-- Opposite polarities for the same grounded claim (§6.3): a claim and
its negation on the same `(subject, value)` are not consistent. -/
theorem negation_pair_inconsistent :
    Theory.semanticallyConsistent S_store
        { elems := {locatedAt, negLocatedAt, store, street23}
          axioms := {(locatedAt, store, street23), (negLocatedAt, store, street23)} } = false := by
  decide

/-! ## Monotonicity -/

/-- Semantic consistency is monotone downward: any sub-theory (axioms
subset) of a semantically consistent theory is semantically consistent. -/
theorem semanticallyConsistent_mono {S : Schema} {T T' : Theory}
    (h : Theory.semanticallyConsistent S T = true) (hsub : T'.axioms ⊆ T.axioms) :
    Theory.semanticallyConsistent S T' = true := by
  simp only [Theory.semanticallyConsistent, decide_eq_true_eq] at h ⊢
  intro a ha b hb
  exact h a (hsub ha) b (hsub hb)

end DarkTower.MemoryClaims
