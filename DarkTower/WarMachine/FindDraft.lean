import DarkTower.WarMachine.Holes

/-!
# Draft `find` interface

This is a standalone draft for Joe's later `Holes.lean` merge.  It imports the
closed `Repository` and `Tension` records rather than reopening them; their
authoritative shapes remain at `Holes.lean:121-130`.
-/

namespace DarkTower.WarMachine.FindDraft

open DarkTower.WarMachine.Holes

universe u v w

/-- The ruled route vocabulary starts with the executable default at
`futon3:checks/find_organise.clj:241`.  Further routes require an explicit
constructor rather than an untyped value. -/
inductive Route where
  | structuredAntecedent
  deriving DecidableEq, Repr

/-- A query keeps the domain-specific antecedent test outside the closed
`Tension` record.  This mirrors `find_organise.clj:230-242`: the predicate reads
a pattern and the tension context. -/
structure FindQuery (State : Type u) (P : Type v) where
  tension : Tension State
  fires? : P → State → Prop

/-- A warrant is a nonempty descent chain rooted at the selected pattern.
Both its adjacency proof and its relation come from this repository's
`standsOn`; the query has no warrant field with which to certify itself. -/
structure Warrant {P : Type v} (R : Repository P) (pattern : P) where
  descent : List P
  rooted : descent.head? = some pattern
  standsOnChain : descent.IsChain R.standsOn

/-- A receipt cannot omit its route or its repository-indexed warrant. -/
structure Receipt {P : Type v} (R : Repository P) (pattern : P)
    (Extra : Type w) where
  route : Route
  warrant : Warrant R pattern
  extra : Extra

/-- The laws observable at the abstract boundary are proof-carrying fields.
In particular, the dependent receipt field makes an unreceipted selection
unrepresentable. -/
structure FindResult {State : Type u} {P : Type v} (q : FindQuery State P)
    (R : Repository P) (Extra : Type w) where
  selected : List P
  contained : ∀ p ∈ selected, p ∈ R.patterns
  receipts : ∀ p ∈ selected, Receipt R p Extra
  fires : ∀ p ∈ selected, q.fires? p q.tension.context

/-- Abstract draft boundary.  The executable implementation that filters
`R.patterns`, constructs `standsOn` warrants, and emits receipts is
`futon3:checks/find_organise.clj:227-253`; Joe's later merge supplies that
implementation without changing this Prop-level interface. -/
axiom find {State : Type u} {P : Type v} {Extra : Type w}
    (q : FindQuery State P) (R : Repository P) : FindResult q R Extra

/-- F1 — every selected pattern belongs to the queried repository. -/
theorem find_containment {State : Type u} {P : Type v} {Extra : Type w}
    (q : FindQuery State P) (R : Repository P) :
    ∀ p ∈ (find (Extra := Extra) q R).selected, p ∈ R.patterns :=
  (find (Extra := Extra) q R).contained

/-- F2 — every selection has a receipt; this is a projection, not an
existential postcondition. -/
theorem find_receipted {State : Type u} {P : Type v} {Extra : Type w}
    (q : FindQuery State P) (R : Repository P) :
    ∀ p ∈ (find (Extra := Extra) q R).selected,
      Nonempty (Receipt R p Extra) := by
  intro p hp
  exact ⟨(find (Extra := Extra) q R).receipts p hp⟩

/-- F3 — every selected receipt's warrant is a chain under the repository's
own `standsOn` relation, so `fires?` cannot self-certify it. -/
theorem find_warrant_standsOn {State : Type u} {P : Type v} {Extra : Type w}
    (q : FindQuery State P) (R : Repository P) :
    ∀ p (hp : p ∈ (find (Extra := Extra) q R).selected),
      ((find (Extra := Extra) q R).receipts p hp).warrant.descent.IsChain
        R.standsOn := by
  intro p hp
  exact ((find (Extra := Extra) q R).receipts p hp).warrant.standsOnChain

/-- F4 — selection is falsifiable by the caller-supplied antecedent test. -/
theorem find_falsifiable {State : Type u} {P : Type v} {Extra : Type w}
    (q : FindQuery State P) (R : Repository P) :
    ∀ p ∈ (find (Extra := Extra) q R).selected,
      q.fires? p q.tension.context :=
  (find (Extra := Extra) q R).fires

end DarkTower.WarMachine.FindDraft
