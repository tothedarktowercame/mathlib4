import Mathlib
import DarkTower.Comb
import DarkTower.Fill

/-!
# Scope as query

This file gives a first-order, finite model of scope-as-query.  A query is a
partial role-keyed hyperedge; answering it against a finite store fills the
variable ends with matching nodes.

Grounding:
* Spivak, *Polynomial functors: a mathematical theory of interaction*
  (with Niu, arXiv:2312.00990), treats interaction/query interfaces by
  polynomial maps into systems such as stores.
* Spivak's Poly viewpoint reads a query as a map into a store interface: the
  open directions are precisely the holes to be filled by an answer.
* nLab's page "representable presheaf" gives the semantic slogan: a partial
  hyperedge is represented by its probes/maps into the store.
* mathlib's `CategoryTheory.Yoneda`/`Yoneda.lean` supplies the categorical
  Yoneda substrate.  This file intentionally does not build that presheaf
  instance; it keeps the executable list unifier needed by DarkTower.
-/

namespace DarkTower

open CategoryTheory

universe uK uR uN uV

namespace ScopeQuery

/-- A hyperedge signature: callers supply edge kinds and role labels. -/
structure Sig where
  /-- The type of hyperedge kinds. -/
  Kind : Type uK
  /-- The type of role labels at hyperedge ends. -/
  Role : Type uR

/-- A ground role-keyed hyperedge over nodes `N`. -/
structure HEdge (S : Sig.{uK, uR}) (N : Type uN) where
  /-- The kind/predicate of the edge. -/
  kind : S.Kind
  /-- The ordered finite list of role-keyed node ends. -/
  ends : List (S.Role × N)

/-- A query end is either a variable hole or a bound node at a given role. -/
abbrev QEnd (S : Sig.{uK, uR}) (N : Type uN) (V : Type uV) :=
  S.Role × (V ⊕ N)

/-- A query is a partial hyperedge whose ends may contain variables. -/
structure Query (S : Sig.{uK, uR}) (N : Type uN) (V : Type uV) where
  /-- The kind/predicate being queried. -/
  kind : S.Kind
  /-- Ordered role-keyed ends, where `Sum.inl v` is a hole and `Sum.inr n` is bound. -/
  ends : List (QEnd S N V)

/-- A finite ground store. -/
abbrev Store (S : Sig.{uK, uR}) (N : Type uN) :=
  List (HEdge S N)

/-- A variable assignment produced by answering a query. -/
abbrev Binding (V : Type uV) (N : Type uN) :=
  V → Option N

namespace Binding

/-- The empty assignment. -/
def empty : Binding V N :=
  fun _ => none

/--
Insert a variable binding.  Repeated occurrences of the same variable must
agree with the node already assigned to that variable.
-/
def insert [DecidableEq V] [DecidableEq N] (ρ : Binding V N) (v : V) (n : N) :
    Option (Binding V N) :=
  match ρ v with
  | none => some fun w => if w = v then some n else ρ w
  | some n' => if n' = n then some ρ else none

@[simp]
theorem empty_apply (v : V) : empty (N := N) v = none :=
  rfl

@[simp]
theorem insert_empty_self [DecidableEq V] [DecidableEq N] (v : V) (n : N) :
    insert (N := N) empty v n = some (fun w => if w = v then some n else none) :=
  rfl

end Binding

variable {S : Sig.{uK, uR}} {N : Type uN} {V : Type uV}

/-- Unify one query end against one ground edge end, extending the binding. -/
def unifyEnd [DecidableEq S.Role] [DecidableEq N] [DecidableEq V]
    (qe : QEnd S N V) (he : S.Role × N) (ρ : Binding V N) :
    Option (Binding V N) :=
  if qe.1 = he.1 then
    match qe.2 with
    | Sum.inl v => Binding.insert ρ v he.2
    | Sum.inr n => if n = he.2 then some ρ else none
  else
    none

/-- Unify ordered query ends against ordered ground ends. -/
def unifyEnds [DecidableEq S.Role] [DecidableEq N] [DecidableEq V] :
    List (QEnd S N V) → List (S.Role × N) → Binding V N → Option (Binding V N)
  | [], [], ρ => some ρ
  | qe :: qes, he :: hes, ρ => do
      let ρ' ← unifyEnd qe he ρ
      unifyEnds qes hes ρ'
  | _, _, _ => none

/-- Attempt to answer a query from a single ground edge. -/
def answerEdge [DecidableEq S.Kind] [DecidableEq S.Role] [DecidableEq N] [DecidableEq V]
    (q : Query S N V) (e : HEdge S N) : Option (Binding V N) :=
  if q.kind = e.kind then
    unifyEnds q.ends e.ends Binding.empty
  else
    none

/--
Answers to a query are the successful finite unifications against the store.
Each returned binding is a fill of the query's variable ends.
-/
def answers [DecidableEq S.Kind] [DecidableEq S.Role] [DecidableEq N] [DecidableEq V]
    (q : Query S N V) (db : Store S N) : List (Binding V N) :=
  db.filterMap (answerEdge q)

/-- Convert a list of all-bound query ends into ground edge ends, failing at variables. -/
def boundEnds? : List (QEnd S N V) → Option (List (S.Role × N))
  | [] => some []
  | (role, Sum.inr n) :: rest => do
      let rest' ← boundEnds? rest
      some ((role, n) :: rest')
  | (_, Sum.inl _) :: _ => none

/-- A query with no variable ends is already a ground hyperedge. -/
def toHEdge? (q : Query S N V) : Option (HEdge S N) :=
  match boundEnds? q.ends with
  | some ends => some ⟨q.kind, ends⟩
  | none => none

/-- The variable ends of a query, i.e. the typed holes in the partial hyperedge. -/
def QueryHole (q : Query S N V) : Type (max uR uN uV) :=
  { e : QEnd S N V // e ∈ q.ends ∧ ∃ v : V, e.2 = Sum.inl v }

/-- The polynomial interface whose directions are the variable ends of a query. -/
def holePoly (q : Query S N V) : PFunctor.{0, max uR uN uV} where
  A := PUnit
  B := fun _ => QueryHole q

/--
A query is a comb whose target directions are exactly the variable ends.  This
is the finite first-order version of the open hyperedge/probe semantics.
-/
def queryComb (q : Query S N V) : Comb Fill.I (holePoly q) where
  onPos := fun _ => PUnit.unit
  onDir := fun _ _ => PUnit.unit

/-- Alias emphasizing that answering a query is filling its variable holes from the store. -/
def fills [DecidableEq S.Kind] [DecidableEq S.Role] [DecidableEq N] [DecidableEq V]
    (q : Query S N V) (db : Store S N) : List (Binding V N) :=
  answers q db

/-- Answers are exactly the fills of the query holes supplied by the finite store. -/
theorem answers_eq_fills [DecidableEq S.Kind] [DecidableEq S.Role] [DecidableEq N]
    [DecidableEq V] (q : Query S N V) (db : Store S N) :
    answers q db = fills q db :=
  rfl

/--
Membership in `answers` is membership in the successful edge-by-edge fills.
This is the executable `answers ↔ fill` bridge for the finite store model.
-/
theorem mem_answers_iff [DecidableEq S.Kind] [DecidableEq S.Role] [DecidableEq N]
    [DecidableEq V] {q : Query S N V} {db : Store S N} {ρ : Binding V N} :
    ρ ∈ answers q db ↔ ρ ∈ db.filterMap (answerEdge q) :=
  Iff.rfl

namespace Example

/-- Example edge kinds. -/
inductive Kind where
  | knows
  | likes
  deriving DecidableEq, Repr

/-- Example role labels. -/
inductive Role where
  | subject
  | object
  deriving DecidableEq, Repr

/-- Example nodes. -/
inductive Node where
  | joe
  | mary
  | alice
  deriving DecidableEq, Repr

/-- Example query variables. -/
inductive Var where
  | x
  deriving DecidableEq, Repr

/-- The example signature. -/
def sig : Sig where
  Kind := Kind
  Role := Role

instance : DecidableEq sig.Kind := by
  dsimp [sig]
  infer_instance

instance : DecidableEq sig.Role := by
  dsimp [sig]
  infer_instance

/-- A two-edge store. -/
def store : Store sig Node :=
  [⟨Kind.knows, [(Role.subject, Node.joe), (Role.object, Node.mary)]⟩,
   ⟨Kind.likes, [(Role.subject, Node.joe), (Role.object, Node.alice)]⟩]

/-- Query: Joe knows whom? -/
def query : Query sig Node Var :=
  ⟨Kind.knows, [(Role.subject, Sum.inr Node.joe), (Role.object, Sum.inl Var.x)]⟩

/-- The unique binding returned by the worked example. -/
def expectedBinding : Binding Var Node
  | Var.x => some Node.mary

example : (answers query store).map (fun ρ => ρ Var.x) = [some Node.mary] :=
  rfl

example : (answers query store).length = 1 :=
  rfl

example : answers query store = [expectedBinding] :=
  rfl

example : QueryHole query :=
  ⟨(Role.object, Sum.inl Var.x), by
    constructor
    · simp [query]
    · exact ⟨Var.x, rfl⟩⟩

#check answers
#check queryComb
#check answers_eq_fills

end Example

end ScopeQuery

end DarkTower
