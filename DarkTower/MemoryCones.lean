import DarkTower.MemoryClaims

/-!
# Memory cones: binding semantic consistency to the 3/2-blend carrier

Packet 2 for pattern M3 (memory-2026): binds the claim-level predicate
`DarkTower.MemoryClaims.Theory.semanticallyConsistent` to the carrier's
cones, per minus40 `docs/SPEC-open-items.md` §6.3 "Admissible cone".

Reading of "the cone's blend axioms": the carrier's `Cone` carries the
target theory `B : Theory` as a field, and a `Theory` *is* its axiom set;
the leg maps `b₁`, `b₂` only *derive* carriage (`PMap.carries`), they do
not store the blend's claims anywhere else. So
`Cone.semanticallyConsistent` reads the axioms of `c.B` directly. Requiring
that named source claims actually be carried along each leg (§6.3
"required carriage") is NOT checked here and is left for a later packet,
as are coverage and non-degeneracy. What is stated today are the two
decidable conditions: `Cone.consistent` (route maps functional) and
semantic consistency of the blend theory.

The headline theorem is codex-68's finding made formal
(`corner_store_cone_gap`): a concrete span and cone for the corner store
— two memories, one claiming `located-at(store, 23rd)`, the other
`located-at(store, 40th)`, sharing the `store` entity — whose cone is
`Cone.consistent` but NOT semantically consistent, hence not
`memoryAdmissible`. -/

namespace DarkTower.MemoryCones

open DarkTower.WarMachine.ThreeHalvesBlend
open DarkTower.MemoryClaims (Schema Theory.semanticallyConsistent locatedAt store street23
  street40 sells coffee candy negLocatedAt S_store)

/-! ## Admissibility (partial, per §6.3) -/

/-- The cone lands in a theory that is semantically consistent under the
claim schema `S`. The blend's claims are read from `c.B.axioms` (see the
module docstring for why). -/
def coneSemanticallyConsistent (s : Span) (c : Cone s) (S : Schema) : Bool :=
  Theory.semanticallyConsistent S c.B

/-- The two §6.3 conditions decidable today: carrier consistency (route
maps functional) and semantic consistency of the blend. Required
carriage, coverage and non-degeneracy are NOT included yet. -/
def coneMemoryAdmissible (s : Span) (c : Cone s) (S : Schema) : Bool :=
  c.consistent && coneSemanticallyConsistent s c S

/-- `coneMemoryAdmissible` implies carrier consistency (trivial, stated). -/
theorem memoryAdmissible_consistent {s : Span} {c : Cone s} {S : Schema}
    (h : coneMemoryAdmissible s c S = true) : c.consistent = true := by
  rw [coneMemoryAdmissible, Bool.and_eq_true] at h
  exact h.1

/-! ## The corner store: codex-68's gap as a theorem -/

/-- The shared context of the two corner-store memories: the relation
symbol `locatedAt` and the entity `store`. -/
def spanG : Theory where
  elems := {locatedAt, store}
  axioms := ∅

/-- Memory one: `located-at(store, 23rd)`. -/
def storeM1 : Theory where
  elems := {locatedAt, store, street23}
  axioms := {(locatedAt, store, street23)}

/-- Memory two: `located-at(store, 40th)`. -/
def storeM2 : Theory where
  elems := {locatedAt, store, street40}
  axioms := {(locatedAt, store, street40)}

/-- The corner-store span: both memories seen over the shared context. -/
def cornerSpan : Span where
  G := spanG
  I₁ := storeM1
  I₂ := storeM2
  a₁ := { rel := {(locatedAt, locatedAt), (store, store)} }
  a₂ := { rel := {(locatedAt, locatedAt), (store, store)} }

/-- The blend: one theory holding both located-at claims, with each leg
the evident inclusion. -/
def cornerCone : Cone cornerSpan where
  B := { elems := {locatedAt, store, street23, street40}
         axioms := {(locatedAt, store, street23), (locatedAt, store, street40)} }
  b₁ := { rel := {(locatedAt, locatedAt), (store, store), (street23, street23)} }
  b₂ := { rel := {(locatedAt, locatedAt), (store, store), (street40, street40)} }
  aux₁ := false
  aux₂ := false

/-- Every route map is functional with endpoints in `G` and `B`: the
carrier is happy. -/
theorem corner_store_cone_consistent : cornerCone.consistent = true := by
  decide

/-- But the blend theory holds two different values of a functional
relation for the same subject: semantic consistency fails. -/
theorem corner_store_cone_not_semantically_consistent :
    coneSemanticallyConsistent cornerSpan cornerCone S_store = false := by
  decide

/-- The corner-store cone is not memory-admissible. -/
theorem corner_store_cone_not_admissible :
    coneMemoryAdmissible cornerSpan cornerCone S_store = false := by
  rw [coneMemoryAdmissible, corner_store_cone_not_semantically_consistent]
  rfl

/-- **codex-68's finding, formal**: a cone can be `Cone.consistent` —
no clashing identification, every route map functional — while the
combined memory is semantically inconsistent. Carrier consistency alone
does not detect contradiction, which is exactly why §6.3 gives memory
combination its own predicate. -/
theorem corner_store_cone_gap :
    cornerCone.consistent = true ∧ coneMemoryAdmissible cornerSpan cornerCone S_store = false :=
  ⟨corner_store_cone_consistent, corner_store_cone_not_admissible⟩


/-! ## A compatible pair -/

/-- Two memories adding different `sells` facts about the same store:
a non-functional relation, so no conflict. -/
def sellsSpan : Span where
  G := { elems := {sells, store}, axioms := ∅ }
  I₁ := { elems := {sells, store, coffee}, axioms := {(sells, store, coffee)} }
  I₂ := { elems := {sells, store, candy}, axioms := {(sells, store, candy)} }
  a₁ := { rel := {(sells, sells), (store, store)} }
  a₂ := { rel := {(sells, sells), (store, store)} }

def sellsCone : Cone sellsSpan where
  B := { elems := {sells, store, coffee, candy}
         axioms := {(sells, store, coffee), (sells, store, candy)} }
  b₁ := { rel := {(sells, sells), (store, store), (coffee, coffee)} }
  b₂ := { rel := {(sells, sells), (store, store), (candy, candy)} }
  aux₁ := false
  aux₂ := false

/-- The compatible pair: both carrier consistency and semantic
consistency hold, so the cone is `memoryAdmissible`. -/
theorem sells_cone_admissible : coneMemoryAdmissible sellsSpan sellsCone S_store = true := by
  decide

end DarkTower.MemoryCones
