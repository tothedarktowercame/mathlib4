import DarkTower.WarMachine.Proof2.ChainOrder

/-!
# Co-application over a containment order: the chain case in general, and the
# shared part that conflicts (PROOF-2a, Clause 0)

Clause 0 (`futon2/holes/labs/wm-contract/PROOF-2a-THEOREM-draft-2026-09-24.md`,
lines 128-212) asks for the co-application kernel `K`, its nonnegativity and
row sum, `K = cascadeKernel` on chains, the frontier-conflict predicate, and
the restricted meet condition. Those are built in
`DarkTower.WarMachine.Proof2.CoApplicationKernel` (kernel, `frontierConflict`,
`hasRestrictedMeets`, `hasMeets_imp_hasRestrictedMeets`, and the two-element
antichain showing the converse fails) and
`DarkTower.WarMachine.Proof2.ChainOrder` (the order built from a precedence
list, with `chainCondition` discharged). This module adds the two things the
clause states that those modules do not.

**1. The chain case for an arbitrary total order, not just a list.** Clause 0
reads "on a chain (`r` a total order, so `F(s)` is `firstEnabled`)".
`ChainOrder` proves the frontier is a singleton for `listChain n` on `Fin n`,
using `Fin n`'s own `<`; nothing said what happens under an arbitrary `r`. Here
the frontier is shown empty-or-singleton for ANY `r` on a finite index type that
is acyclic and total, with the singleton derived rather than assumed:
finiteness, transitivity of `Reach` and irreflexivity from
`acyclicDescent` give a maximal enabled unit, and totality makes it unique.
`CoApplicationKernel.chainCondition` then follows for any precedence list whose
`firstEnabled` matches that unit, so its `coApplyKernel_eq_cascadeKernel_of_chain`
applies with the frontier structure proven. What remains as data, and is not a
gap in the proof, is WHICH list realises a given abstract chain; for the
list-induced chain that is `ChainOrder.chainCondition_of_list`.

**2. The missing meet and the frontier conflict as one fact.** Clause 0's
reading (3) of instance 6: "the one overlapping pair without a meet has exactly
those two patterns as the maximal units of its common part: the missing meet
and the conflict are the same fact". The committed fixtures do not state this
and cannot: `ConflictFixture` proves `¬ Overlap` on its carrier, and
`MissingMeetFixture` carries an order with no patterns, no guards and no
frontier. `SharedPartConflict` below puts patterns on `MissingMeetFixture`'s own
carrier, where `A` and `B` overlap without a meet and their maximal common units
are `p` and `q`, and shows that the same `p`, `q` are the enabled frontier at
the initial state and that they conflict there.

The frontier is a classical `Finset.filter` (see `CoApplicationKernel`), so
these theorems carry `Classical.choice`. Nothing here is computed by evaluation.
-/
namespace DarkTower.WarMachine.CascadeCoapplication

open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.Proof2.CoApplicationKernel

/-! ## `Reach` is a strict order under `acyclicDescent` -/

section Order

variable {α : Type*} {r : α → α → Prop}

/-- `Reach` is transitive: paths compose. `CascadeOrder` proves it only through
a rank function (`reach_increases_rank`); the relation itself is transitive with
no rank in sight. -/
theorem reach_trans {a b c : α} (hab : Reach r a b) (hbc : Reach r b c) : Reach r a c := by
  induction hbc with
  | single e => exact Reach.tail hab e
  | tail _ e ih => exact Reach.tail ih e

/-- Acyclicity is exactly irreflexivity of `Reach`. -/
theorem not_reach_self (h : acyclicDescent r) (a : α) : ¬ Reach r a a := h a

/-- A chain: any two distinct units are comparable. A precedence list is the
case where this holds by position (`ChainOrder.listChain`). -/
def IsChainOrder (r : α → α → Prop) : Prop :=
  ∀ a b, a ≠ b → Reach r a b ∨ Reach r b a

end Order

/-! ## The enabled frontier over an arbitrary containment order -/

section Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {pat : ι → InterpretedPattern V} {r : ι → ι → Prop} {s : Finset V}

omit [DecidableEq ι] in
/-- Membership in the frontier, unfolded once so the rest reads in the clause's
own words: enabled, with nothing enabled above. -/
theorem mem_enabledFrontier_iff {i : ι} :
    i ∈ enabledFrontier pat r s ↔ guard (pat i) s ∧ ∀ j, guard (pat j) s → ¬ Reach r i j := by
  classical
  simp [enabledFrontier]

omit [DecidableEq ι] in
theorem guard_of_mem_enabledFrontier {i : ι} (h : i ∈ enabledFrontier pat r s) :
    guard (pat i) s :=
  (mem_enabledFrontier_iff.mp h).1

omit [DecidableEq ι] in
/-- A unit with an enabled unit above it is not on the frontier: the outermost
enabled container fires, not its parts. -/
theorem not_mem_enabledFrontier_of_enabled_above {i j : ι} (hj : guard (pat j) s)
    (hij : Reach r i j) : i ∉ enabledFrontier pat r s :=
  fun hi => (mem_enabledFrontier_iff.mp hi).2 j hj hij

omit [DecidableEq ι] in
/-- The frontier is an antichain: no frontier unit contains another. This is
what makes co-application well posed — the units fire independently because
none of them sits above another. -/
theorem not_reach_of_mem_enabledFrontier {i j : ι} (hi : i ∈ enabledFrontier pat r s)
    (hj : j ∈ enabledFrontier pat r s) : ¬ Reach r i j :=
  (mem_enabledFrontier_iff.mp hi).2 j (guard_of_mem_enabledFrontier hj)

omit [DecidableEq ι] in
/-- Nothing enabled, nothing on the frontier (any order, any index type). -/
theorem enabledFrontier_eq_empty_of_no_guard (h : ∀ i, ¬ guard (pat i) s) :
    enabledFrontier pat r s = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  exact fun x hx => h x (guard_of_mem_enabledFrontier hx)

omit [DecidableEq ι] in
/-- Something enabled, something on the frontier. The maximal enabled unit
exists because the index type is finite and `Reach r` is a strict order:
`acyclicDescent` gives irreflexivity, `reach_trans` transitivity, and a finite
strict order is well founded. -/
theorem enabledFrontier_nonempty_of_exists_guard (hacyc : acyclicDescent r)
    (h : ∃ i, guard (pat i) s) : (enabledFrontier pat r s).Nonempty := by
  haveI : IsTrans ι (fun x y : ι => Reach r y x) :=
    ⟨fun _ _ _ hab hbc => reach_trans hbc hab⟩
  haveI : Std.Irrefl (fun x y : ι => Reach r y x) := ⟨fun a ha => hacyc a ha⟩
  obtain ⟨i0, hi0⟩ := h
  obtain ⟨i, hi, hmin⟩ :=
    (Finite.wellFounded_of_trans_of_irrefl (fun x y : ι => Reach r y x)).has_min
      {j | guard (pat j) s} ⟨i0, hi0⟩
  exact ⟨i, mem_enabledFrontier_iff.mpr ⟨hi, fun j hj hreach => hmin j hj hreach⟩⟩

/-- On a chain the frontier holds at most one unit: two distinct frontier units
would be comparable, and the frontier is an antichain. -/
theorem eq_of_mem_enabledFrontier_of_chain (hchain : IsChainOrder r) {i j : ι}
    (hi : i ∈ enabledFrontier pat r s) (hj : j ∈ enabledFrontier pat r s) : i = j := by
  by_contra hne
  rcases hchain i j hne with hij | hji
  · exact not_reach_of_mem_enabledFrontier hi hj hij
  · exact not_reach_of_mem_enabledFrontier hj hi hji

/-- **The chain case, for an arbitrary total order.** At every state the
frontier is empty or a singleton. Neither disjunct is assumed: the singleton is
the maximal enabled unit, unique by totality. -/
theorem enabledFrontier_of_chainOrder (hacyc : acyclicDescent r) (hchain : IsChainOrder r)
    (s : Finset V) :
    enabledFrontier pat r s = ∅ ∨ ∃ i, enabledFrontier pat r s = {i} := by
  by_cases h : ∃ i, guard (pat i) s
  · obtain ⟨i, hi⟩ := enabledFrontier_nonempty_of_exists_guard hacyc h
    exact Or.inr ⟨i, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hi, fun x hx => eq_of_mem_enabledFrontier_of_chain hchain hx hi⟩⟩
  · exact Or.inl (enabledFrontier_eq_empty_of_no_guard (fun i hi => h ⟨i, hi⟩))

/-- On a chain the kernel is one pattern's kernel, or the identity: the sum over
subsets of the frontier has at most two terms. -/
theorem coApplyKernel_of_chainOrder (hacyc : acyclicDescent r) (hchain : IsChainOrder r)
    (s s' : Finset V) :
    coApplyKernel pat r s s' = (if s' = s then 1 else 0) ∨
      ∃ i, i ∈ enabledFrontier pat r s ∧
        coApplyKernel pat r s s' = patternKernel (pat i) s s' := by
  rcases enabledFrontier_of_chainOrder (pat := pat) hacyc hchain s with h | ⟨i, h⟩
  · exact Or.inl (coApplyKernel_of_emptyFrontier h s')
  · exact Or.inr ⟨i, by rw [h]; exact Finset.mem_singleton_self i,
      coApplyKernel_of_singletonFrontier h s'⟩

/-- The chain condition of `CoApplicationKernel` holds for any total order whose
frontier `firstEnabled` tracks. The empty-or-singleton shape is no longer part
of the hypothesis — only the correspondence between the order and the list,
which is the data saying which list realises the chain. -/
theorem chainCondition_of_chainOrder (hacyc : acyclicDescent r) (hchain : IsChainOrder r)
    {precedence : List (InterpretedPattern V)}
    (hnone : ∀ s, enabledFrontier pat r s = ∅ → firstEnabled precedence s = none)
    (hsome : ∀ s i, enabledFrontier pat r s = {i} → firstEnabled precedence s = some (pat i)) :
    chainCondition pat r precedence := by
  intro s
  rcases enabledFrontier_of_chainOrder (pat := pat) hacyc hchain s with h | ⟨i, h⟩
  · exact Or.inl ⟨h, hnone s h⟩
  · exact Or.inr ⟨i, h, hsome s i h⟩

/-- `K = cascadeKernel` on a chain, with the frontier structure proven. -/
theorem coApplyKernel_eq_cascadeKernel_of_chainOrder (hacyc : acyclicDescent r)
    (hchain : IsChainOrder r) {precedence : List (InterpretedPattern V)}
    (hnone : ∀ s, enabledFrontier pat r s = ∅ → firstEnabled precedence s = none)
    (hsome : ∀ s i, enabledFrontier pat r s = {i} → firstEnabled precedence s = some (pat i))
    (s s' : Finset V) :
    coApplyKernel pat r s s' = cascadeKernel precedence s s' :=
  coApplyKernel_eq_cascadeKernel_of_chain
    (chainCondition_of_chainOrder hacyc hchain hnone hsome) s s'

end Frontier

/-! ## The missing meet and the frontier conflict are one fact (instance 6)

Clause 0's reading (3): "the one overlapping pair without a meet has exactly
those two patterns as the maximal units of its common part: the missing meet
and the conflict are the same fact". The carrier is `MissingMeetFixture`'s own
order — `p` and `q` sit inside both `A` and `B`, which overlap and have no meet,
with `p` and `q` the maximal units of their common part, all already proven
there. What is added here is the interpretation: patterns on that carrier under
which `p` and `q` are the enabled frontier at the initial state and conflict on
it, so one carrier carries both halves of the claim.

The containers ask for a token the initial state lacks, so they are disabled and
the shared parts are on the frontier; `p` produces the token `q` forbids. -/

namespace SharedPartConflict

open DarkTower.WarMachine.Proof2.CoApplicationKernel.MissingMeetFixture

instance : Fintype Idx where
  elems := {Idx.A, Idx.B, Idx.p, Idx.q}
  complete := by intro x; cases x <;> decide

inductive Tok
  | a | b | z
  deriving DecidableEq, Fintype

/-- `A` and `B` need `z`; `p` and `q` are the shared parts, and each produces
what the other forbids. -/
noncomputable def pat : Idx → InterpretedPattern Tok
  | .A => ⟨{Tok.z}, {Tok.a}, ∅, 1, zero_le_one, le_rfl⟩
  | .B => ⟨{Tok.z}, {Tok.b}, ∅, 1, zero_le_one, le_rfl⟩
  | .p => ⟨∅, {Tok.a}, {Tok.b}, 4 / 5, by norm_num, by norm_num⟩
  | .q => ⟨∅, {Tok.b}, {Tok.a}, 4 / 5, by norm_num, by norm_num⟩

/-- At the initial state exactly the two shared parts are enabled: the
containers are waiting on `z`. -/
theorem enabled_iff {j : Idx} : guard (pat j) (∅ : Finset Tok) ↔ (j = Idx.p ∨ j = Idx.q) := by
  cases j <;> simp [CascadeTransition.guard, pat]

private theorem not_reach_to_p {x : Idx} : ¬ Reach r x Idx.p := by
  intro h
  rcases (reach_shape h).2 with h' | h' <;> exact Idx.noConfusion h'

private theorem not_reach_to_q {x : Idx} : ¬ Reach r x Idx.q := by
  intro h
  rcases (reach_shape h).2 with h' | h' <;> exact Idx.noConfusion h'

/-- The frontier is the pair of shared parts. The containers are absent because
they are disabled, not because anything sits above them. -/
theorem frontier_eq : enabledFrontier pat r ∅ = {Idx.p, Idx.q} := by
  ext x
  rw [mem_enabledFrontier_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, -⟩
    exact enabled_iff.mp hx
  · intro hx
    refine ⟨enabled_iff.mpr hx, fun j hj hreach => ?_⟩
    rcases enabled_iff.mp hj with rfl | rfl
    · exact not_reach_to_p hreach
    · exact not_reach_to_q hreach

/-- A part is on the frontier only while its containers are disabled: once `z`
is present, `A` is enabled and `p` drops off. -/
theorem part_off_frontier_when_container_enabled :
    Idx.p ∉ enabledFrontier pat r {Tok.z} := by
  refine not_mem_enabledFrontier_of_enabled_above (j := Idx.A) ?_ ?_
  · simp [CascadeTransition.guard, pat]
  · exact Reach.single ⟨Or.inl rfl, Or.inl rfl⟩

/-- The frontier conflicts: `p` produces `a`, which `q` forbids. -/
theorem conflict : frontierConflict pat r ∅ := by
  refine ⟨Idx.p, ?_, Idx.q, ?_, by decide, ⟨Tok.a, ?_⟩⟩
  · rw [frontier_eq]; decide
  · rw [frontier_eq]; decide
  · simp [pat]

/-- The kernel still co-applies across the conflict: `{a, b}` is reached from
the initial state in one step with probability `θ_p · θ_q`. -/
theorem coApply_reaches_both :
    coApplyKernel pat r ∅ {Tok.a, Tok.b} = 16 / 25 := by
  rw [coApplyKernel, frontier_eq]
  have hpow : ({Idx.p, Idx.q} : Finset Idx).powerset = {∅, {Idx.p}, {Idx.q}, {Idx.p, Idx.q}} := by
    decide
  have h1 : ({Tok.a, Tok.b} : Finset Tok) ≠ ∅ := by decide
  have h2 : ({Tok.a, Tok.b} : Finset Tok) ≠ {Tok.a} := by decide
  have h3 : ({Tok.a, Tok.b} : Finset Tok) ≠ {Tok.b} := by decide
  have h4 : ({Tok.a, Tok.b} : Finset Tok) = {Tok.a} ∪ {Tok.b} := by decide
  have d1 : ({Idx.p, Idx.q} : Finset Idx) \ {Idx.p} = {Idx.q} := by decide
  have d2 : ({Idx.p, Idx.q} : Finset Idx) \ {Idx.q} = {Idx.p} := by decide
  have hpq : Idx.p ∉ ({Idx.q} : Finset Idx) := by decide
  rw [hpow, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Finset.prod_empty, Finset.sdiff_empty, Finset.prod_singleton, Finset.sdiff_self,
    Finset.biUnion_empty, Finset.union_empty, Finset.singleton_biUnion, Finset.empty_union,
    Finset.biUnion_insert, Finset.prod_insert hpq, d1, d2, pat, one_mul, mul_one]
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  norm_num

/-- **Clause 0, reading (3).** On one carrier: `A` and `B` overlap, have no
meet, and the maximal units of their common part are `p` and `q`; and those
same `p`, `q` are the enabled frontier at the initial state and conflict there.
The missing meet and the conflict are the same pair. -/
theorem missing_meet_and_frontier_conflict_are_one_fact :
    Overlap r Idx.A Idx.B ∧
      (¬ ∃ m, IsMeet r Idx.A Idx.B m) ∧
      MaximalCommon r Idx.A Idx.B Idx.p ∧
      MaximalCommon r Idx.A Idx.B Idx.q ∧
      enabledFrontier pat r ∅ = {Idx.p, Idx.q} ∧
      frontierConflict pat r ∅ :=
  ⟨overlap_AB, no_meet_AB, maximalCommon_p, maximalCommon_q, frontier_eq, conflict⟩

/-- The carrier is acyclic, so it is a lawful containment order: the finding is
a missing meet, not a broken order. -/
theorem carrier_is_acyclic : acyclicDescent r := acyclic

end SharedPartConflict

#print axioms reach_trans
#print axioms not_reach_self
#print axioms mem_enabledFrontier_iff
#print axioms not_mem_enabledFrontier_of_enabled_above
#print axioms not_reach_of_mem_enabledFrontier
#print axioms enabledFrontier_eq_empty_of_no_guard
#print axioms enabledFrontier_nonempty_of_exists_guard
#print axioms eq_of_mem_enabledFrontier_of_chain
#print axioms enabledFrontier_of_chainOrder
#print axioms coApplyKernel_of_chainOrder
#print axioms chainCondition_of_chainOrder
#print axioms coApplyKernel_eq_cascadeKernel_of_chainOrder
#print axioms SharedPartConflict.enabled_iff
#print axioms SharedPartConflict.frontier_eq
#print axioms SharedPartConflict.part_off_frontier_when_container_enabled
#print axioms SharedPartConflict.conflict
#print axioms SharedPartConflict.coApply_reaches_both
#print axioms SharedPartConflict.missing_meet_and_frontier_conflict_are_one_fact
#print axioms SharedPartConflict.carrier_is_acyclic

end DarkTower.WarMachine.CascadeCoapplication
