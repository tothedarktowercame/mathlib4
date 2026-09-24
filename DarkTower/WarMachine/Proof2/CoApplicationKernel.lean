import DarkTower.WarMachine.CascadeTransition
import DarkTower.WarMachine.CascadeOrder

/-!
# Co-application kernel over a descent order (PROOF-2a, Clause 0)

PROOF-2a (`futon2/holes/labs/wm-contract/PROOF-2a-THEOREM-draft-2026-09-24.md`,
Clause 0) replaces the one-at-a-time list kernel by co-application of the
*enabled frontier*: at state `s` the enabled patterns (`CascadeTransition.guard`)
with no enabled pattern strictly above them in the descent order `r` all fire
independently, each succeeding with its own `θ`, and the next state adds the
produced tokens of those that succeed. On a chain the frontier is the first
enabled pattern, so the kernel is `cascadeKernel` there.

The carrier condition is a containment order with meets demanded only for
OVERLAPPING pairs (pairs sharing a descendant); `CascadeOrder.hasMeets`, which
demands a meet for every pair, is too strong. An overlapping pair without a
meet is a typed finding naming the maximal units of the common part.

Patterns are indexed by a finite type `ι`; the order `r` lives on indices, so
two indices may carry equal pattern data and still be distinct units. `Reach`,
`Below`, `IsMeet`, `hasMeets` are the top-level definitions of `CascadeOrder`;
`Below r a b` reads "a is below b" and `Reach r a b` "b is strictly above a".

Decidability of `r` and of `Reach r` is not assumed; the frontier is a
classical `Finset.filter` (`open Classical` at the definition), so the
theorems here use `Classical.choice`. Nothing here is computed by evaluation.
-/
namespace DarkTower.WarMachine.Proof2.CoApplicationKernel

open scoped BigOperators
open DarkTower.WarMachine.CascadeTransition

/-! ## The carrier: overlap, restricted meets, maximal common units -/

section Carrier

variable {α : Type*}

/-- Two units overlap when they share a descendant. -/
def Overlap (r : α → α → Prop) (a b : α) : Prop :=
  ∃ c, Below r c a ∧ Below r c b

/-- The semilattice condition restricted to overlapping pairs: every pair that
shares a descendant has a meet. Disjoint pairs need none. -/
def hasRestrictedMeets (r : α → α → Prop) : Prop :=
  ∀ a b, Overlap r a b → ∃ m, IsMeet r a b m

/-- `c` is a maximal unit of the common part of `a` and `b`: below both, and
nothing at or above `c` that is still below both is other than `c`. A
missing-meet finding names these. -/
def MaximalCommon (r : α → α → Prop) (a b c : α) : Prop :=
  Below r c a ∧ Below r c b ∧
    ∀ z, Below r c z → Below r z a → Below r z b → z = c

/-- F. The unrestricted semilattice condition implies the restricted one. -/
theorem hasMeets_imp_hasRestrictedMeets {r : α → α → Prop} (h : hasMeets r) :
    hasRestrictedMeets r :=
  fun a b _ => h a b

/-- A relation with no edges has no reach. -/
theorem not_reach_of_empty {r : α → α → Prop} (hr : ∀ x y, ¬ r x y) {x y : α} :
    ¬ Reach r x y := by
  intro h
  induction h with
  | single e => exact hr _ _ e
  | tail _ e _ => exact hr _ _ e

/-- Under a relation with no edges, the only overlaps are of a unit with
itself, so the restricted condition holds vacuously. -/
theorem hasRestrictedMeets_of_empty {r : α → α → Prop} (hr : ∀ x y, ¬ r x y) :
    hasRestrictedMeets r := by
  rintro a b ⟨c, hca, hcb⟩
  have hca' : c = a := hca.resolve_right (not_reach_of_empty hr)
  have hcb' : c = b := hcb.resolve_right (not_reach_of_empty hr)
  subst hca'
  subst hcb'
  exact ⟨c, Or.inl rfl, Or.inl rfl, fun _ hz _ => hz⟩

end Carrier

/-! ## The kernel -/

section Kernel

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The enabled frontier at `s`: indices whose guard holds and above which no
index with a holding guard sits. Classical: membership needs `Reach r`. -/
noncomputable def enabledFrontier (pat : ι → InterpretedPattern V) (r : ι → ι → Prop)
    (s : Finset V) : Finset ι :=
  Finset.univ.filter fun p => guard (pat p) s ∧ ∀ q, guard (pat q) s → ¬ Reach r p q

/-- Co-application of the enabled frontier: each subset `S` of the frontier
is the set of patterns that succeed, with probability `∏_{S} θ · ∏_{F∖S} (1−θ)`,
and it moves `s` to `s ∪ ⋃_{p∈S} produces_p`. -/
noncomputable def coApplyKernel (pat : ι → InterpretedPattern V) (r : ι → ι → Prop)
    (s s' : Finset V) : ℝ :=
  ∑ S ∈ (enabledFrontier pat r s).powerset,
    (∏ p ∈ S, (pat p).theta) * (∏ p ∈ enabledFrontier pat r s \ S, (1 - (pat p).theta)) *
      (if s' = s ∪ S.biUnion (fun p => (pat p).produces) then 1 else 0)

/-- A conflicting frontier: two distinct frontier patterns, one producing a
token the other forbids. The kernel still co-applies; the certificate carries
the flag. -/
noncomputable def frontierConflict (pat : ι → InterpretedPattern V) (r : ι → ι → Prop)
    (s : Finset V) : Prop :=
  ∃ p ∈ enabledFrontier pat r s, ∃ q ∈ enabledFrontier pat r s,
    p ≠ q ∧ ((pat p).produces ∩ (pat q).forbids).Nonempty

noncomputable instance (pat : ι → InterpretedPattern V) (r : ι → ι → Prop) (s : Finset V) :
    Decidable (frontierConflict pat r s) := by
  unfold frontierConflict
  infer_instance

/-- The chain condition relating a descent order to a precedence list: at every
state the frontier is empty exactly when nothing is first-enabled, and is the
singleton `{p}` exactly when `pat p` is first-enabled. Stated as a hypothesis;
this module does not derive it from a list-to-relation construction. -/
def chainCondition (pat : ι → InterpretedPattern V) (r : ι → ι → Prop)
    (precedence : List (InterpretedPattern V)) : Prop :=
  ∀ s, (enabledFrontier pat r s = ∅ ∧ firstEnabled precedence s = none) ∨
    (∃ p, enabledFrontier pat r s = {p} ∧ firstEnabled precedence s = some (pat p))

variable (pat : ι → InterpretedPattern V) (r : ι → ι → Prop)

/-- A. -/
theorem coApplyKernel_nonneg (s s' : Finset V) : 0 ≤ coApplyKernel pat r s s' := by
  unfold coApplyKernel
  refine Finset.sum_nonneg fun S _ => ?_
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact Finset.prod_nonneg fun p _ => (pat p).theta_nonneg
  · exact Finset.prod_nonneg fun p _ => by linarith [(pat p).theta_le_one]
  · split_ifs <;> norm_num

/-- B. Row sum: the indicator sums to one over `s'`, and the remaining sum
over subsets is `∏_{F} (θ + (1 − θ)) = 1` by `Finset.prod_add`. -/
theorem coApplyKernel_rowsum (s : Finset V) :
    ∑ s' : Finset V, coApplyKernel pat r s s' = 1 := by
  unfold coApplyKernel
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
  rw [← Finset.prod_add]
  simp

variable {pat r}

/-- C. An empty frontier gives the identity kernel, with no special case in the
definition: the only subset is `∅`, with weight one and no produced tokens. -/
theorem coApplyKernel_of_emptyFrontier {s : Finset V} (h : enabledFrontier pat r s = ∅)
    (s' : Finset V) :
    coApplyKernel pat r s s' = if s' = s then 1 else 0 := by
  simp [coApplyKernel, h]

omit [Fintype ι] in
private theorem powerset_singleton (p : ι) :
    ({p} : Finset ι).powerset = {∅, {p}} := by
  ext t
  simp [Finset.subset_singleton_iff]

/-- D. A singleton frontier `{p}` gives the pattern kernel of `p`: the two
subsets are `∅` (stay, weight `1 − θ`) and `{p}` (fire, weight `θ`). -/
theorem coApplyKernel_of_singletonFrontier {s : Finset V} {p : ι}
    (h : enabledFrontier pat r s = {p}) (s' : Finset V) :
    coApplyKernel pat r s s' = patternKernel (pat p) s s' := by
  unfold coApplyKernel patternKernel
  rw [h, powerset_singleton, Finset.sum_pair (Finset.empty_ne_singleton p)]
  simp only [Finset.prod_empty, Finset.sdiff_empty, Finset.prod_singleton, Finset.sdiff_self,
    Finset.biUnion_empty, Finset.union_empty, Finset.singleton_biUnion, one_mul, mul_one]
  split_ifs <;> ring

/-- E. Under the chain condition the co-application kernel is the list kernel. -/
theorem coApplyKernel_eq_cascadeKernel_of_chain {precedence : List (InterpretedPattern V)}
    (hchain : chainCondition pat r precedence) (s s' : Finset V) :
    coApplyKernel pat r s s' = cascadeKernel precedence s s' := by
  rcases hchain s with ⟨hF, hfirst⟩ | ⟨p, hF, hfirst⟩
  · rw [coApplyKernel_of_emptyFrontier hF, cascadeKernel_of_noEnabled precedence s s' hfirst]
  · rw [coApplyKernel_of_singletonFrontier hF, cascadeKernel, hfirst]

end Kernel

/-! ## G. Two-pattern conflict fixture (PROOF-2a instance 6 shape)

`p` produces `a` and forbids `b`; `q` produces `b` and forbids `a`. Both are
enabled at `∅` and incomparable under the empty order. Co-application reaches
`{a, b}` in one step with probability `θ_p · θ_q`; the list kernel in either
order never does, because whichever fires first disables the other. -/
namespace ConflictFixture

inductive Tok
  | a | b
  deriving DecidableEq, Fintype

inductive Idx
  | p | q
  deriving DecidableEq, Fintype

def pat (tp tq : ℝ) (hp0 : 0 ≤ tp) (hp1 : tp ≤ 1) (hq0 : 0 ≤ tq) (hq1 : tq ≤ 1) :
    Idx → InterpretedPattern Tok
  | .p => ⟨∅, {.a}, {.b}, tp, hp0, hp1⟩
  | .q => ⟨∅, {.b}, {.a}, tq, hq0, hq1⟩

/-- The empty descent order: `p` and `q` are incomparable. -/
def r : Idx → Idx → Prop := fun _ _ => False

theorem not_reach {x y : Idx} : ¬ Reach r x y :=
  not_reach_of_empty (fun _ _ h => h)

section Parametrised

variable (tp tq : ℝ) (hp0 : 0 ≤ tp) (hp1 : tp ≤ 1) (hq0 : 0 ≤ tq) (hq1 : tq ≤ 1)

/-- Both patterns are on the frontier at `∅`. -/
theorem frontier_eq :
    enabledFrontier (pat tp tq hp0 hp1 hq0 hq1) r ∅ = {Idx.p, Idx.q} := by
  ext x
  simp only [enabledFrontier, Finset.mem_filter, Finset.mem_univ, true_and, not_reach,
    not_false_eq_true, implies_true, and_true]
  cases x <;> simp [CascadeTransition.guard, pat]

/-- The frontier conflicts: `p` produces `a`, which `q` forbids. -/
theorem conflict : frontierConflict (pat tp tq hp0 hp1 hq0 hq1) r ∅ := by
  refine ⟨Idx.p, ?_, Idx.q, ?_, by decide, ⟨Tok.a, ?_⟩⟩
  · rw [frontier_eq]; decide
  · rw [frontier_eq]; decide
  · simp [pat]

/-- Co-application reaches `{a, b}` from `∅` in one step with probability
`θ_p · θ_q`: only the subset `{p, q}` of the frontier lands there. -/
theorem coApply_both :
    coApplyKernel (pat tp tq hp0 hp1 hq0 hq1) r ∅ {Tok.a, Tok.b} = tp * tq := by
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
  ring

/-- The list kernel `[p, q]` never reaches `{a, b}` in one step. -/
theorem list_pq_zero :
    cascadeKernel [pat tp tq hp0 hp1 hq0 hq1 Idx.p, pat tp tq hp0 hp1 hq0 hq1 Idx.q]
      ∅ {Tok.a, Tok.b} = 0 := by
  rw [cascadeKernel,
    show firstEnabled [pat tp tq hp0 hp1 hq0 hq1 Idx.p, pat tp tq hp0 hp1 hq0 hq1 Idx.q] ∅
        = some (pat tp tq hp0 hp1 hq0 hq1 Idx.p) by
      simp [firstEnabled, CascadeTransition.guard, pat]]
  have h1 : ({Tok.a, Tok.b} : Finset Tok) ≠ ∅ := by decide
  have h2 : ({Tok.a, Tok.b} : Finset Tok) ≠ {Tok.a} := by decide
  simp only [patternKernel, pat, Finset.empty_union]
  rw [if_neg h2, if_neg h1]
  ring

/-- The list kernel `[q, p]` never reaches `{a, b}` in one step either. -/
theorem list_qp_zero :
    cascadeKernel [pat tp tq hp0 hp1 hq0 hq1 Idx.q, pat tp tq hp0 hp1 hq0 hq1 Idx.p]
      ∅ {Tok.a, Tok.b} = 0 := by
  rw [cascadeKernel,
    show firstEnabled [pat tp tq hp0 hp1 hq0 hq1 Idx.q, pat tp tq hp0 hp1 hq0 hq1 Idx.p] ∅
        = some (pat tp tq hp0 hp1 hq0 hq1 Idx.q) by
      simp [firstEnabled, CascadeTransition.guard, pat]]
  have h1 : ({Tok.a, Tok.b} : Finset Tok) ≠ ∅ := by decide
  have h3 : ({Tok.a, Tok.b} : Finset Tok) ≠ {Tok.b} := by decide
  simp only [patternKernel, pat, Finset.empty_union]
  rw [if_neg h3, if_neg h1]
  ring

/-- H (first part). `p` and `q` do not overlap under the empty order, so no
meet is demanded of them. -/
theorem not_overlap : ¬ Overlap r Idx.p Idx.q := by
  rintro ⟨c, hcp, hcq⟩
  have h1 : c = Idx.p := hcp.resolve_right not_reach
  have h2 : c = Idx.q := hcq.resolve_right not_reach
  rw [h1] at h2
  exact Idx.noConfusion h2

/-- The restricted condition holds on this carrier while the unrestricted one
fails: `p` and `q` have nothing below both, and nothing is asked of them. -/
theorem restricted_holds_unrestricted_fails : hasRestrictedMeets r ∧ ¬ hasMeets r := by
  refine ⟨hasRestrictedMeets_of_empty (fun _ _ h => h), ?_⟩
  intro h
  obtain ⟨m, hmp, hmq, _⟩ := h Idx.p Idx.q
  have h1 : m = Idx.p := hmp.resolve_right not_reach
  have h2 : m = Idx.q := hmq.resolve_right not_reach
  rw [h1] at h2
  exact Idx.noConfusion h2

end Parametrised

theorem h80_nonneg : (0 : ℝ) ≤ 4 / 5 := by norm_num
theorem h80_le_one : (4 / 5 : ℝ) ≤ 1 := by norm_num

/-- With `θ_p = θ_q = 0.8` (PROOF-2a's θ), co-application gives `0.64`, not the
list kernel's `0`. -/
theorem coApply_ne_zero :
    coApplyKernel (pat (4 / 5) (4 / 5) h80_nonneg h80_le_one h80_nonneg h80_le_one) r ∅
      {Tok.a, Tok.b} ≠ 0 := by
  rw [coApply_both]
  norm_num

-- Negative control. Must fail: the list-kernel value `0` is not the
-- co-application value at the both-tokens state.
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example :
    coApplyKernel (pat (4 / 5) (4 / 5) h80_nonneg h80_le_one h80_nonneg h80_le_one) r ∅
      {Tok.a, Tok.b} = 0 := by
  simp only [coApply_ne_zero]

end ConflictFixture

/-! ## H. Missing-meet fixture

Two units `A`, `B` each contain two incomparable parts `p`, `q`. `A` and `B`
overlap (they share `p`) but have no meet: both `p` and `q` are below both,
and neither is below the other. The finding names `p` and `q` as the maximal
units of the common part. Three indices cannot exhibit this: with only one
element strictly below an overlapping pair, that element is their meet. -/
namespace MissingMeetFixture

inductive Idx
  | A | B | p | q
  deriving DecidableEq

/-- Containment: `p` and `q` sit inside `A` and inside `B`. -/
def r : Idx → Idx → Prop := fun x y => (x = .p ∨ x = .q) ∧ (y = .A ∨ y = .B)

theorem reach_shape {x y : Idx} (h : Reach r x y) :
    (x = .p ∨ x = .q) ∧ (y = .A ∨ y = .B) := by
  induction h with
  | single e => exact e
  | tail _ e ih =>
    rcases ih.2 with hb | hb <;> rcases e.1 with hb' | hb' <;> rw [hb] at hb' <;>
      exact Idx.noConfusion hb'

theorem acyclic : acyclicDescent r := by
  apply acyclic_of_increasing_rank r (fun x => match x with
    | .p => 0 | .q => 0 | .A => 1 | .B => 1)
  intro a b e
  rcases e with ⟨ha, hb⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem overlap_AB : Overlap r Idx.A Idx.B :=
  ⟨Idx.p, Or.inr (Reach.single ⟨Or.inl rfl, Or.inl rfl⟩),
    Or.inr (Reach.single ⟨Or.inl rfl, Or.inr rfl⟩)⟩

private theorem not_below_A_B : ¬ Below r Idx.A Idx.B := by
  rintro (h | h)
  · exact Idx.noConfusion h
  · rcases (reach_shape h).1 with h' | h' <;> exact Idx.noConfusion h'

private theorem not_below_B_A : ¬ Below r Idx.B Idx.A := by
  rintro (h | h)
  · exact Idx.noConfusion h
  · rcases (reach_shape h).1 with h' | h' <;> exact Idx.noConfusion h'

private theorem not_below_q_p : ¬ Below r Idx.q Idx.p := by
  rintro (h | h)
  · exact Idx.noConfusion h
  · rcases (reach_shape h).2 with h' | h' <;> exact Idx.noConfusion h'

private theorem not_below_p_q : ¬ Below r Idx.p Idx.q := by
  rintro (h | h)
  · exact Idx.noConfusion h
  · rcases (reach_shape h).2 with h' | h' <;> exact Idx.noConfusion h'

theorem below_p_A : Below r Idx.p Idx.A := Or.inr (Reach.single ⟨Or.inl rfl, Or.inl rfl⟩)
theorem below_p_B : Below r Idx.p Idx.B := Or.inr (Reach.single ⟨Or.inl rfl, Or.inr rfl⟩)
theorem below_q_A : Below r Idx.q Idx.A := Or.inr (Reach.single ⟨Or.inr rfl, Or.inl rfl⟩)
theorem below_q_B : Below r Idx.q Idx.B := Or.inr (Reach.single ⟨Or.inr rfl, Or.inr rfl⟩)

/-- `A` and `B` overlap but have no meet. -/
theorem no_meet_AB : ¬ ∃ m, IsMeet r Idx.A Idx.B m := by
  rintro ⟨m, hmA, hmB, hgreatest⟩
  cases m with
  | A => exact not_below_A_B hmB
  | B => exact not_below_B_A hmA
  | p => exact not_below_q_p (hgreatest Idx.q below_q_A below_q_B)
  | q => exact not_below_p_q (hgreatest Idx.p below_p_A below_p_B)

/-- The restricted condition fails on this carrier. -/
theorem not_hasRestrictedMeets : ¬ hasRestrictedMeets r :=
  fun h => no_meet_AB (h Idx.A Idx.B overlap_AB)

/-- `p` is a maximal unit of the common part of `A` and `B`. -/
theorem maximalCommon_p : MaximalCommon r Idx.A Idx.B Idx.p := by
  refine ⟨below_p_A, below_p_B, fun z hpz hzA hzB => ?_⟩
  rcases hpz with h | h
  · exact h.symm
  · rcases (reach_shape h).2 with rfl | rfl
    · exact absurd hzB not_below_A_B
    · exact absurd hzA not_below_B_A

/-- `q` is the other maximal unit of the common part of `A` and `B`. -/
theorem maximalCommon_q : MaximalCommon r Idx.A Idx.B Idx.q := by
  refine ⟨below_q_A, below_q_B, fun z hqz hzA hzB => ?_⟩
  rcases hqz with h | h
  · exact h.symm
  · rcases (reach_shape h).2 with rfl | rfl
    · exact absurd hzB not_below_A_B
    · exact absurd hzA not_below_B_A

end MissingMeetFixture

#print axioms hasMeets_imp_hasRestrictedMeets
#print axioms not_reach_of_empty
#print axioms hasRestrictedMeets_of_empty
#print axioms coApplyKernel_nonneg
#print axioms coApplyKernel_rowsum
#print axioms coApplyKernel_of_emptyFrontier
#print axioms powerset_singleton
#print axioms coApplyKernel_of_singletonFrontier
#print axioms coApplyKernel_eq_cascadeKernel_of_chain
#print axioms ConflictFixture.not_reach
#print axioms ConflictFixture.frontier_eq
#print axioms ConflictFixture.conflict
#print axioms ConflictFixture.coApply_both
#print axioms ConflictFixture.list_pq_zero
#print axioms ConflictFixture.list_qp_zero
#print axioms ConflictFixture.not_overlap
#print axioms ConflictFixture.restricted_holds_unrestricted_fails
#print axioms ConflictFixture.h80_nonneg
#print axioms ConflictFixture.h80_le_one
#print axioms ConflictFixture.coApply_ne_zero
#print axioms MissingMeetFixture.reach_shape
#print axioms MissingMeetFixture.acyclic
#print axioms MissingMeetFixture.overlap_AB
#print axioms MissingMeetFixture.not_below_A_B
#print axioms MissingMeetFixture.not_below_B_A
#print axioms MissingMeetFixture.not_below_q_p
#print axioms MissingMeetFixture.not_below_p_q
#print axioms MissingMeetFixture.below_p_A
#print axioms MissingMeetFixture.below_p_B
#print axioms MissingMeetFixture.below_q_A
#print axioms MissingMeetFixture.below_q_B
#print axioms MissingMeetFixture.no_meet_AB
#print axioms MissingMeetFixture.not_hasRestrictedMeets
#print axioms MissingMeetFixture.maximalCommon_p
#print axioms MissingMeetFixture.maximalCommon_q

end DarkTower.WarMachine.Proof2.CoApplicationKernel
