import DarkTower.WarMachine.Proof2.CoApplicationKernel

/-!
# A precedence list as the chain case of the descent order (PROOF-2a, Clause 0)

PROOF-2a (`futon2/holes/labs/wm-contract/PROOF-2a-THEOREM-draft-2026-09-24.md`,
Clause 0, carrier) says "a precedence list is the chain case of `r`".
`CoApplicationKernel` states the chain condition
(`CoApplicationKernel.chainCondition`) only as a hypothesis of
`coApplyKernel_eq_cascadeKernel_of_chain`. This module builds the order from
the list and discharges that hypothesis, so the kernel equality holds for
every precedence list with nothing assumed.

## Direction convention

`enabledFrontier pat r s` keeps an enabled index `p` when no enabled `q` has
`Reach r p q`, and `CoApplicationKernel` reads `Reach r a b` as "`b` is
strictly above `a`". In a precedence list the EARLIER pattern wins, so the
earlier index must sit strictly above the later one: `listChain n i j`
holds iff `j < i` (`j` earlier, hence above `i`). With this reading the
frontier at `s` is the least enabled index, which is what `firstEnabled`
returns. The opposite convention (`i < j`) would make the frontier the
LAST enabled index and the chain condition false.

Consequently "below" in the order means "later in the list": `Below
(listChain n) a b ↔ b ≤ a`, and the meet of two indices is the later one,
`max a b`.

Patterns are `pat : Fin n → InterpretedPattern V`; for a list `l` the
indexing is `listPat l i := l.get i` on `Fin l.length`. The frontier is a
classical `Finset.filter` (see `CoApplicationKernel`), so theorems about it
carry `Classical.choice`.
-/
namespace DarkTower.WarMachine.Proof2.ChainOrder

open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.Proof2.CoApplicationKernel

/-! ## The chain relation on `Fin n` -/

section Chain

/-- The chain relation of a precedence list of length `n`: `listChain n i j`
reads "`j` is strictly above `i`", and the earlier index is the one above, so
this is `j < i`. See the module docstring for why the direction is this way. -/
def listChain (n : ℕ) : Fin n → Fin n → Prop := fun i j => j < i

/-- `Reach` adds nothing to a chain: `j` is reachable above `i` iff `j < i`. -/
theorem reach_listChain_iff {n : ℕ} {i j : Fin n} : Reach (listChain n) i j ↔ j < i := by
  constructor
  · intro h
    induction h with
    | single e => exact e
    | tail _ e ih => exact lt_trans e ih
  · exact fun h => Reach.single h

/-- `a` is below `b` in the chain iff `a` is at or after `b` in the list. -/
theorem below_listChain_iff {n : ℕ} {a b : Fin n} : Below (listChain n) a b ↔ b ≤ a := by
  unfold Below
  rw [reach_listChain_iff, le_iff_eq_or_lt, eq_comm]

/-- 5. The chain is acyclic: rank `i ↦ n - i` strictly increases along every
edge (an edge goes from `i` up to an earlier `j < i`). -/
theorem acyclicDescent_listChain (n : ℕ) : acyclicDescent (listChain n) :=
  acyclic_of_increasing_rank _ (fun i => n - i.1) (fun a b e => by
    have e' : b.1 < a.1 := e
    have ha := a.isLt
    show n - a.1 < n - b.1
    omega)

/-- 6. A chain has all meets: the meet of `a` and `b` is the lower of the
two, which is the later index `max a b`. -/
theorem hasMeets_listChain (n : ℕ) : hasMeets (listChain n) := by
  intro a b
  refine ⟨max a b, ?_, ?_, ?_⟩
  · exact below_listChain_iff.mpr (le_max_left a b)
  · exact below_listChain_iff.mpr (le_max_right a b)
  · intro z hza hzb
    exact below_listChain_iff.mpr
      (max_le (below_listChain_iff.mp hza) (below_listChain_iff.mp hzb))

/-- 6. The restricted condition follows from the unrestricted one by
`CoApplicationKernel.hasMeets_imp_hasRestrictedMeets`. -/
theorem hasRestrictedMeets_listChain (n : ℕ) : hasRestrictedMeets (listChain n) :=
  hasMeets_imp_hasRestrictedMeets (hasMeets_listChain n)

end Chain

/-! ## The frontier of a chain is the least enabled index -/

section Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ} (pat : Fin n → InterpretedPattern V)

/-- `i` is the least index whose guard holds at `s`. -/
def IsLeastEnabled (s : Finset V) (i : Fin n) : Prop :=
  guard (pat i) s ∧ ∀ j, guard (pat j) s → i ≤ j

variable {pat}

/-- If some index is enabled at `s`, a least one exists. -/
theorem exists_isLeastEnabled {s : Finset V} (h : ∃ i, guard (pat i) s) :
    ∃ i, IsLeastEnabled pat s i := by
  obtain ⟨i0, hi0⟩ := h
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun j => guard (pat j) s) id ⟨i0, by simp [hi0]⟩
  exact ⟨i, (Finset.mem_filter.mp hi).2, fun j hj => hmin j (by simp [hj])⟩

/-- Under any order, the frontier is empty when nothing is enabled. -/
theorem enabledFrontier_eq_empty_of_none {r : Fin n → Fin n → Prop} {s : Finset V}
    (h : ∀ i, ¬ guard (pat i) s) : enabledFrontier pat r s = ∅ := by
  ext x
  simp only [enabledFrontier, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_and]
  exact fun hx _ => h x hx

/-- Under the chain, the frontier is the singleton of the least enabled index:
nothing enabled sits earlier than it, and every other enabled index has it
strictly above. -/
theorem enabledFrontier_listChain_eq_singleton {s : Finset V} {i : Fin n}
    (hi : IsLeastEnabled pat s i) : enabledFrontier pat (listChain n) s = {i} := by
  ext x
  simp only [enabledFrontier, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    reach_listChain_iff]
  constructor
  · rintro ⟨hx, hno⟩
    exact le_antisymm (not_lt.mp (hno i hi.1)) (hi.2 x hx)
  · rintro rfl
    exact ⟨hi.1, fun q hq hlt => not_lt.mpr (hi.2 q hq) hlt⟩

/-- 1. At every state the chain frontier is empty when no index is enabled and
is `{i}` for the least enabled index `i` otherwise. -/
theorem frontier_of_listChain (s : Finset V) :
    ((∀ i, ¬ guard (pat i) s) ∧ enabledFrontier pat (listChain n) s = ∅) ∨
      (∃ i, IsLeastEnabled pat s i ∧ enabledFrontier pat (listChain n) s = {i}) := by
  by_cases h : ∃ i, guard (pat i) s
  · obtain ⟨i, hi⟩ := exists_isLeastEnabled h
    exact Or.inr ⟨i, hi, enabledFrontier_listChain_eq_singleton hi⟩
  · have h' : ∀ i, ¬ guard (pat i) s := fun i hi => h ⟨i, hi⟩
    exact Or.inl ⟨h', enabledFrontier_eq_empty_of_none h'⟩

end Frontier

/-! ## `firstEnabled` on a list is the least enabled index -/

section List

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The patterns of a list, indexed by position. -/
abbrev listPat (l : List (InterpretedPattern V)) : Fin l.length → InterpretedPattern V :=
  fun i => l.get i

/-- `firstEnabled` is `List.find?` on the guard. -/
theorem firstEnabled_eq_find? (l : List (InterpretedPattern V)) (s : Finset V) :
    firstEnabled l s = l.find? fun p => decide (guard p s) := by
  induction l with
  | nil => simp [firstEnabled]
  | cons p ps ih =>
    by_cases h : guard p s
    · simp [firstEnabled, h]
    · simp [firstEnabled, h, ih]

/-- `firstEnabled` is `none` iff no pattern of the list is enabled. -/
theorem firstEnabled_eq_none_iff (l : List (InterpretedPattern V)) (s : Finset V) :
    firstEnabled l s = none ↔ ∀ p ∈ l, ¬ guard p s := by
  rw [firstEnabled_eq_find?, List.find?_eq_none]
  simp

/-- 2 (none). No index enabled gives `firstEnabled = none`. -/
theorem firstEnabled_eq_none_of_none (l : List (InterpretedPattern V)) (s : Finset V)
    (h : ∀ i, ¬ guard (listPat l i) s) : firstEnabled l s = none := by
  rw [firstEnabled_eq_none_iff]
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  exact h i

/-- 2 (some). `firstEnabled` returns the pattern at the least enabled index. -/
theorem firstEnabled_eq_get_least (l : List (InterpretedPattern V)) (s : Finset V)
    {i : Fin l.length} (hi : IsLeastEnabled (listPat l) s i) :
    firstEnabled l s = some (l.get i) := by
  rw [firstEnabled_eq_find?, List.find?_eq_some_iff_getElem]
  refine ⟨by simpa [listPat] using hi.1, i.1, i.2, by simp, fun j hj => ?_⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  intro hg
  have hle := hi.2 ⟨j, lt_trans hj i.2⟩ (by simpa [listPat] using hg)
  exact absurd hj (not_lt.mpr hle)

/-- 3. The chain condition holds for every precedence list: `firstEnabled`
and the chain frontier both pick the least enabled index, or both pick
nothing. This is the hypothesis `CoApplicationKernel` left open. -/
theorem chainCondition_of_list (l : List (InterpretedPattern V)) :
    chainCondition (listPat l) (listChain l.length) l := by
  intro s
  rcases frontier_of_listChain (pat := listPat l) s with ⟨hnone, hF⟩ | ⟨i, hi, hF⟩
  · exact Or.inl ⟨hF, firstEnabled_eq_none_of_none l s hnone⟩
  · exact Or.inr ⟨i, hF, firstEnabled_eq_get_least l s hi⟩

/-- 4. On the chain of a precedence list the co-application kernel is the list
kernel, with no hypothesis. -/
theorem coApplyKernel_eq_cascadeKernel_of_list (l : List (InterpretedPattern V))
    (s s' : Finset V) :
    coApplyKernel (listPat l) (listChain l.length) s s' = cascadeKernel l s s' :=
  coApplyKernel_eq_cascadeKernel_of_chain (chainCondition_of_list l) s s'

end List

/-! ## Two-element fixture and negative control

Two patterns, both enabled at `∅`: `p0` produces `a`, `p1` produces `b`,
neither consumes or forbids anything. In the list `[p0, p1]` the first sits
above the second, so the chain frontier at `∅` is `{0}`, never `{1}`. -/
namespace TwoListFixture

inductive Tok
  | a | b
  deriving DecidableEq, Fintype

def p0 : InterpretedPattern Tok := ⟨∅, {.a}, ∅, 1, zero_le_one, le_rfl⟩
def p1 : InterpretedPattern Tok := ⟨∅, {.b}, ∅, 1, zero_le_one, le_rfl⟩

/-- The precedence list `[p0, p1]`. -/
def precedence : List (InterpretedPattern Tok) := [p0, p1]

/-- The list's patterns on `Fin 2` (the length is definitionally `2`). -/
def pat : Fin 2 → InterpretedPattern Tok := listPat precedence

theorem guard_p0 : guard p0 ∅ := by
  simp [CascadeTransition.guard, p0]

theorem guard_p1 : guard p1 ∅ := by
  simp [CascadeTransition.guard, p1]

/-- Both patterns are enabled at `∅`. -/
theorem both_enabled : guard (pat 0) ∅ ∧ guard (pat 1) ∅ :=
  ⟨guard_p0, guard_p1⟩

/-- `0` is the least enabled index. -/
theorem isLeastEnabled_zero : IsLeastEnabled pat ∅ 0 :=
  ⟨guard_p0, fun j _ => Fin.zero_le j⟩

/-- The frontier at `∅` is the first element alone, although both are enabled. -/
theorem frontier_eq : enabledFrontier pat (listChain 2) ∅ = {0} :=
  enabledFrontier_listChain_eq_singleton isLeastEnabled_zero

/-- The frontier is not the second element. -/
theorem frontier_ne_one : enabledFrontier pat (listChain 2) ∅ ≠ {1} := by
  rw [frontier_eq]
  decide

/-- `firstEnabled` agrees: it returns `p0`. -/
theorem firstEnabled_eq : firstEnabled precedence ∅ = some p0 :=
  firstEnabled_eq_get_least precedence ∅ isLeastEnabled_zero

/-- The kernel equality on the fixture, from the list theorem. -/
theorem coApply_eq_cascade (s s' : Finset Tok) :
    coApplyKernel pat (listChain 2) s s' = cascadeKernel precedence s s' :=
  coApplyKernel_eq_cascadeKernel_of_list precedence s s'

-- Negative control. Must fail: the second element is not the frontier at `∅`
-- even though its guard holds, because the first element sits above it.
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : enabledFrontier pat (listChain 2) ∅ = {1} := by
  simp only [frontier_ne_one]

end TwoListFixture

#print axioms reach_listChain_iff
#print axioms below_listChain_iff
#print axioms acyclicDescent_listChain
#print axioms hasMeets_listChain
#print axioms hasRestrictedMeets_listChain
#print axioms exists_isLeastEnabled
#print axioms enabledFrontier_eq_empty_of_none
#print axioms enabledFrontier_listChain_eq_singleton
#print axioms frontier_of_listChain
#print axioms firstEnabled_eq_find?
#print axioms firstEnabled_eq_none_iff
#print axioms firstEnabled_eq_none_of_none
#print axioms firstEnabled_eq_get_least
#print axioms chainCondition_of_list
#print axioms coApplyKernel_eq_cascadeKernel_of_list
#print axioms TwoListFixture.guard_p0
#print axioms TwoListFixture.guard_p1
#print axioms TwoListFixture.both_enabled
#print axioms TwoListFixture.isLeastEnabled_zero
#print axioms TwoListFixture.frontier_eq
#print axioms TwoListFixture.frontier_ne_one
#print axioms TwoListFixture.firstEnabled_eq
#print axioms TwoListFixture.coApply_eq_cascade

end DarkTower.WarMachine.Proof2.ChainOrder
