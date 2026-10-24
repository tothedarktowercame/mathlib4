import DarkTower.WarMachine.R20CheckedMapCarry

/-!
# Executable finite checked-map closure

This module refines `CheckedProblemMap.Closed` on a fixed finite statement
universe. It never evaluates the interpretation `I`; artifacts and reductions
already contain the proofs. The production-shaped executable construction
repeats one monotone saturation step from the empty set for `card S` rounds.
That bound suffices because every non-stable round adds an element. A second,
exhaustive construction enumerates at most `2 ^ card S` candidate subsets and
serves as a small reference oracle. Both compute the existing least closure
without any decidability assumption on `I`.

AND is tail membership within one reduction; OR is the presence of any
enabled reduction with the same head. Empty-tail reductions fire, unseeded
cycles do not, and seeded cycles may propagate. No fixture IDs are special.
This is an algorithmic refinement of the existing checked-map semantics, not
new AIF, runtime-authenticity, scoring, or learning semantics.
-/

namespace DarkTower.WarMachine.ExecutableCheckedClosure

open CheckedProblemMap CheckedReturnObservation

section Proofs

universe u
variable {S : Type u} [Fintype S] [DecidableEq S] {I : S → Prop}

/-- One structural saturation step, useful for executable inspection. -/
def step (m : ProblemMap I) (T : Finset S) : Finset S :=
  T ∪ Finset.univ.filter fun s =>
    (∃ a ∈ m.artifacts, a.stmt = s) ∨
      ∃ r ∈ m.reductions, r.head = s ∧ ∀ t ∈ r.tails, t ∈ T

theorem subset_step (m : ProblemMap I) (T : Finset S) : T ⊆ step m T :=
  Finset.subset_union_left

theorem step_mono (m : ProblemMap I) : Monotone (step m) := by
  intro A B hAB s hs
  simp only [step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and] at hs ⊢
  rcases hs with hs | hs
  · exact Or.inl (hAB hs)
  · right
    rcases hs with hs | ⟨r, hr, rfl, ht⟩
    · exact Or.inl hs
    · exact Or.inr ⟨r, hr, rfl, fun t htt => hAB (ht t htt)⟩

/-- The production-shaped bounded saturation algorithm. -/
def iterativeClosedSet (m : ProblemMap I) : Finset S :=
  (step m)^[Fintype.card S] ∅

/-- Decidable structural form of the existing `RuleClosed`. -/
def StructurallyClosed (m : ProblemMap I) (T : Finset S) : Prop :=
  m.artifacts.Forall (fun a => a.stmt ∈ T) ∧
    m.reductions.Forall (fun r => (∀ t ∈ r.tails, t ∈ T) → r.head ∈ T)

instance (m : ProblemMap I) (T : Finset S) : Decidable (StructurallyClosed m T) :=
  by unfold StructurallyClosed; infer_instance

theorem ruleClosedB_iff (m : ProblemMap I) (T : Finset S) :
    StructurallyClosed m T ↔ RuleClosed m (↑T : Set S) := by
  simp [StructurallyClosed, RuleClosed, List.forall_iff_forall_mem]

/-- All finite structurally rule-closed candidates. There are at most
`2 ^ Fintype.card S` of them because that is the cardinality of `Finset S`. -/
def candidates (m : ProblemMap I) : Finset (Finset S) :=
  Finset.univ.filter fun T => StructurallyClosed m T

/-- Executable least closure: membership in every structurally rule-closed
finite candidate. -/
def executableClosedSet (m : ProblemMap I) : Finset S :=
  Finset.univ.filter fun s => ∀ T ∈ candidates m, s ∈ T

theorem mem_executableClosedSet (m : ProblemMap I) (s : S) :
    s ∈ executableClosedSet m ↔
      ∀ T : Finset S, RuleClosed m (↑T : Set S) → s ∈ T := by
  simp [executableClosedSet, candidates, ruleClosedB_iff]

theorem executable_ruleClosed (m : ProblemMap I) :
    RuleClosed m (↑(executableClosedSet m) : Set S) := by
  constructor
  · intro a ha
    change a.stmt ∈ executableClosedSet m
    rw [mem_executableClosedSet]
    intro T hT
    exact hT.1 a ha
  · intro r hr ht
    change r.head ∈ executableClosedSet m
    rw [mem_executableClosedSet]
    intro T hT
    exact hT.2 r hr fun t ht' =>
      (mem_executableClosedSet m t).1 (ht t ht') T hT

/-- Exact refinement of the existing inductive semantic predicate. -/
theorem mem_executable_iff_closed (m : ProblemMap I) (s : S) :
    s ∈ executableClosedSet m ↔ Closed m s := by
  constructor
  · intro hs
    exact mem_closedSet.1 ((mem_executableClosedSet m s).1 hs
      (closedSet m)
      (by
        constructor
        · intro a ha
          exact mem_closedSet.2 (Closed.artifact a ha)
        · intro r hr ht
          exact mem_closedSet.2 (Closed.reduction r hr fun t htail =>
            mem_closedSet.1 (ht t htail))))
  · intro hs
    exact closed_least (executable_ruleClosed m) hs

theorem executable_eq_closedSet (m : ProblemMap I) :
    executableClosedSet m = closedSet m := by
  ext s
  rw [mem_executable_iff_closed, mem_closedSet]

/-- The executable result is a fixed point of the structural saturation step. -/
theorem step_executableClosedSet (m : ProblemMap I) :
    step m (executableClosedSet m) = executableClosedSet m := by
  apply Finset.Subset.antisymm
  · intro s hs
    simp only [step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and] at hs
    rcases hs with hs | hs
    · exact hs
    · rw [mem_executable_iff_closed]
      rcases hs with ⟨a, ha, rfl⟩ | ⟨r, hr, rfl, ht⟩
      · exact Closed.artifact a ha
      · exact Closed.reduction r hr fun t htt =>
          (mem_executable_iff_closed m t).1 (ht t htt)
  · exact Finset.subset_union_left

theorem iterate_subset_executable (m : ProblemMap I) (n : ℕ) :
    (step m)^[n] ∅ ⊆ executableClosedSet m := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (step_mono m ih).trans_eq (step_executableClosedSet m)

theorem iterate_eq_executable_of_fixed (m : ProblemMap I) (n : ℕ)
    (hfix : step m ((step m)^[n] ∅) = (step m)^[n] ∅) :
    (step m)^[n] ∅ = executableClosedSet m := by
  apply Finset.Subset.antisymm (iterate_subset_executable m n)
  intro s hs
  rw [mem_executable_iff_closed] at hs
  apply closed_least (m := m) (T := ↑((step m)^[n] ∅))
  · constructor
    · intro a ha
      have hx : a.stmt ∈ step m ((step m)^[n] ∅) := by
        simp only [step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
      rwa [hfix] at hx
    · intro r hr ht
      have hx : r.head ∈ step m ((step m)^[n] ∅) := by
        simp only [step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact Or.inr (Or.inr ⟨r, hr, rfl, ht⟩)
      rwa [hfix] at hx
  · exact hs
theorem card_iterate_ge (m : ProblemMap I) (n : ℕ)
    (hne : (step m)^[n] ∅ ≠ executableClosedSet m) :
    n ≤ ((step m)^[n] ∅).card := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hprev : (step m)^[n] ∅ ≠ executableClosedSet m := by
        intro heq
        apply hne
        rw [Function.iterate_succ_apply', heq, step_executableClosedSet]
      have hproper : (step m)^[n] ∅ ⊂ step m ((step m)^[n] ∅) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_step _ _, ?_⟩
        intro heq
        exact hprev (iterate_eq_executable_of_fixed m n heq.symm)
      exact (Nat.succ_le_succ (ih hprev)).trans (Finset.card_lt_card hproper)

/-- `card S` rounds suffice: any earlier non-stable round strictly increases
cardinality, and a finite subset of `S` cannot contain more than `card S`
elements. -/
theorem iterative_eq_executable (m : ProblemMap I) :
    iterativeClosedSet m = executableClosedSet m := by
  by_contra hne
  have hlo := card_iterate_ge m (Fintype.card S) hne
  have hproper : iterativeClosedSet m ⊂ executableClosedSet m :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨iterate_subset_executable m _, hne⟩
  have hhi : (iterativeClosedSet m).card < Fintype.card S := by
    exact (Finset.card_lt_card hproper).trans_le (Finset.card_le_univ _)
  exact (Nat.not_lt_of_ge hlo) hhi

theorem mem_iterative_iff_closed (m : ProblemMap I) (s : S) :
    s ∈ iterativeClosedSet m ↔ Closed m s := by
  rw [iterative_eq_executable, mem_executable_iff_closed]

theorem step_iterativeClosedSet (m : ProblemMap I) :
    step m (iterativeClosedSet m) = iterativeClosedSet m := by
  rw [iterative_eq_executable, step_executableClosedSet]

theorem closureObs_executable (scored : Finset S) (m : ProblemMap I) :
    scored ∩ executableClosedSet m = closureObs scored m := by
  rw [executable_eq_closedSet]
  rfl

theorem closureObs_iterative (scored : Finset S) (m : ProblemMap I) :
    scored ∩ iterativeClosedSet m = closureObs scored m := by
  rw [iterative_eq_executable]
  exact closureObs_executable scored m

theorem returnObs_executable {Label A : Type} (m : ProblemMap I)
    (scored : Finset S) (realize : A → Option (ReturnReport I Label)) (a : A) :
    scored ∩ executableClosedSet (update m (realize a)) =
      returnObs m scored realize a := by
  rw [executable_eq_closedSet]
  rfl

theorem returnObs_iterative {Label A : Type} (m : ProblemMap I)
    (scored : Finset S) (realize : A → Option (ReturnReport I Label)) (a : A) :
    scored ∩ iterativeClosedSet (update m (realize a)) =
      returnObs m scored realize a := by
  rw [iterative_eq_executable]
  exact returnObs_executable m scored realize a

end Proofs

/-! ## Executable fixture checks -/

open CheckedProblemMap

def emptyTailHard : Reduction interp where
  head := .hard
  tails := ∅
  proof _ := by
    show ∀ n : ℕ, n + 0 = 0 + n
    intro n
    simp

def cycASeed : Artifact interp where
  stmt := .cycA
  proof := trivial

def emptyRuleMap : ProblemMap interp :=
  { m0 with reductions := emptyTailHard :: m0.reductions }

def seededCycleMap : ProblemMap interp :=
  { m0 with artifacts := [cycASeed] }

def emptyMap : ProblemMap interp :=
  { artifacts := [], reductions := [], obligations := ∅ }

def repeatedReductionMap : ProblemMap interp :=
  { m0 with reductions := viaFoundation :: m0.reductions }

/-- First derive `hard` from the seed; `viaHard` then derives `consumer` in a
later round. -/
def chainHard : Reduction interp where
  head := .hard
  tails := {.foundation}
  proof h := by
    have hf : ∀ n : ℕ, 0 + n = n := h .foundation (by simp)
    intro n
    simpa [hf n]

def chainMap : ProblemMap interp where
  artifacts := [foundationArt]
  reductions := [chainHard, viaHard]
  obligations := {.consumer}

#eval Stmt.consumer ∈ executableClosedSet m0
#eval Stmt.consumer ∈ executableClosedSet (update m0 (some foundationOnly))
#eval Stmt.consumer ∈ executableClosedSet (update m0 (some foundationAndAdapter))
#eval Stmt.adapter ∈ executableClosedSet (update m0 (some censoredHelper))
#eval Stmt.hard ∈ executableClosedSet emptyRuleMap
#eval Stmt.cycB ∈ executableClosedSet seededCycleMap
#eval executableClosedSet emptyMap = ∅
#eval executableClosedSet repeatedReductionMap = executableClosedSet m0
#eval Stmt.consumer ∈ (step chainMap)^[2] ∅
#eval Stmt.consumer ∈ (step chainMap)^[3] ∅
#eval iterativeClosedSet chainMap = executableClosedSet chainMap

example : Stmt.consumer ∉ executableClosedSet (update m0 (some foundationOnly)) := by native_decide
example : Stmt.consumer ∈ executableClosedSet (update m0 (some foundationAndAdapter)) := by native_decide
example : Stmt.cycA ∉ executableClosedSet m0 := by native_decide
example : Stmt.hard ∈ executableClosedSet emptyRuleMap := by native_decide
example : Stmt.cycB ∈ executableClosedSet seededCycleMap := by native_decide
example : executableClosedSet emptyMap = ∅ := by native_decide
example : executableClosedSet repeatedReductionMap = executableClosedSet m0 := by native_decide

theorem fixture_chain_needs_three :
    Stmt.consumer ∉ (step chainMap)^[2] ∅ ∧
      Stmt.consumer ∈ (step chainMap)^[3] ∅ := by
  native_decide

theorem fixture_iterative_matches_oracle :
    iterativeClosedSet chainMap = executableClosedSet chainMap := by
  native_decide

#print axioms mem_executable_iff_closed
#print axioms executable_eq_closedSet
#print axioms step_executableClosedSet
#print axioms returnObs_executable
#print axioms step_mono
#print axioms iterative_eq_executable
#print axioms mem_iterative_iff_closed
#print axioms step_iterativeClosedSet
#print axioms returnObs_iterative
#print axioms fixture_chain_needs_three
#print axioms fixture_iterative_matches_oracle

end DarkTower.WarMachine.ExecutableCheckedClosure
