import DarkTower.WarMachine.R20CheckedMapCarry

/-!
# Executable finite checked-map closure

This module refines `CheckedProblemMap.Closed` on a fixed finite statement
universe. It never evaluates the interpretation `I`; artifacts and reductions
already contain the proofs. The executable construction enumerates the finite
candidate subsets (at most `2 ^ card S`) and intersects precisely those closed
under the existing artifact and reduction rules. This is extensionally the
same least fixed point as repeated monotone saturation, while avoiding any
decidability assumption on `I`.

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

theorem closureObs_executable (scored : Finset S) (m : ProblemMap I) :
    scored ∩ executableClosedSet m = closureObs scored m := by
  rw [executable_eq_closedSet]
  rfl

theorem returnObs_executable {Label A : Type} (m : ProblemMap I)
    (scored : Finset S) (realize : A → Option (ReturnReport I Label)) (a : A) :
    scored ∩ executableClosedSet (update m (realize a)) =
      returnObs m scored realize a := by
  rw [executable_eq_closedSet]
  rfl

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

#eval Stmt.consumer ∈ executableClosedSet m0
#eval Stmt.consumer ∈ executableClosedSet (update m0 (some foundationOnly))
#eval Stmt.consumer ∈ executableClosedSet (update m0 (some foundationAndAdapter))
#eval Stmt.adapter ∈ executableClosedSet (update m0 (some censoredHelper))
#eval Stmt.hard ∈ executableClosedSet emptyRuleMap
#eval Stmt.cycB ∈ executableClosedSet seededCycleMap
#eval executableClosedSet emptyMap = ∅
#eval executableClosedSet repeatedReductionMap = executableClosedSet m0

example : Stmt.consumer ∉ executableClosedSet (update m0 (some foundationOnly)) := by native_decide
example : Stmt.consumer ∈ executableClosedSet (update m0 (some foundationAndAdapter)) := by native_decide
example : Stmt.cycA ∉ executableClosedSet m0 := by native_decide
example : Stmt.hard ∈ executableClosedSet emptyRuleMap := by native_decide
example : Stmt.cycB ∈ executableClosedSet seededCycleMap := by native_decide
example : executableClosedSet emptyMap = ∅ := by native_decide
example : executableClosedSet repeatedReductionMap = executableClosedSet m0 := by native_decide

#print axioms mem_executable_iff_closed
#print axioms executable_eq_closedSet
#print axioms step_executableClosedSet
#print axioms returnObs_executable

end DarkTower.WarMachine.ExecutableCheckedClosure
