import Mathlib.Tactic

/-!
# What a click's record binds (defect lines R10, R11)

Source: `~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` R10, R11
(claude-9, 2026-10-26).

R10.  A click's environment is the loaded namespace identities, not the disk
HEAD; the run record binds the loaded hashes.  Observed on click c52
(`~/notes/wm-next/diagnostic-clicks/report.md`): the child stopped at
`:runner-source` with `:stale-outer-selection-composition`; the namespace
`meta-live-outer-selector` had loaded hash `9d317e32…` and disk hash
`f878d316…`.  That refusal is the correct behaviour; the clause is kept as a
check.

R11.  The parent's verdict is a function of the child's completion; `notChecked`
is a distinct inhabitant from `passed`.  Observed on both machinery-150 parents
(`~/notes/wm-next/diagnostic-clicks/remaining-two/report.md`): each exited 1
because the requirements record was absent when it returned; the children later
wrote records; no child requirements verdict file was found.
-/

namespace DarkTower.WarMachine.ClickRecordBinding

abbrev Id := Nat

structure NamespaceIdentity where
  ns : Id
  loadedHash : Id
  diskHash : Id
  deriving DecidableEq, Repr

def NamespaceIdentity.Current (n : NamespaceIdentity) : Prop := n.loadedHash = n.diskHash

instance (n : NamespaceIdentity) : Decidable n.Current := by
  unfold NamespaceIdentity.Current
  infer_instance

/-- The run record's environment binding: the namespaces the click ran in, and
the `(namespace, hash)` pairs the record binds. -/
structure RunRecordBinding where
  environment : List NamespaceIdentity
  bound : List (Id × Id)
  deriving DecidableEq, Repr

def loadedPairs (env : List NamespaceIdentity) : List (Id × Id) :=
  env.map (fun n => (n.ns, n.loadedHash))

def diskPairs (env : List NamespaceIdentity) : List (Id × Id) :=
  env.map (fun n => (n.ns, n.diskHash))

/-- R10.  The record binds exactly the loaded hashes. -/
def RunRecordBinding.Valid (b : RunRecordBinding) : Prop :=
  b.bound = loadedPairs b.environment

instance (b : RunRecordBinding) : Decidable b.Valid := by
  unfold RunRecordBinding.Valid
  infer_instance

/-- A record that binds disk hashes while some loaded namespace is stale is
invalid: it names code the click did not run. -/
theorem disk_bound_stale_namespace_invalid (b : RunRecordBinding) (n : NamespaceIdentity)
    (hn : n ∈ b.environment) (hstale : ¬ n.Current)
    (hbound : b.bound = diskPairs b.environment) : ¬ b.Valid := by
  intro h
  unfold RunRecordBinding.Valid at h
  rw [hbound] at h
  unfold diskPairs loadedPairs at h
  have := (List.map_inj_left.mp h) n hn
  exact hstale (Prod.mk.inj this).2.symm

/-- Where every namespace is current the two bindings coincide, so the check
costs nothing on a fresh JVM. -/
theorem current_environment_bindings_agree (env : List NamespaceIdentity)
    (hcur : ∀ n ∈ env, n.Current) : diskPairs env = loadedPairs env := by
  unfold diskPairs loadedPairs
  exact List.map_congr_left (fun n hn => by rw [hcur n hn])

/-! ### Control: click c52

Namespace 1 is `futon2.aif.meta-live-outer-selector`; the hashes are the first
sixteen bits of the recorded sha256s: loaded `9d31` = 40241, disk `f878` = 63608. -/

def c52Selector : NamespaceIdentity := ⟨1, 40241, 63608⟩

theorem c52_selector_stale : ¬ c52Selector.Current := by decide

/-- The record the click correctly refused to write: disk hashes bound. -/
theorem c52_disk_binding_invalid :
    ¬ (RunRecordBinding.mk [c52Selector] (diskPairs [c52Selector])).Valid := by decide

theorem c52_loaded_binding_valid :
    (RunRecordBinding.mk [c52Selector] (loadedPairs [c52Selector])).Valid := by decide

/-! ## R11: parent verdict from child completion -/

inductive Verdict where
  | passed
  | failed
  | notChecked
  deriving DecidableEq, Repr

theorem notChecked_ne_passed : Verdict.notChecked ≠ Verdict.passed := by decide

inductive ChildCompletion where
  | pending
  | complete (verdict : Verdict)
  deriving DecidableEq, Repr

/-- The parent's verdict is this function and nothing else. -/
def parentVerdict : ChildCompletion → Verdict
  | .pending => .notChecked
  | .complete v => v

/-- The parent record: the child completion it is bound to (the Clojure record
may lack it, hence `Option`), and the verdict it reports. -/
structure ParentRecord where
  child : Option ChildCompletion
  verdict : Verdict
  deriving DecidableEq, Repr

def ParentRecord.valid (r : ParentRecord) : Bool :=
  match r.child with
  | none => false
  | some c => r.verdict == parentVerdict c

/-- R11.  A parent record is bound to a child completion and reports its
verdict. -/
def ParentRecord.Valid (r : ParentRecord) : Prop := r.valid = true

instance (r : ParentRecord) : Decidable r.Valid := by
  unfold ParentRecord.Valid
  infer_instance

theorem unbound_child_invalid (v : Verdict) : ¬ (ParentRecord.mk none v).Valid := by
  simp [ParentRecord.Valid, ParentRecord.valid]

theorem pending_child_not_passed (r : ParentRecord) (h : r.child = some .pending)
    (hv : r.Valid) : r.verdict = .notChecked := by
  simp_all [ParentRecord.Valid, ParentRecord.valid, parentVerdict]

theorem pending_child_passed_invalid :
    ¬ (ParentRecord.mk (some .pending) .passed).Valid := by decide

/-- A parent still reporting `notChecked` after the child completed is stale. -/
theorem completed_child_stale_parent_invalid (v : Verdict) (hv : v ≠ .notChecked) :
    ¬ (ParentRecord.mk (some (.complete v)) .notChecked).Valid := by
  cases v <;> simp_all [ParentRecord.Valid, ParentRecord.valid, parentVerdict]

/-! ### Control: the machinery-150 parents

Both parents returned with no child requirements verdict bound (none was ever
written) and exit code 1, read as `notChecked`. -/

def m150Parent : ParentRecord := ⟨none, .notChecked⟩

theorem m150_parent_invalid : ¬ m150Parent.Valid := unbound_child_invalid _

/-- Exit 1 was the right reading of that state: `passed` would also have been
invalid, and for a second reason. -/
theorem m150_parent_passed_invalid : ¬ (ParentRecord.mk none .passed).Valid :=
  unbound_child_invalid _

end DarkTower.WarMachine.ClickRecordBinding
