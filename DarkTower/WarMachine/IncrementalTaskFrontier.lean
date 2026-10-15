import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs
import Mathlib.Tactic

/-!
# Incremental outer-task frontier

The outer selector ranks durable task entries.  This carrier is deliberately
separate from target-local cascade policy scoring (`G`).
-/

namespace DarkTower.WarMachine.IncrementalTaskFrontier

abbrev Id := Nat

/-- A decidable, list-bounded universal.  Unlike spelling this as an
unrestricted dependent `∀`, its decision procedure only visits the entries
that are actually in the frontier. -/
def allIn {α : Type} (xs : List α) (p : α → Prop) : Prop :=
  ∀ x ∈ xs, p x

instance {α : Type} [DecidableEq α] (xs : List α) (p : α → Prop)
    [DecidablePred p] : Decidable (allIn xs p) :=
  List.decidableBAll p xs

structure Entry where
  task : Id
  observation : Id
  evidence : Id
  rankingLaw : Id
  rankingVersion : Nat
  dependencies : Finset Id
  comparisonKey : Nat
  freshnessEpoch : Nat
  deriving DecidableEq

structure WorldDelta where
  changedObservations : Finset Id
  addedTasks : Finset Id
  removedTasks : Finset Id
  deriving DecidableEq

def taskSet (entries : List Entry) : Finset Id :=
  entries.toFinset.image (·.task)

def affected (delta : WorldDelta) (entry : Entry) : Bool :=
  decide (entry.dependencies ∩ delta.changedObservations).Nonempty

structure RefreshCertificate where
  prior : List Entry
  current : List Entry
  retained : List Entry
  invalidated : List Entry
  recomputed : List Entry
  removed : Finset Id
  delta : WorldDelta
  currentOpenTasks : Finset Id
  deriving DecidableEq

/-- Exact incremental refresh: prior entries are partitioned, changed entries
and additions are recomputed, retained values are literally preserved, and the
current frontier covers exactly the current open population. -/
def RefreshCertificate.Valid (c : RefreshCertificate) : Prop :=
  (c.prior.map (·.task)).Nodup ∧
  (c.current.map (·.task)).Nodup ∧
  c.removed = c.delta.removedTasks ∩ taskSet c.prior ∧
  allIn c.retained (fun e => e ∈ c.prior ∧ ¬ affected c.delta e ∧
    e.task ∉ c.removed ∧ e ∈ c.current) ∧
  allIn c.invalidated (fun e => e ∈ c.prior ∧ affected c.delta e ∧
    e.task ∉ c.removed) ∧
  allIn c.prior (fun e => e.task ∉ c.removed →
    (e ∈ c.invalidated ↔ affected c.delta e)) ∧
  taskSet c.prior = taskSet c.retained ∪ taskSet c.invalidated ∪ c.removed ∧
  taskSet c.recomputed = taskSet c.invalidated ∪ c.delta.addedTasks ∧
  allIn c.recomputed (fun e => e ∈ c.current) ∧
  taskSet c.current = taskSet c.retained ∪ taskSet c.recomputed ∧
  taskSet c.current = c.currentOpenTasks ∧
  Disjoint c.removed c.currentOpenTasks ∧
  Disjoint c.delta.addedTasks (taskSet c.prior) ∧
  Disjoint c.delta.addedTasks c.delta.removedTasks

instance (c : RefreshCertificate) : Decidable c.Valid := by
  unfold RefreshCertificate.Valid
  infer_instance

theorem changed_dependency_cannot_be_retained
    (c : RefreshCertificate) (e : Entry)
    (h : c.Valid) (he : e ∈ c.retained) : ¬ affected c.delta e := by
  rcases h with ⟨_, _, _, hretained, _⟩
  exact (hretained e he).2.1

theorem unchanged_disjoint_entry_retained_identically
    (c : RefreshCertificate) (e : Entry)
    (h : c.Valid) (he : e ∈ c.retained) : e ∈ c.prior ∧ e ∈ c.current := by
  rcases h with ⟨_, _, _, hretained, _⟩
  exact ⟨(hretained e he).1, (hretained e he).2.2.2⟩

theorem invalidated_task_cannot_be_omitted
    (c : RefreshCertificate) (e : Entry)
    (h : c.Valid) (he : e ∈ c.invalidated) : e.task ∈ taskSet c.recomputed := by
  rcases h with ⟨_, _, _, _, _, _, _, hrecomputed, _⟩
  rw [hrecomputed]
  exact Finset.mem_union_left _ (by
    simp only [taskSet, Finset.mem_image, List.mem_toFinset]
    exact ⟨e, he, rfl⟩)

theorem added_task_cannot_be_omitted
    (c : RefreshCertificate) (t : Id)
    (h : c.Valid) (ht : t ∈ c.delta.addedTasks) : t ∈ taskSet c.recomputed := by
  rcases h with ⟨_, _, _, _, _, _, _, hrecomputed, _⟩
  rw [hrecomputed]
  exact Finset.mem_union_right _ ht

def keyLE (a b : Entry) : Prop :=
  a.comparisonKey < b.comparisonKey ∨
    (a.comparisonKey = b.comparisonKey ∧ a.task ≤ b.task)

instance (a b : Entry) : Decidable (keyLE a b) := by
  unfold keyLE
  infer_instance

structure SelectionCertificate where
  selected : Entry
  currentEpoch : Nat
  deriving DecidableEq

def SelectionCertificate.Valid (frontier : List Entry) (openTasks : Finset Id)
    (s : SelectionCertificate) : Prop :=
  s.selected ∈ frontier ∧
  taskSet frontier = openTasks ∧
  s.selected.freshnessEpoch = s.currentEpoch ∧
  allIn frontier (keyLE s.selected)

instance (frontier : List Entry) (openTasks : Finset Id) (s : SelectionCertificate) :
    Decidable (s.Valid frontier openTasks) := by
  unfold SelectionCertificate.Valid
  infer_instance

/-- Under strict refresh-before-selection there is no selectable frontier until
every affected prior entry has a recomputed current entry. -/
theorem unresolved_stale_contender_prevents_selection
    (c : RefreshCertificate) (e : Entry) (h : c.Valid)
    (he : e ∈ c.invalidated) (homitted : e.task ∉ taskSet c.recomputed) : False :=
  homitted (invalidated_task_cannot_be_omitted c e h he)

theorem removed_task_cannot_be_selected
    (refresh : RefreshCertificate) (selection : SelectionCertificate)
    (hr : refresh.Valid) (hs : selection.Valid refresh.current refresh.currentOpenTasks) :
    selection.selected.task ∉ refresh.removed := by
  intro hm
  have hopen : selection.selected.task ∈ refresh.currentOpenTasks := by
    rw [← hs.2.1]
    simp only [taskSet, Finset.mem_image, List.mem_toFinset]
    exact ⟨selection.selected, hs.1, rfl⟩
  rcases hr with ⟨_, _, _, _, _, _, _, _, _, _, _, hdisjoint, _, _⟩
  exact Finset.disjoint_left.mp hdisjoint hm hopen

/-- Retention is literal entry equality, so its comparison key and epoch need
no population-wide ordinal rewrite. -/
theorem no_global_reindexing_required
    (c : RefreshCertificate) (e : Entry) (h : c.Valid) (he : e ∈ c.retained) :
    ∃ currentEntry ∈ c.current,
      currentEntry = e ∧ currentEntry.comparisonKey = e.comparisonKey ∧
        currentEntry.freshnessEpoch = e.freshnessEpoch := by
  rcases h with ⟨_, _, _, hretained, _⟩
  exact ⟨e, (hretained e he).2.2.2, rfl, rfl, rfl⟩

/-- The open-task census beside the ranked frontier.  Every open task is
exactly one of: eligible for ranking, or excluded with the typed reason the
selector recorded (reason id `0` stands for "no reason" and is refused).
Excluded tasks carry no comparison key: the selector never ranked them. -/
structure Exclusion where
  task : Id
  reason : Id
  deriving DecidableEq

structure EligibilityCensus where
  eligible : Finset Id
  excluded : List Exclusion
  deriving DecidableEq

def excludedTasks (xs : List Exclusion) : Finset Id :=
  xs.toFinset.image (·.task)

def EligibilityCensus.Valid (c : EligibilityCensus) (openTasks : Finset Id) : Prop :=
  (c.excluded.map (·.task)).Nodup ∧
  allIn c.excluded (fun x => x.reason ≠ 0) ∧
  Disjoint c.eligible (excludedTasks c.excluded) ∧
  c.eligible ∪ excludedTasks c.excluded = openTasks

instance (c : EligibilityCensus) (openTasks : Finset Id) :
    Decidable (c.Valid openTasks) := by
  unfold EligibilityCensus.Valid
  infer_instance

theorem omitted_open_task_invalid (c : EligibilityCensus) (openTasks : Finset Id)
    (t : Id) (ht : t ∈ openTasks) (he : t ∉ c.eligible)
    (hx : t ∉ excludedTasks c.excluded) : ¬ c.Valid openTasks := by
  intro h
  have : t ∈ c.eligible ∪ excludedTasks c.excluded := by rw [h.2.2.2]; exact ht
  rcases Finset.mem_union.mp this with h1 | h1
  · exact he h1
  · exact hx h1

/-- Target-local cascade identity correspondence.  It does not quantify over
other open tasks.  Every stage holds the same truthful set up to scoring; a
requirement may then remove scored policies before the one comparison
(`requirementExcluded`, justified at Q8 by the run's Q6 facts), and the
posterior is exactly what remains.  Multiple posterior policies are required
only when more than one selectable policy remains. -/
structure TargetCascadeCertificate where
  selectedTask : Id
  availableAdmissible : Finset Id
  constructed : Finset Id
  admitted : Finset Id
  scored : Finset Id
  requirementExcluded : Finset Id
  posterior : Finset Id
  deriving DecidableEq

def TargetCascadeCertificate.Valid (c : TargetCascadeCertificate) : Prop :=
  c.availableAdmissible = c.constructed ∧
  c.constructed = c.admitted ∧
  c.admitted = c.scored ∧
  c.requirementExcluded ⊆ c.scored ∧
  c.posterior = c.scored \ c.requirementExcluded ∧
  (1 < (c.scored \ c.requirementExcluded).card → 1 < c.posterior.card)

instance (c : TargetCascadeCertificate) : Decidable c.Valid := by
  unfold TargetCascadeCertificate.Valid
  infer_instance

theorem constructed_admitted_mismatch_invalid
    (c : TargetCascadeCertificate) (h : c.constructed ≠ c.admitted) : ¬ c.Valid := by
  intro hv; exact h hv.2.1

theorem admitted_scored_mismatch_invalid
    (c : TargetCascadeCertificate) (h : c.admitted ≠ c.scored) : ¬ c.Valid := by
  intro hv; exact h hv.2.2.1

theorem scored_posterior_mismatch_invalid
    (c : TargetCascadeCertificate) (h : c.posterior ≠ c.scored \ c.requirementExcluded) :
    ¬ c.Valid := by
  intro hv; exact h hv.2.2.2.2.1

theorem exclusion_outside_scored_invalid
    (c : TargetCascadeCertificate) (h : ¬ c.requirementExcluded ⊆ c.scored) : ¬ c.Valid := by
  intro hv; exact h hv.2.2.2.1

theorem historical_all_target_breadth_not_a_premise
    (c : TargetCascadeCertificate) (h : c.Valid)
    (unrelatedOpenTasks : Finset Id) : c.Valid := h

def retainedEntry : Entry := ⟨1, 10, 100, 20, 3, {10}, 7, 4⟩
def changedEntry : Entry := ⟨2, 11, 101, 20, 3, {11}, 9, 4⟩
def recomputedEntry : Entry := ⟨2, 12, 102, 20, 3, {11}, 8, 5⟩
def addedEntry : Entry := ⟨3, 13, 103, 20, 3, {13}, 10, 5⟩

def positiveRefresh : RefreshCertificate where
  prior := [retainedEntry, changedEntry]
  current := [retainedEntry, recomputedEntry, addedEntry]
  retained := [retainedEntry]
  invalidated := [changedEntry]
  recomputed := [recomputedEntry, addedEntry]
  removed := ∅
  delta := ⟨{11}, {3}, ∅⟩
  currentOpenTasks := {1, 2, 3}

def positiveSelection : SelectionCertificate := ⟨retainedEntry, 4⟩
def positiveCascade : TargetCascadeCertificate := ⟨1, {40}, {40}, {40}, {40}, ∅, {40}⟩

/-- A literal, unchanged frontier useful for closed positive witnesses.  Keys
are stable task identities rather than population ordinals. -/
def stableEntry (task : Id) : Entry :=
  ⟨task, task, task, 1, 1, ∅, task, 0⟩

def stableEntries (tasks : List Id) : List Entry :=
  tasks.map stableEntry

def stableRefresh (tasks : List Id) : RefreshCertificate where
  prior := stableEntries tasks
  current := stableEntries tasks
  retained := stableEntries tasks
  invalidated := []
  recomputed := []
  removed := ∅
  delta := ⟨∅, ∅, ∅⟩
  currentOpenTasks := tasks.toFinset

def stableSelection (task : Id) : SelectionCertificate :=
  ⟨stableEntry task, 0⟩

def singletonCascade (task policy : Id) : TargetCascadeCertificate :=
  ⟨task, {policy}, {policy}, {policy}, {policy}, ∅, {policy}⟩

theorem positive_refresh_valid : positiveRefresh.Valid := by
  simp [RefreshCertificate.Valid, positiveRefresh, retainedEntry, changedEntry,
    recomputedEntry, addedEntry, taskSet, affected, allIn]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  aesop
theorem positive_selection_valid :
    positiveSelection.Valid positiveRefresh.current positiveRefresh.currentOpenTasks := by
  simp [SelectionCertificate.Valid, positiveSelection, positiveRefresh, retainedEntry,
    recomputedEntry, addedEntry, taskSet, keyLE, allIn]
theorem positive_cascade_valid : positiveCascade.Valid := by
  decide

def omittedRefresh : RefreshCertificate :=
  { positiveRefresh with
    current := [retainedEntry, addedEntry]
    recomputed := [addedEntry]
    currentOpenTasks := {1, 3} }

def mismatchedCascade : TargetCascadeCertificate :=
  ⟨1, {40}, {40}, {40}, {40}, ∅, {41}⟩

def twoAdmissibleOnePosterior : TargetCascadeCertificate :=
  ⟨1, {40, 41}, {40, 41}, {40, 41}, {40, 41}, ∅, {40}⟩

/-- The previous run's refused policy 41, removed by Q6 before selection:
truthful stages, and a posterior of what remains. -/
def requirementExcludedCascade : TargetCascadeCertificate :=
  ⟨1, {40, 41}, {40, 41}, {40, 41}, {40, 41}, {41}, {40}⟩

/-- An exclusion that names a policy that was never scored. -/
def foreignExclusionCascade : TargetCascadeCertificate :=
  ⟨1, {40, 41}, {40, 41}, {40, 41}, {40, 41}, {42}, {40, 41}⟩

theorem omitted_refresh_invalid : ¬ omittedRefresh.Valid := by
  native_decide
theorem mismatched_cascade_invalid : ¬ mismatchedCascade.Valid := by
  decide
theorem two_admissible_one_posterior_invalid : ¬ twoAdmissibleOnePosterior.Valid := by
  decide
theorem requirement_excluded_cascade_valid : requirementExcludedCascade.Valid := by
  decide
theorem foreign_exclusion_invalid : ¬ foreignExclusionCascade.Valid := by
  decide

end DarkTower.WarMachine.IncrementalTaskFrontier
