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

def keyLT (a b : Entry) : Prop :=
  a.comparisonKey < b.comparisonKey

instance (a b : Entry) : Decidable (keyLT a b) := by
  unfold keyLT
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
  ∀ candidate ∈ frontier, candidate ≠ s.selected → keyLT s.selected candidate

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
    recomputedEntry, addedEntry, taskSet, keyLT]

def tiedEntry : Entry :=
  { recomputedEntry with comparisonKey := retainedEntry.comparisonKey }

def tiedSelectionFrontier : List Entry := [retainedEntry, tiedEntry]

/-- A tied objective minimum is not selectable, even when task identity would
previously have broken the tie. -/
theorem tied_minimum_selection_invalid :
    ¬ positiveSelection.Valid tiedSelectionFrontier {1, 2} := by
  native_decide
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

/-! ## Typed-unranked frontier coverage (defect lines R3, R12)

Source: `~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` R3, R12
(claude-9, 2026-10-26); Clojure carrier `futon2.aif.q8-frontier/canonical-outer-frontier`
(futon2 `f764d36a4`, schema `:wm/q8-outer-frontier-v1`) whose fields
`[:census :eligible]`, `:entries`, `:unranked` and `:census-verdict` these
definitions read.  `SelectionCertificate.Valid` above already requires
`taskSet frontier = openTasks`; this section states the typed-unranked form
beside it, so that an eligible task with no entry is accounted for (with a
reason) rather than silently absent, and shows that an accounted-but-uncovered
frontier is still not a selectable one. -/

/-- Why an eligible task has no ranked entry: a failure kind the carrier
recorded, or the carrier saying it cannot name one.  No absent inhabitant. -/
inductive OmissionReason where
  | failure (kind : Id)
  | unexplained
  deriving DecidableEq, Repr

/-- One `:unranked` row: `{:task :stage :reason :reasons}`. -/
structure Omission where
  task : Id
  stage : Id
  reason : OmissionReason
  reasons : Finset Id
  deriving DecidableEq

/-- `[:census :eligible]`, `:entries`, `:unranked`. -/
structure FrontierCoverage where
  eligible : Finset Id
  ranked : List Entry
  unranked : List Omission
  deriving DecidableEq

def omittedTasks (xs : List Omission) : Finset Id :=
  xs.toFinset.image (·.task)

/-- The headline reason is one of the recorded kinds (or is `unexplained`). -/
def OmissionReason.named : OmissionReason → Finset Id → Prop
  | .failure k, kinds => k ∈ kinds
  | .unexplained, _ => True

instance (r : OmissionReason) (kinds : Finset Id) : Decidable (r.named kinds) := by
  cases r <;> unfold OmissionReason.named <;> infer_instance

/-- R3.  Every eligible task is ranked or typed-unranked, never both and never
neither.  The carrier's refusals `:eligible-task-unaccounted`,
`:entry-also-unranked` and `:frontier-task-not-eligible` are the three ways the
union clause fails. -/
def FrontierCoverage.Valid (c : FrontierCoverage) : Prop :=
  (c.ranked.map (·.task)).Nodup ∧
  (c.unranked.map (·.task)).Nodup ∧
  Disjoint (taskSet c.ranked) (omittedTasks c.unranked) ∧
  taskSet c.ranked ∪ omittedTasks c.unranked = c.eligible ∧
  allIn c.unranked (fun o => o.reason.named o.reasons)

instance (c : FrontierCoverage) : Decidable c.Valid := by
  unfold FrontierCoverage.Valid
  infer_instance

/-- `:census-verdict :pass`: nothing unranked. -/
def FrontierCoverage.Covers (c : FrontierCoverage) : Prop := c.unranked = []

theorem unaccounted_eligible_task_invalid (c : FrontierCoverage) (t : Id)
    (ht : t ∈ c.eligible) (hr : t ∉ taskSet c.ranked) (hu : t ∉ omittedTasks c.unranked) :
    ¬ c.Valid := by
  intro h
  have : t ∈ taskSet c.ranked ∪ omittedTasks c.unranked := by rw [h.2.2.2.1]; exact ht
  rcases Finset.mem_union.mp this with h1 | h1
  · exact hr h1
  · exact hu h1

theorem entry_also_unranked_invalid (c : FrontierCoverage) (t : Id)
    (hr : t ∈ taskSet c.ranked) (hu : t ∈ omittedTasks c.unranked) : ¬ c.Valid := by
  intro h
  exact Finset.disjoint_left.mp h.2.2.1 hr hu

/-- An accounted but uncovered frontier is not a selectable Q8 frontier: with
`openTasks` the eligible census, `SelectionCertificate.Valid` fails for every
certificate, because the omitted task is eligible and not in the frontier. -/
theorem uncovered_frontier_not_selectable (c : FrontierCoverage) (hc : c.Valid)
    (o : Omission) (ho : o ∈ c.unranked) (s : SelectionCertificate) :
    ¬ s.Valid c.ranked c.eligible := by
  intro hs
  have hmem : o.task ∈ omittedTasks c.unranked := by
    simp only [omittedTasks, Finset.mem_image, List.mem_toFinset]
    exact ⟨o, ho, rfl⟩
  have hel : o.task ∈ c.eligible := by
    rw [← hc.2.2.2.1]
    exact Finset.mem_union_right _ hmem
  have hr : o.task ∈ taskSet c.ranked := by rw [hs.2.1]; exact hel
  exact Finset.disjoint_left.mp hc.2.2.1 hr hmem

/-- R12.  The headline reason discriminates: it is a failure kind that no ranked
task also carries.  `rankedKinds` is the set of kinds in the sealed menu's
`:failures` rows whose target is ranked. -/
def OmissionReason.discriminates : OmissionReason → Finset Id → Prop
  | .failure k, rankedKinds => k ∉ rankedKinds
  | .unexplained, _ => True

instance (r : OmissionReason) (rankedKinds : Finset Id) : Decidable (r.discriminates rankedKinds) := by
  cases r <;> unfold OmissionReason.discriminates <;> infer_instance

def FrontierCoverage.Discriminating (c : FrontierCoverage) (rankedKinds : Finset Id) : Prop :=
  allIn c.unranked (fun o => o.reason.discriminates rankedKinds)

instance (c : FrontierCoverage) (rankedKinds : Finset Id) :
    Decidable (c.Discriminating rankedKinds) := by
  unfold FrontierCoverage.Discriminating
  infer_instance

theorem shared_kind_reason_not_discriminating (c : FrontierCoverage) (rankedKinds : Finset Id)
    (o : Omission) (ho : o ∈ c.unranked) (k : Id) (hk : o.reason = .failure k)
    (hshared : k ∈ rankedKinds) : ¬ c.Discriminating rankedKinds := by
  intro h
  have hd : o.reason.discriminates rankedKinds := h o ho
  rw [hk] at hd
  exact hd hshared

/-! ### Control: machinery-150 attempt-002 (the Q8a fixture)

Task ids are positions in the sorted `:support` census (109 tasks).  Ranked:
71 M-recommendation-bindings, 73 M-self-improvement-loop, 79 M-stack-geometry,
98 M-war-machine-wiring.  Unranked at S4 (stage 4): 31 M-digital-nomad-patterns,
40 M-formal-war-machine, 65 M-pattern-posteriors.  Unranked at S2 (stage 2):
93 M-vsatarcs-writer and the 101 others.  Failure kinds: 1
`:no-current-target-reading`, 2 `:occurrence-squares-not-authored`, 3
`:seed-not-in-graph`, 4 `:isolated-seed`, 5 `:target-class-unknown`, 6
`:void-pattern-citation`, 7 `:frontier-too-wide-for-exact-enumeration`, 8
`:occurrence-identity-absent`.  The ranked tasks' menu failure kinds are
{3, 4, 6, 7, 8}; the carrier's headline reasons for 31 and 40 are 4 and 3. -/

def m150RankedTasks : List Id := [71, 73, 79, 98]
def m150S4Tasks : List Id := [31, 40, 65]

def m150Ranked : List Entry := m150RankedTasks.map stableEntry

def m150S2Unranked : List Omission :=
  ((List.range 109).filter
      (fun t => decide (t ∉ m150RankedTasks ∧ t ∉ m150S4Tasks ∧ t ≠ 93))).map
    (fun t => ⟨t, 2, .failure 1, {1}⟩)

def m150Coverage : FrontierCoverage where
  eligible := (List.range 109).toFinset
  ranked := m150Ranked
  unranked :=
    ⟨31, 4, .failure 4, {4, 5}⟩ :: ⟨40, 4, .failure 3, {3, 5}⟩ ::
    ⟨65, 4, .failure 5, {5}⟩ :: ⟨93, 2, .failure 2, {2}⟩ :: m150S2Unranked

def m150RankedKinds : Finset Id := {3, 4, 6, 7, 8}

theorem m150_unranked_count : m150Coverage.unranked.length = 105 := by native_decide

/-- The Q8a carrier's reading: every eligible task accounted for (`:decided-failure`,
not `:not-recomputable`). -/
theorem m150_coverage_valid : m150Coverage.Valid := by native_decide

theorem m150_not_covered : ¬ m150Coverage.Covers := by
  simp [FrontierCoverage.Covers, m150Coverage]

/-- R3 on the receipt: no certificate makes this frontier selectable over its
own eligible census. -/
theorem m150_not_selectable (s : SelectionCertificate) :
    ¬ s.Valid m150Coverage.ranked m150Coverage.eligible :=
  uncovered_frontier_not_selectable m150Coverage m150_coverage_valid
    ⟨40, 4, .failure 3, {3, 5}⟩ (by simp [m150Coverage]) s

/-- R12 on the receipt: M-formal-war-machine's headline `:seed-not-in-graph` is
also carried by ranked M-self-improvement-loop. -/
theorem m150_not_discriminating : ¬ m150Coverage.Discriminating m150RankedKinds :=
  shared_kind_reason_not_discriminating m150Coverage m150RankedKinds
    ⟨40, 4, .failure 3, {3, 5}⟩ (by simp [m150Coverage]) 3 rfl (by decide)

/-- The repaired carrier: headline reasons taken outside the ranked kinds. -/
def m150Repaired : FrontierCoverage :=
  { m150Coverage with
    unranked :=
      ⟨31, 4, .failure 5, {4, 5}⟩ :: ⟨40, 4, .failure 5, {3, 5}⟩ ::
      ⟨65, 4, .failure 5, {5}⟩ :: ⟨93, 2, .failure 2, {2}⟩ :: m150S2Unranked }

theorem m150_repaired_valid : m150Repaired.Valid := by native_decide
theorem m150_repaired_discriminating : m150Repaired.Discriminating m150RankedKinds := by
  native_decide

/-- The silent form the stub produced: four entries, nothing unranked, eligible
census of 109.  Not valid coverage. -/
def m150Stub : FrontierCoverage := { m150Coverage with unranked := [] }

theorem m150_stub_invalid : ¬ m150Stub.Valid :=
  unaccounted_eligible_task_invalid m150Stub 40 (by simp [m150Stub, m150Coverage])
    (by native_decide) (by simp [m150Stub, omittedTasks])

/-! ## Cascade certification needs the selected carrier's stages (defect line R4)

Source: DEFECTS R4; `q8_frontier.clj:438` returns
`{:status :not-recomputable :reason :policy-stages-absent}` when the decision
has no `[:selection-certificate :policy-stages]`; on the canonical route they
are absent (machinery-150 attempt-002). -/

/-- Where the stages came from: the carrier's `[:recomputation :q4]` pin and the
sealed menu pin.  Zero is the refused "no pin". -/
structure StageProvenance where
  q4Pin : Id
  menuPin : Id
  deriving DecidableEq, Repr

inductive CascadeCertification where
  | notRecomputable (reason : Id)
  | present (c : TargetCascadeCertificate) (provenance : StageProvenance)
  deriving DecidableEq

/-- `:policy-stages-absent` and `:stage-provenance-absent`. -/
def policyStagesAbsent : Id := 1
def stageProvenanceAbsent : Id := 2

/-- Certification is a function of the stage input.  No input, no `present`;
input without provenance, no `present`. -/
def certifyStages : Option (TargetCascadeCertificate × StageProvenance) → CascadeCertification
  | none => .notRecomputable policyStagesAbsent
  | some (c, p) =>
    if p.q4Pin ≠ 0 ∧ p.menuPin ≠ 0 then .present c p
    else .notRecomputable stageProvenanceAbsent

/-- A record's certification claim is valid only when it is what the stage
input certifies. -/
def CertificationClaim.Valid (stages : Option (TargetCascadeCertificate × StageProvenance))
    (claim : CascadeCertification) : Prop :=
  claim = certifyStages stages

instance (stages : Option (TargetCascadeCertificate × StageProvenance))
    (claim : CascadeCertification) : Decidable (CertificationClaim.Valid stages claim) := by
  unfold CertificationClaim.Valid
  infer_instance

theorem absent_stages_never_present (c : TargetCascadeCertificate) (p : StageProvenance) :
    certifyStages none ≠ .present c p := by
  simp [certifyStages]

theorem present_claim_without_stages_invalid (c : TargetCascadeCertificate)
    (p : StageProvenance) : ¬ CertificationClaim.Valid none (.present c p) := by
  unfold CertificationClaim.Valid
  exact fun h => absent_stages_never_present c p h.symm

theorem unpinned_stages_never_present (c : TargetCascadeCertificate) (p : StageProvenance)
    (hp : p.q4Pin = 0 ∨ p.menuPin = 0) (c' : TargetCascadeCertificate) (p' : StageProvenance) :
    certifyStages (some (c, p)) ≠ .present c' p' := by
  rcases hp with h | h <;> simp [certifyStages, h]

/-- The canonical route today: stages absent, so the only valid claim is the
typed refusal, and `Q8`'s `selectedCascade.Valid` clause has nothing to check. -/
theorem m150_cascade_certification :
    certifyStages none = .notRecomputable policyStagesAbsent := rfl

theorem pinned_stages_present (c : TargetCascadeCertificate) :
    certifyStages (some (c, ⟨5, 6⟩)) = .present c ⟨5, 6⟩ := by
  simp [certifyStages]

/-! ## U1, a question rather than a clause: graph failures on a reading

Observation (m150-002, claude-9 2026-10-26): the graph failures
`:isolated-seed`, `:seed-not-in-graph`, `:void-pattern-citation` are carried from
a reading into a `:computed` family's `:failures` (policy-id nil);
`family-coverage-kind` maps none of them to a coverage kind, so they count as
`:current` and touch neither scoring nor binding.  All four ranked tasks carry
them, including the chosen M-war-machine-wiring (`:isolated-seed`).  Today:
neither disqualifying nor measured.

Conjecture (claude-5): a reading's graph failures are a measurement of the
reading, not a standing verdict on the target.  They should raise the ambiguity
of every policy drawn from that reading (the reading is evidence of lower
precision about what the target's patterns are), monotonically in the set of
failures, while the target stays eligible.  Disqualifying on them would
reinstate the whitelist in another form (landscape §10.1, Joe's rule).  Stated
as a predicate on a scorer; not proved; no runtime carries it. -/
def U1Conjecture {α : Type} [Preorder α] (ambiguity : Id → Finset Id → α)
    (eligibleUnder : Id → Finset Id → Prop) : Prop :=
  (∀ t (k₁ k₂ : Finset Id), k₁ ⊆ k₂ → ambiguity t k₁ ≤ ambiguity t k₂) ∧
  (∀ t k, eligibleUnder t ∅ → eligibleUnder t k)

end DarkTower.WarMachine.IncrementalTaskFrontier
