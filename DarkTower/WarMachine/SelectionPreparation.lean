import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs
import Mathlib.Tactic

/-!
# Reading preparation inside the selection step (defect lines R1, R2)

Source: `~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` R1, R2 (claude-9,
2026-10-26, Joe's course recorded in futon2 `7871f58c5`), and ruling
`holes/labs/wm-contract/RULING-frontier-is-measured-not-pass-fail-2026-10-19.md`
item 4: selection produces target readings on demand for the targets it is
weighing and records how many of the eligible targets it assessed.

Direction of conformance: these are forward requirements on the selection
step's receipt.  The reading-era receipt (machinery-150 attempt-002,
`002-selection.edn`, projected byte-exactly in futon2
`test/resources/q8-canonical-frontier/attempt-002-projection.edn`) is encoded
below as a control and shown to fail them.  Nothing here is derived from the
runner; `full_loop_runtime.clj` is the thing to be changed.
-/

namespace DarkTower.WarMachine.SelectionPreparation

abbrev Id := Nat

/-- R2.  The preparation outcome for one eligible target whose reading is unmet.
A sum type with no absent inhabitant: the step either attempted the reading
(carrying the request it published), refused it for a typed reason, or deferred
it because the per-click budget was spent, carrying the target's position in the
backlog order. -/
inductive PreparationOutcome where
  | attempted (request : Id)
  | refused (reason : Id)
  | deferredByBudget (position : Nat)
  deriving DecidableEq, Repr

structure PreparationRow where
  task : Id
  outcome : PreparationOutcome
  deriving DecidableEq, Repr

def PreparationOutcome.isAttempted : PreparationOutcome → Bool
  | .attempted _ => true
  | _ => false

def PreparationOutcome.isRefused : PreparationOutcome → Bool
  | .refused _ => true
  | _ => false

def PreparationOutcome.isDeferred : PreparationOutcome → Bool
  | .deferredByBudget _ => true
  | _ => false

/-- One selection step's preparation facts.  `unmet` is the set of eligible
targets whose family failed `:no-current-target-reading`; `budget` is the
per-click bound (3 today, `target_reading_preparation.clj`); `preparation` is the
receipt's preparation rows. -/
structure PreparationStep where
  eligible : Finset Id
  unmet : Finset Id
  budget : Nat
  preparation : List PreparationRow
  deriving DecidableEq

def preparedTasks (rows : List PreparationRow) : Finset Id :=
  rows.toFinset.image (·.task)

def attemptedCount (rows : List PreparationRow) : Nat :=
  (rows.filter (fun r => r.outcome.isAttempted)).length

def refusedCount (rows : List PreparationRow) : Nat :=
  (rows.filter (fun r => r.outcome.isRefused)).length

def deferredCount (rows : List PreparationRow) : Nat :=
  (rows.filter (fun r => r.outcome.isDeferred)).length

/-- R1.  A valid step prepares, for every unmet eligible target, exactly one
typed outcome; the slots spent (attempts and refusals together) stay within the
budget; and a deferral is admissible only when the budget was actually spent
(otherwise "deferred" would be the empty preparation set under another name).

Amendment (claude-9, 2026-10-26, review of `8683505654`): a refusal spends a
slot too.  A step that attempted two, had one refused and deferred the other
98 is a valid preparation; under the original conjuncts (attempts alone
against the budget) it was not.  Today's `prepare!` (futon2
`target_reading_preparation.clj:52-80`) stops the whole batch at the first
refusal and leaves the refused need in `:pending` with the rest unrecorded;
that shape has no row for the refused target and fails `preparedTasks = unmet`.
The R1 Clojure repair is to continue past a refusal, recording it as a
`refused` row that counts against the budget. -/
def PreparationStep.Valid (s : PreparationStep) : Prop :=
  s.unmet ⊆ s.eligible ∧
  (s.preparation.map (·.task)).Nodup ∧
  preparedTasks s.preparation = s.unmet ∧
  attemptedCount s.preparation + refusedCount s.preparation ≤ s.budget ∧
  (0 < deferredCount s.preparation →
    attemptedCount s.preparation + refusedCount s.preparation = s.budget)

instance (s : PreparationStep) : Decidable s.Valid := by
  unfold PreparationStep.Valid
  infer_instance

/-- R1, the defect as stated: an empty preparation set beside a non-empty unmet
set is not a valid step.  (The budget hypothesis of the defect line is not
needed: with budget `0` every unmet target must still appear, as deferred.) -/
theorem empty_preparation_with_unmet_invalid (s : PreparationStep)
    (hunmet : s.unmet.Nonempty) (hempty : s.preparation = []) : ¬ s.Valid := by
  intro h
  have h3 := h.2.2.1
  rw [hempty] at h3
  simp only [preparedTasks, List.toFinset_nil, Finset.image_empty] at h3
  exact hunmet.ne_empty h3.symm

/-- Deferring everything while spending no slot (nothing attempted, nothing
refused), with budget to spare, is not preparation.  (The `hnoref` hypothesis
is new with the amendment: with refusals counting as spent slots, a step that
refused exactly `budget` targets and deferred the rest is valid.) -/
theorem all_deferred_under_budget_invalid (s : PreparationStep)
    (hpos : 0 < s.budget) (hnone : attemptedCount s.preparation = 0)
    (hnoref : refusedCount s.preparation = 0)
    (hdef : 0 < deferredCount s.preparation) : ¬ s.Valid := by
  intro h
  have := h.2.2.2.2 hdef
  omega

/-- A deferral is admitted only once the budget is spent, counting refusals. -/
theorem deferral_needs_spent_budget (s : PreparationStep) (h : s.Valid)
    (hdef : 0 < deferredCount s.preparation) :
    attemptedCount s.preparation + refusedCount s.preparation = s.budget :=
  h.2.2.2.2 hdef

/-- R2 at the receipt boundary.  The preparation field of a selection receipt is
one of these; `notRun` carries its reason.  The Clojure receipt before C4a could
hold `nil` in this position; that shape is `Option` here and `fieldTotal`
refuses it. -/
inductive PreparationRecord where
  | notRun (reason : Id)
  | ran (rows : List PreparationRow)
  deriving DecidableEq, Repr

def fieldTotal (field : Option PreparationRecord) : Prop := field.isSome = true

instance (field : Option PreparationRecord) : Decidable (fieldTotal field) := by
  unfold fieldTotal
  infer_instance

theorem absent_field_not_total : ¬ fieldTotal none := by decide

def PreparationRecord.rows : PreparationRecord → List PreparationRow
  | .notRun _ => []
  | .ran rows => rows

/-- A `notRun` record under a non-empty unmet set is typed (R2) and still not a
valid step (R1): typing the absence does not discharge the requirement. -/
theorem notRun_with_unmet_invalid (s : PreparationStep) (reason : Id)
    (hrec : s.preparation = (PreparationRecord.notRun reason).rows)
    (hunmet : s.unmet.Nonempty) : ¬ s.Valid :=
  empty_preparation_with_unmet_invalid s hunmet hrec

/-! ## Control: machinery-150 attempt-002

Task ids are positions in the sorted eligible census of the Q8a fixture
(`:support` ids sorted as strings, 109 tasks).  Ranked: 71 M-recommendation-bindings,
73 M-self-improvement-loop, 79 M-stack-geometry, 98 M-war-machine-wiring.
Unranked at S4: 31 M-digital-nomad-patterns, 40 M-formal-war-machine,
65 M-pattern-posteriors.  Unranked at S2 for `:occurrence-squares-not-authored`:
93 M-vsatarcs-writer.  The other 101 eligible tasks failed
`:no-current-target-reading`.  No checkpoint of the attempt holds a preparation
record (C4a packet premise, claude-9 2026-10-26): the field is `none`. -/

def readTasks : List Id := [31, 40, 65, 71, 73, 79, 93, 98]

def m150Unmet : Finset Id :=
  ((List.range 109).filter (fun t => decide (t ∉ readTasks))).toFinset

def m150Step : PreparationStep where
  eligible := (List.range 109).toFinset
  unmet := m150Unmet
  budget := 3
  preparation := []

theorem m150_unmet_card : m150Unmet.card = 101 := by native_decide

theorem m150_field_absent : ¬ fieldTotal none := absent_field_not_total

/-- The observed step is a certified violation of R1. -/
theorem m150_step_invalid : ¬ m150Step.Valid :=
  empty_preparation_with_unmet_invalid m150Step ⟨0, by native_decide⟩ rfl

/-- The same step under C4a's typed `:not-run` record is still invalid. -/
theorem m150_notRun_invalid : ¬ m150Step.Valid :=
  notRun_with_unmet_invalid m150Step 1 rfl ⟨0, by native_decide⟩

/-- The repaired shape (codex-11's proposal, DEFECTS R1 repair): three attempts,
the rest deferred in backlog order. -/
def m150Repaired : PreparationStep :=
  let unmet := (List.range 109).filter (fun t => decide (t ∉ readTasks))
  { m150Step with
    preparation :=
      (unmet.take 3).map (fun t => ⟨t, .attempted t⟩) ++
      ((unmet.drop 3).zipIdx.map (fun p => ⟨p.1, .deferredByBudget p.2⟩)) }

theorem m150_repaired_valid : m150Repaired.Valid := by native_decide

/-- The vacuous repair: all 101 deferred, nothing attempted, budget 3. -/
def m150AllDeferred : PreparationStep :=
  let unmet := (List.range 109).filter (fun t => decide (t ∉ readTasks))
  { m150Step with
    preparation := unmet.zipIdx.map (fun p => ⟨p.1, .deferredByBudget p.2⟩) }

theorem m150_all_deferred_invalid : ¬ m150AllDeferred.Valid := by native_decide

/-! ### Amendment controls: a refusal spends a slot

Budget 3 over `m150Unmet` (101 targets).  Reason id `1` stands for the typed
refusal reason of the refused reading request. -/

/-- Two attempted, one refused, 98 deferred: the budget is spent, the deferrals
are admissible, every unmet target has a row. -/
def m150TwoAttemptedOneRefused : PreparationStep :=
  let unmet := (List.range 109).filter (fun t => decide (t ∉ readTasks))
  { m150Step with
    preparation :=
      (unmet.take 2).map (fun t => ⟨t, .attempted t⟩) ++
      ((unmet.drop 2).take 1).map (fun t => ⟨t, .refused 1⟩) ++
      ((unmet.drop 3).zipIdx.map (fun p => ⟨p.1, .deferredByBudget p.2⟩)) }

theorem m150_two_attempted_one_refused_valid : m150TwoAttemptedOneRefused.Valid := by
  native_decide

/-- One attempted, one refused, 99 deferred: a slot was left unspent, so the
99 deferrals are not admissible. -/
def m150OneAttemptedOneRefused : PreparationStep :=
  let unmet := (List.range 109).filter (fun t => decide (t ∉ readTasks))
  { m150Step with
    preparation :=
      (unmet.take 1).map (fun t => ⟨t, .attempted t⟩) ++
      ((unmet.drop 1).take 1).map (fun t => ⟨t, .refused 1⟩) ++
      ((unmet.drop 2).zipIdx.map (fun p => ⟨p.1, .deferredByBudget p.2⟩)) }

theorem m150_one_attempted_one_refused_invalid : ¬ m150OneAttemptedOneRefused.Valid := by
  native_decide

/-- Today's `prepare!` shape after one refusal among three slots: two attempted
rows, then the batch stops; the refused target and the other 98 have no row.
Not valid, by the totality conjunct, independent of the budget conjuncts. -/
def m150StopAtRefusal : PreparationStep :=
  let unmet := (List.range 109).filter (fun t => decide (t ∉ readTasks))
  { m150Step with
    preparation := (unmet.take 2).map (fun t => ⟨t, .attempted t⟩) }

theorem m150_stop_at_refusal_invalid : ¬ m150StopAtRefusal.Valid := by native_decide

end DarkTower.WarMachine.SelectionPreparation
