/-!
# The learning replay scores the pending cascade over the placements the
# selection pinned (R32)

Source: `~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` R32 (claude-2,
2026-11-04) and the restoration trail.  Lean first; the Clojure conforms in
packet R32-b.  Beside `R20Step` (the placed gate `placedGate keep := .gate keep`,
whose `keep` refuses a fact with no placement key) and
`SPEC-placement-adapter-2026-11-02`.

**What happened.**  Clicks `wm-click-9b7d7f52…` and `wm-click-259f044c…`
(2026-11-04 00:35Z, 00:38Z) refused `:outer-score/placement-unavailable` before
scoring.  The pending selection in `outer-state` was run 561c5ec3's, the first
whose cascade carries `:placed-gate`.  `resolve-pending-learning` rebuilt that
run's Giraffe field with `outer-observation/giraffe-field` and never annotated
it, then `outer-state/consume-observation` re-applied the pending cascade to it
(`next-state` → `outer-model` → `cascade-pick` → `placed-workable?`), and the gate
refused on the first fact, as its contract says it must when the adapter was not
wired.  The refusal propagates to the whole click; the pending is never consumed;
every later click meets it again.

**What this module settles.**

1. The replay is a second observation site.  It carries placement facts, and the
   placements it carries are the ones the selection pinned (`:placement/source
   :tsv :sha256`), not whatever file is current.
2. A pinned source whose sha differs at replay time, or that cannot be loaded,
   defers the learning with a typed reason.  Nothing is scored on other facts.
3. A pending selection with no pinned source (made before the adapter) is
   annotated with the typed absence; its cascade has no placed gate and scores
   as before.
4. Under the repaired replay no learning resolution ever refuses on a missing
   placement key.  Today's does, on exactly the witness.

**Clojure correspondence (R32-b).**  `previous-giraffe-observation` loads the
placements from the pinned path, compares the loaded sha with the pinned sha,
annotates on equality, and otherwise returns a typed marker that
`resolve-pending-learning` passes through as `{:status :deferred :reason
:placement-source-changed | :placement-source-absent}`; a pending without
`:placement/source` is annotated with `absent-placement` on every fact.
-/

namespace DarkTower.WarMachine.PlacementReplay

/-- A content sha, transcribed as a numeral. -/
abbrev Sha := Nat

/-- What the replay can read: the sha the selection pinned (if any), the sha of
the source as loaded now (if loadable), and whether the rebuilt observation
carries a placement key on every fact. -/
structure Replay where
  pinned : Option Sha
  current : Option Sha
  annotated : Bool
  deriving DecidableEq, Repr

inductive Reason where
  | placementSourceChanged
  | placementSourceAbsent
  deriving DecidableEq, Repr

inductive Outcome where
  | scored
  | deferred (reason : Reason)
  | refused
  deriving DecidableEq, Repr

/-- The deployed replay: the rebuilt field is never annotated, and a placed-gate
cascade over an un-annotated field refuses (`placed-workable?`). -/
def currentReplay (r : Replay) : Outcome :=
  if r.annotated then .scored else .refused

/-- Whether the deployed code annotates the replay field: it does not. -/
def deployedAnnotates : Bool := false

/-- The repaired replay: annotate from the pinned source, defer on a changed or
missing source, score the typed absence when nothing was pinned. -/
def repairedReplay (r : Replay) : Outcome :=
  match r.pinned, r.current with
  | some p, some c => if p = c then .scored else .deferred .placementSourceChanged
  | some _, none => .deferred .placementSourceAbsent
  | none, _ => .scored

/-- The witness: run 561c5ec3 pinned `A1-placements.tsv` at `30bceb18…`, the
file is unchanged, and the deployed replay did not annotate. -/
def click9b7d7f52 : Replay := ⟨some 30, some 30, deployedAnnotates⟩

/-! ## Theorems -/

/-- The witness refuses today and scores under the repair. -/
theorem witness_refuses_today_scores_repaired :
    currentReplay click9b7d7f52 = .refused ∧ repairedReplay click9b7d7f52 = .scored := by
  decide

/-- Clause 4: the repaired replay never refuses. -/
theorem repaired_never_refuses (r : Replay) : repairedReplay r ≠ .refused := by
  obtain ⟨p, c, a⟩ := r
  cases p with
  | none => cases c <;> simp [repairedReplay]
  | some p =>
    cases c with
    | none => simp [repairedReplay]
    | some c => by_cases h : p = c <;> simp [repairedReplay, h]

/-- Clause 1: with a pinned source, the repaired replay scores exactly when the
loaded source is the pinned one. -/
theorem repaired_scores_iff_same_source (p c : Sha) (a : Bool) :
    repairedReplay ⟨some p, some c, a⟩ = .scored ↔ p = c := by
  unfold repairedReplay
  by_cases h : p = c <;> simp [h]

/-- Clause 2: a changed source defers with its reason, whatever the annotation. -/
theorem changed_source_defers (p c : Sha) (a : Bool) (h : p ≠ c) :
    repairedReplay ⟨some p, some c, a⟩ = .deferred .placementSourceChanged := by
  simp [repairedReplay, h]

/-- Clause 2: a pinned source that cannot be loaded defers. -/
theorem absent_source_defers (p : Sha) (c : Option Sha) (a : Bool) :
    repairedReplay ⟨some p, none, a⟩ = .deferred .placementSourceAbsent ∧
      (c = none → repairedReplay ⟨some p, c, a⟩ ≠ .scored) := by
  constructor
  · rfl
  · intro hc; subst hc; simp [repairedReplay]

/-- Clause 3: a pending selection with no pinned source scores (typed absence). -/
theorem unpinned_scores (c : Option Sha) (a : Bool) :
    repairedReplay ⟨none, c, a⟩ = .scored := by
  cases c <;> rfl

/-- Control: the deployed replay refuses every un-annotated field, pinned or
not; annotation, not the pin, is what it lacked. -/
theorem deployed_refuses_unannotated (p c : Option Sha) :
    currentReplay ⟨p, c, false⟩ = .refused := rfl

/-- The repaired replay never scores a pinned source against a different one:
scoring implies the facts come from the pinned source or from the typed absence. -/
theorem scored_means_pinned_or_absent (r : Replay) (h : repairedReplay r = .scored) :
    r.pinned = none ∨ r.pinned = r.current := by
  obtain ⟨p, c, a⟩ := r
  cases p with
  | none => exact Or.inl rfl
  | some p =>
    cases c with
    | none => simp [repairedReplay] at h
    | some c =>
      by_cases hpc : p = c
      · exact Or.inr (by simp [hpc])
      · simp [repairedReplay, hpc] at h

#print axioms witness_refuses_today_scores_repaired
#print axioms repaired_never_refuses
#print axioms repaired_scores_iff_same_source
#print axioms changed_source_defers
#print axioms absent_source_defers
#print axioms unpinned_scores
#print axioms deployed_refuses_unannotated
#print axioms scored_means_pinned_or_absent

end DarkTower.WarMachine.PlacementReplay
