/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: claude-2
-/
import DarkTower.ExperimentPreregistration
import DarkTower.ExperimentalDesign

/-!
# E1 — Which retrieval arm actually delivers?

Preregistration for the first experiment of the V3 memory programme, written
**before the outcome statistic was computed**. The feasibility check
established only that the field exists and which two values it takes; the split
between them was deliberately not inspected, because that split *is* the
outcome.

## The question

A deployed agent-memory system retrieves by two arms: a lexical `content-match`
arm and a `pattern` arm that traverses a typed edge to a pattern endpoint and
returns the memories attached to it. A prior report (V2) established:

* term rarity does **not** predict retrieval failure (a U-curve; rare vs common
  `p = 0.618`);
* pairwise co-occurrence predicts it with the **wrong sign**
  (`p = 0.0172`, high co-occurrence → more empty);
* removing *either* arm changes the ordered top-five for every problem measured
  (n = 10) — both arms are ranking-critical.

Two lexical mechanisms therefore failed, and the surviving conjecture is that
the constraint lies not in matching text but in the **attachment layer**: that
"empty" means no *memories* surfaced rather than no *text* matched. This
experiment takes the first direct measurement bearing on that.

## Why this is registered rather than simply run

The corpus is frozen and the computation is cheap, which is exactly the
condition under which an unregistered analysis becomes a post-hoc fit. V2
recorded four preregistered expectations about mechanism and **three were
wrong**; that ratio was its most valuable property and is worth preserving by
construction.
-/

namespace DarkTower.MemoryArm

open ExperimentPreregistration

/-! ## The trace

One row per surfaced memory in the frozen corpus of 129 dispatch receipts.
`viaPattern` is read from `:memory-use/surfacing-via`, which records for each
surfaced memory whether it arrived by `:content-match` or by `:pattern`.
-/

/-- A single surfacing event, as recorded in an offered-phase receipt. -/
structure Surfacing where
  /-- Dispatch this memory surfaced in. -/
  dispatchId : String
  /-- The memory that surfaced. -/
  memoryId : String
  /-- True when `:via` was `:pattern`; false when `:content-match`. -/
  viaPattern : Bool
  deriving Repr

/-- The trace: every surfacing in the frozen corpus, plus the dispatches that
surfaced nothing at all. Empty dispatches are carried explicitly rather than
dropped, because a design that silently omits them cannot distinguish
"the pattern arm returned nothing" from "we did not look". -/
structure Trace where
  surfacings : List Surfacing
  /-- Dispatch ids whose recall returned no memories. -/
  emptyDispatches : List String
  /-- Dispatches that surfaced memories but carry NO arm attribution. These are
  the instrument's blind spot and must be counted, not dropped. -/
  unattributedNonEmpty : List String
  /-- Dispatch ids present in the corpus but lacking a recorded query, and so
  excluded from rates. Held as data so the denominator is auditable. -/
  unusable : List String
  /-- Total offered dispatches in the corpus, in time order. -/
  totalDispatches : Nat
  /-- Zero-based position, in time order, of the earliest dispatch carrying arm
  attribution. Retained for reporting; **not** the basis of the coverage
  observable — see `attributedSpanSeconds`. -/
  earliestAttributedIndex : Nat
  /-- Elapsed **nanoseconds** from the first to the last dispatch in the corpus.

  Nanoseconds rather than seconds because the two spans are truncated
  independently, and near the observable's boundary independent truncation can
  flip the verdict: real spans of 2.9 s and 1.0 s serialize as 2 and 1, so
  `2 ≤ 2 * 1` passes although `2.9 ≤ 2 * 1.0` is false. The receipts carry
  nanosecond-precision timestamps, so this unit is exact rather than merely
  finer, and the failure mode is removed rather than made unlikely. -/
  corpusSpanNanos : Nat
  /-- Elapsed seconds from the first ATTRIBUTED dispatch to the last dispatch.

  Coverage must be stated in elapsed time, not in ordinal position. The first
  version of this registration used the index, and on the real trace that
  index sits at 71 of 129 — comfortably inside the first two-thirds, so the
  check passed. The same trace covers **6.6% of elapsed time**: attribution
  began 6.9 hours before the end of a 105-hour corpus. Receipt density is
  heavily skewed toward the final days, so ordinal position and temporal
  coverage diverge by an order of magnitude, and the ordinal reading is the
  misleading one. In nanoseconds, per `corpusSpanNanos`. -/
  attributedSpanNanos : Nat
  deriving Repr

namespace Trace

/-- Surfacings attributed to the pattern arm. -/
def patternArm (t : Trace) : List Surfacing :=
  t.surfacings.filter (·.viaPattern)

/-- Surfacings attributed to the lexical content-match arm. -/
def contentArm (t : Trace) : List Surfacing :=
  t.surfacings.filter (fun s => ! s.viaPattern)

/-- Dispatches in which the pattern arm contributed at least one memory. -/
def dispatchesWithPattern (t : Trace) : List String :=
  (t.patternArm.map (·.dispatchId)).eraseDups

end Trace

/-! ## Observables

Each observable must inhabit `check_sound`: the check may never pass a trace
that violates the claim. This is the constraint that rules out a measurement
which cannot distinguish *absence* from *inability to ask* — the exact failure
V2 hit when a "discoverability" category scored zero because every receipt
field is closed over the offered set.
-/

/--
The corpus records arm attribution for every surfacing.

Without this the experiment is not merely underpowered but unaskable: an
unattributed surfacing is indistinguishable from one the instrument could not
classify.
-/
def attributionComplete : Observable Trace where
  name := "no dispatch surfaced memories without arm attribution"
  holds := fun t => t.unattributedNonEmpty = []
  check := fun t => t.unattributedNonEmpty.isEmpty
  check_sound := by
    intro t h
    simpa using List.isEmpty_iff.mp h

/--
**The attributed subset is not a recency tail — measured in elapsed time.**

The attributed window must span at least half the corpus's elapsed duration.
An instrument switched on late measures the period after it was switched on,
and a rate computed there cannot be read as a property of the corpus.

**This is the second version of this observable, and the first was wrong in an
instructive way.** It required the earliest attributed dispatch to sit within
the first two-thirds of the corpus *by ordinal position*. On the trace that
motivated the observable, that index is 71 of 129 — so the check **passed**,
on precisely the data it was written to reject. Attribution there begins 6.9
hours before the end of a 105-hour corpus: 6.6% of elapsed time. Dispatch
density is heavily skewed toward the final days, so ordinal rank and temporal
coverage diverge by an order of magnitude.

The first version was not vacuous — it could return `false`, and did so on a
constructed counter-trace. It measured the wrong *dimension*. `check_sound`
guarantees a check never passes a trace violating the stated claim; it cannot
tell you the claim is the wrong one. That distinction is worth stating, because
soundness is easy to mistake for adequacy.

A third revision changed the unit from seconds to nanoseconds: independently
truncated durations can flip this verdict at the boundary, which is a defect in
the instrument even where the margin makes it harmless. Three passes, three
defects, all of them in the instrument and none in the data.
-/
def coverageNotTail : Observable Trace where
  name := "attributed window spans at least half the corpus's elapsed duration"
  holds := fun t => t.corpusSpanNanos ≤ 2 * t.attributedSpanNanos
  check := fun t => decide (t.corpusSpanNanos ≤ 2 * t.attributedSpanNanos)
  check_sound := by intro t h; exact of_decide_eq_true h

/-! ## Arms

The comparison is between retrieval arms as they actually fired, not between
treatments we impose. The neutral arm is the content-match arm: it is the
lexical baseline whose two candidate mechanisms V2 already falsified, so it
functions as the empirical null against which any pattern-arm contribution must
be read.
-/

/-- The lexical arm: the empirical null. -/
def contentArm : Arm where
  name := "content-match (lexical)"
  neutral := true
  axes := []

/-- The pattern arm: traversal to a pattern endpoint and its attachments. -/
def patternArm : Arm where
  name := "pattern (attachment traversal)"
  neutral := false
  axes := []

/-! ## Stop rule -/

/--
Stop if the corpus cannot support the comparison at all.

`check_iff` rather than mere soundness: a checker that never fires would
otherwise satisfy the registration while permitting a run that can conclude
nothing.
-/
def insufficientCorpus : StopRule Trace where
  name := "fewer than 20 surfacings with arm attribution"
  fires := fun t => t.surfacings.length < 20
  check := fun t => decide (t.surfacings.length < 20)
  check_iff := by intro t; simp

/-! ## Outcome and decision rule

The decision rule is **total**: every trace the experiment can emit is
classified in advance. V2's load-bearing adjudication used a three-category
rubric that was not total, and five of forty-nine items fell through it — the
categories having been chosen under a substitutive model of memory use that the
same paper had already shown to be wrong. A total classification makes that
failure a type error rather than a discovery.
-/

/-- Pre-committed interpretations. `patternArmMarginal` is a live possibility,
not a hedge: it is what the attachment-layer conjecture predicts. -/
inductive Outcome
  /-- The pattern arm contributes a substantial share of surfacings. -/
  | patternArmSubstantial
  /-- The pattern arm fires, but marginally — consistent with the constraint
  lying in attachment coverage rather than in lexical matching. -/
  | patternArmMarginal
  /-- The pattern arm contributes nothing at all in the frozen corpus. -/
  | patternArmSilent
  /-- The corpus cannot support the comparison. -/
  | indeterminate
  deriving DecidableEq, Repr

/--
Thresholds fixed in advance: substantial at ≥ 25% of surfacings, silent at
exactly zero, marginal in between.

The boundary is declared here so that it cannot be chosen after the count is
known. It is not derived from theory; it is a commitment.
-/
def classify : Trace → Outcome := fun t =>
  if t.surfacings.length < 20 then Outcome.indeterminate
  else if t.patternArm.length = 0 then Outcome.patternArmSilent
  else if 4 * t.patternArm.length ≥ t.surfacings.length then
    Outcome.patternArmSubstantial
  else Outcome.patternArmMarginal

def decision : DecisionRule Trace Outcome where
  name := "pattern-arm share of surfacings, thresholds fixed pre-hoc"
  classify := classify

/-! ## Replication

Seeds are disjoint by construction. The computation over a frozen corpus is
deterministic, so replication here is not resampling but **re-derivation**: the
pilot seeds index an extraction of the trace from the receipts, and the
confirmation seeds index an independent re-extraction that must agree byte for
byte. This catches an extraction bug, which is the live failure mode when the
data cannot change.
-/
def replication : ReplicationPlan where
  pilotSeeds := [20260801]
  confirmationSeeds := [20260802]
  pilotNonempty := by decide
  confirmationNonempty := by decide
  disjoint := by simp

/-! ## The registration -/

def base : Registration Trace where
  name := "E1 — retrieval arm attribution in the frozen corpus"
  claim := ClaimForm.comparative
  arms := [contentArm, patternArm]
  flags := [⟨"no unattributed non-empty dispatch", attributionComplete⟩,
            ⟨"attributed subset is not a recency tail", coverageNotTail⟩]
  -- Frozen corpus, no dispatches, no runner tokens. The cost is one extraction
  -- pass over 129 receipts, measured from the comparable P1 extraction.
  estimatedCost := 0
  budgetCap := 0
  -- An offline analysis still has a teardown: the scratch extraction is
  -- deleted whether or not the run concludes anything. `none` was wrong — it
  -- left the registration unable to produce a `ReadyToRun` witness, because
  -- the facility generates a teardown obligation unconditionally. A zero-cost
  -- experiment is not an experiment without cleanup; it is one whose cleanup
  -- is cheap.
  teardownDeadline := some 3600

def registration : ProspectiveRegistration Trace Outcome where
  base := base
  replication := replication
  stopRules := [insufficientCorpus]
  stopRulesNonempty := by simp
  decision := decision

/-! ## What this experiment does not settle

Registered explicitly, so that a confirmatory result is not over-read.

* It measures the arm that surfaced each memory, **not** whether that memory
  was useful. Arm share is not a use rate and must not be reported as one.
* A marginal or silent pattern arm is *consistent with* the attachment-layer
  conjecture but does not establish it: attachment coverage is not measured
  here, only its downstream consequence.
* The corpus is one lane, one runner model, one domain, and one week.
* `surfacing-via` was itself empty on a minority of offered receipts. Those
  dispatches enter `unusable` and are excluded from rates; the exclusion is
  recorded in the trace rather than applied silently, because an unrecorded
  exclusion is how the four denominator failures of V2 happened.
-/

end DarkTower.MemoryArm
