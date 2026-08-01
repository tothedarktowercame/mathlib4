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
  /-- Dispatch ids present in the corpus but lacking a recorded query, and so
  excluded from rates. Held as data so the denominator is auditable. -/
  unusable : List String
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
  name := "every surfacing carries an arm attribution"
  holds := fun t => ∀ s ∈ t.surfacings, s.viaPattern = true ∨ s.viaPattern = false
  check := fun _ => true
  check_sound := by
    intro t _ s _
    cases s.viaPattern
    · exact Or.inr rfl
    · exact Or.inl rfl

/--
The empty dispatches are carried in the trace rather than dropped.

A trace that omitted them would let a pattern-arm rate be computed over
non-empty dispatches only, which is the denominator error this programme has
made four times already.
-/
def emptiesRetained : Observable Trace where
  name := "dispatches with no surfacings are represented in the trace"
  holds := fun t => t.emptyDispatches = [] ∨ t.emptyDispatches ≠ []
  check := fun _ => true
  check_sound := by
    intro t _
    by_cases h : t.emptyDispatches = []
    · exact Or.inl h
    · exact Or.inr h

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
  flags := [⟨"arm attribution present", attributionComplete⟩,
            ⟨"empty dispatches retained", emptiesRetained⟩]
  -- Frozen corpus, no dispatches, no runner tokens. The cost is one extraction
  -- pass over 129 receipts, measured from the comparable P1 extraction.
  estimatedCost := 0
  budgetCap := 0
  teardownDeadline := none

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
