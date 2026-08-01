/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: claude-2
-/
import DarkTower.ExperimentPreregistration
import DarkTower.ExperimentalDesign

/-!
# E2 — Does removing a memory change the outcome?

Preregistration for the ablation experiment of the V3 memory programme.

## The claim under test, and why it needs an experiment

A prior report (V2) adjudicated 49 recorded memory uses against a rubric fixed
in advance, judging 17 of them **load-bearing** — meaning that removing the
memory would have changed the outcome. That counterfactual was never run, and
could not be: a dispatch cannot be re-executed with a memory withheld. Every
verdict is therefore a judgement of plausible causal contribution read off the
runner's own prose, and the reported rate of 38% is an adjudication rather than
a measurement.

This experiment runs the counterfactual, and in doing so **tests the rubric
rather than any individual memory**. If ablating load-bearing memories changes
outcomes more often than ablating incidental ones, the adjudication is
validated as measurement. If it does not, the 38% is judgement only and must be
reported as such.

## Why closed problems

The subjects are problems the loop has already *solved*. This is not a
concession to availability but the better design:

* the outcome is **binary against a known-achievable target** — "did it close"
  — where an open problem leaves failure ambiguous between "the memory
  mattered" and "the problem is hard";
* the successful route is on record, so an ablation can be checked against what
  actually worked;
* re-running solved problems costs the live loop nothing, where reserving
  unsolved ones would sacrifice real progress.

## Why isolation is a validity requirement rather than hygiene

A git worktree at a pre-solution revision **still reaches the solution**: the
object database is shared, so `git log --all` shows the closing commit and
`git show <sha>:<path>` returns the solved file. These runners demonstrably do
search their repository — one closed a problem on a lemma found by grep. The
solution also appears outside the source tree, in three analysis artifacts that
describe the routes taken.

Isolation is therefore modelled below as `Flag`s carrying `Observable`s, so
that a run whose isolation was not demonstrated cannot be counted. This is the
structural form of the failure where a flag reaches a billing run without ever
taking effect.
-/

namespace DarkTower.MemoryAblation

open ExperimentPreregistration

/-! ## The trace -/

/-- Which arm a run belongs to. -/
inductive ArmKind
  /-- Full corpus. Establishes the same-corpus disagreement rate. -/
  | control
  /-- A memory adjudicated load-bearing was withheld. -/
  | ablateLoadBearing
  /-- A memory adjudicated incidental was withheld. -/
  | ablateIncidental
  /-- A memory the structured field dropped but the runner's prose reported
  using was withheld. Tests whether that field's failure is *biased* toward
  the consequential, not merely lossy. -/
  | ablateProseOnly
  deriving DecidableEq, Repr

/--
One dispatch of one problem under one arm.

`withheldPresent` records whether the memory that was supposed to be withheld
nevertheless appeared in the surfaced set. It is carried as *evidence*, not as
an assumption, because an ablation that silently failed to ablate would
otherwise be indistinguishable from a null result.
-/
structure Run where
  problemId : String
  arm : ArmKind
  /-- Distinct per run: no conversational continuity between repeats. -/
  sessionId : String
  /-- The pre-solution revision the working tree was reset to. -/
  baseRevision : String
  /-- **The dependent variable: attempts required to close.**

  Not closure itself. On a sample the loop has driven to 100% solved, closure
  has no variance and a binary outcome hits a ceiling — the ablation could
  show nothing. Effort does have variance, and it is the quantity a memory
  plausibly moves.

  This is also the only dependent variable that can see the *majority* of
  observed memory use. Five of seven catalogued use-modes are regulative
  rather than substitutive: they change what the runner does, or stops doing,
  without supplying mathematics. A stopping rule or a route override should
  reduce **attempts**, not decide **closure**. A binary DV is blind to
  precisely the modes that dominate. -/
  attemptsToClose : Nat
  /-- Ceiling check, retained so a non-closing run is not silently scored as
  high effort. -/
  closed : Bool
  /-- Secondary, retained for sensitivity: sorries remaining. -/
  sorriesRemaining : Nat
  /-- Secondary: distinct proof routes attempted before the successful one.
  A route override should move this where it does not move attempts. -/
  distinctRoutesTried : Nat
  /-- Memory id withheld, if any. -/
  withheldMemory : Option String
  /-- True if the withheld memory appeared in the surfaced set anyway. -/
  withheldPresent : Bool
  deriving Repr

/--
The result of probing whether the isolated account could reach the answer.

Each field records the outcome of an *attempted* read. An attestation that the
runner "was isolated" would be a claim; these are probe results.
-/
structure IsolationProbe where
  /-- Attempted read of the operator home directory; must have been denied. -/
  homeReadDenied : Bool
  /-- `git log --all` in the runner's checkout reached no commit later than the
  pinned base revision. -/
  noFutureCommits : Bool
  /-- No analysis artifact describing the routes was readable. -/
  noAnalysisArtifacts : Bool
  /-- The Codex-side persistent store was not reachable. -/
  noRunnerSideStore : Bool
  deriving Repr

/-- The trace: every run, plus the isolation evidence for the account they ran
in, plus runs discarded before analysis and why. -/
structure Trace where
  runs : List Run
  isolation : IsolationProbe
  /-- Discarded runs, held as data so the denominator stays auditable. -/
  discarded : List Run
  deriving Repr

namespace Trace

def controlRuns (t : Trace) : List Run := t.runs.filter (·.arm = ArmKind.control)

def armRuns (t : Trace) (k : ArmKind) : List Run := t.runs.filter (·.arm = k)

/-- Runs that closed, within an arm. -/
def closedIn (t : Trace) (k : ArmKind) : List Run :=
  (t.armRuns k).filter (·.closed)

/-- An arm's failure count: runs that did not close. Retained as a ceiling
check, not as the dependent variable. -/
def notClosedIn (t : Trace) (k : ArmKind) : Nat :=
  ((t.armRuns k).filter (fun r => ! r.closed)).length

/-- **Total attempts across an arm — the dependent variable.** -/
def attemptsIn (t : Trace) (k : ArmKind) : Nat :=
  ((t.armRuns k).map (·.attemptsToClose)).sum

end Trace

/-! ## Observables

Every observable here is checked against recorded probe evidence rather than
against an assertion. `check_sound` then holds definitionally, and the honest
residue — that the probes must themselves be trustworthy — is stated in the
closing section rather than hidden inside a tautology.
-/

/-- The isolated account could not read the operator's home directory. -/
def homeUnreadable : Observable Trace where
  name := "probe: operator home directory read was denied"
  holds := fun t => t.isolation.homeReadDenied = true
  check := fun t => t.isolation.homeReadDenied
  check_sound := by intro t h; exact h

/-- The runner's checkout contained no commit after the pinned base revision,
so the solution was not reachable through the object database. -/
def historyTruncated : Observable Trace where
  name := "probe: no commit later than the pinned base revision is reachable"
  holds := fun t => t.isolation.noFutureCommits = true
  check := fun t => t.isolation.noFutureCommits
  check_sound := by intro t h; exact h

/-- No analysis artifact describing the successful routes was readable. -/
def artifactsUnreachable : Observable Trace where
  name := "probe: route-describing analysis artifacts unreadable"
  holds := fun t => t.isolation.noAnalysisArtifacts = true
  check := fun t => t.isolation.noAnalysisArtifacts
  check_sound := by intro t h; exact h

/-- The runner-side persistent store was not reachable. -/
def runnerStoreUnreachable : Observable Trace where
  name := "probe: runner-side persistent store unreachable"
  holds := fun t => t.isolation.noRunnerSideStore = true
  check := fun t => t.isolation.noRunnerSideStore
  check_sound := by intro t h; exact h

/--
**The ablation flag actually ablated.**

No run in the trace shows the withheld memory present in its surfaced set. A
flag whose observable is not declared is a type error here; this is the
observable that makes the ablation flag mean something.
-/
def ablationTookEffect : Observable Trace where
  name := "no run surfaced the memory it was supposed to withhold"
  holds := fun t => ∀ r ∈ t.runs, r.withheldPresent = false
  check := fun t => t.runs.all (fun r => ! r.withheldPresent)
  check_sound := by
    intro t h r hr
    have := List.all_eq_true.mp h r hr
    simpa using this

/-! ## Arms -/

def controlArm : Arm where
  name := "control — full corpus, closed problem re-run"
  neutral := true
  axes := []

def lbArm : Arm where
  name := "ablate load-bearing"
  neutral := false
  axes := []

def inArm : Arm where
  name := "ablate incidental"
  neutral := false
  axes := []

def proseOnlyArm : Arm where
  name := "ablate prose-only (dropped by the structured field)"
  neutral := false
  axes := []

/-! ## Stop rules

The first is the one that matters. An ablation difference is uninterpretable
without knowing how often *identical* runs disagree, so the control arm is the
pilot and a high floor stops the experiment rather than being explained away.
-/

/--
Stop if same-corpus repeats disagree too often for an effect to be readable.

Fires when more than a quarter of control runs failed to close a problem that
is known to close.
-/
def noiseFloorTooHigh : StopRule Trace where
  name := "control arm fails to close in > 25% of runs"
  fires := fun t => 4 * (t.notClosedIn ArmKind.control) > (t.armRuns ArmKind.control).length
  check := fun t =>
    decide (4 * (t.notClosedIn ArmKind.control) > (t.armRuns ArmKind.control).length)
  check_iff := by intro t; simp

/-- Stop if the ablation did not take effect in some run. -/
def ablationLeaked : StopRule Trace where
  name := "a withheld memory surfaced anyway"
  fires := fun t => ∃ r ∈ t.runs, r.withheldPresent = true
  check := fun t => t.runs.any (·.withheldPresent)
  check_iff := by
    intro t
    constructor
    · intro h
      obtain ⟨r, hr, hp⟩ := List.any_eq_true.mp h
      exact ⟨r, hr, by simpa using hp⟩
    · rintro ⟨r, hr, hp⟩
      exact List.any_eq_true.mpr ⟨r, hr, by simpa using hp⟩

/-! ## Outcome and decision rule

Total by construction. The categories are chosen so that the *uninteresting*
results have names: an experiment whose only articulated outcome is its
hypothesis has not been designed.
-/

inductive Outcome
  /-- Load-bearing ablations break closure more than incidental ones. The
  adjudication rubric is validated as measurement. -/
  | rubricValidated
  /-- Neither ablation arm departs from the control floor. The 38% is
  judgement only and must be reported as such. -/
  | rubricUnsupported
  /-- Both arms depart from the floor. The experiment is measuring
  perturbation sensitivity rather than load-bearingness, and the design needs
  revisiting before any rubric claim. -/
  | anyAblationBreaks
  /-- The floor was too high, the ablation leaked, or isolation failed. -/
  | indeterminate
  deriving DecidableEq, Repr

/--
Classification, with thresholds fixed before any run.

A departure counts when an arm's non-closure count exceeds the control arm's by
at least two runs; the LB/IN separation counts when load-bearing exceeds
incidental by at least two. These are commitments, not derivations, and are
stated numerically so they cannot be adjusted after the counts are known.
-/
def classify : Trace → Outcome := fun t =>
  -- Effort, not closure. Thresholds are on TOTAL ATTEMPTS per arm: an arm
  -- departs when it needs at least 3 more attempts than control across the
  -- arm, and the LB/IN separation needs a further 3. Fixed here so they
  -- cannot be adjusted once the counts are known.
  let ctrl := t.attemptsIn ArmKind.control
  let lb := t.attemptsIn ArmKind.ablateLoadBearing
  let inc := t.attemptsIn ArmKind.ablateIncidental
  if 4 * (t.notClosedIn ArmKind.control) > (t.armRuns ArmKind.control).length then
    Outcome.indeterminate
  else if t.runs.any (·.withheldPresent) then Outcome.indeterminate
  else if ! (t.isolation.homeReadDenied && t.isolation.noFutureCommits
             && t.isolation.noAnalysisArtifacts && t.isolation.noRunnerSideStore) then
    Outcome.indeterminate
  else if lb ≥ ctrl + 3 && inc ≥ ctrl + 3 then Outcome.anyAblationBreaks
  else if lb ≥ ctrl + 3 && lb ≥ inc + 3 then Outcome.rubricValidated
  else Outcome.rubricUnsupported

def decision : DecisionRule Trace Outcome where
  name := "arm-wise non-closure against the control floor, thresholds fixed pre-hoc"
  classify := classify

/-! ## Replication

The pilot **is** the noise floor: control-arm repeats, inspected before any
ablation arm is run. The confirmation seeds index the ablation arms. They are
disjoint by construction, which is what prevents the floor from being
re-estimated after the effect is seen.
-/
def replication : ReplicationPlan where
  pilotSeeds := [20260801, 20260802, 20260803]
  confirmationSeeds := [20260811, 20260812, 20260813]
  pilotNonempty := by decide
  confirmationNonempty := by decide
  disjoint := by simp

/-! ## The registration -/

def base : Registration Trace where
  name := "E2 — memory ablation on closed problems in an isolated account"
  claim := ClaimForm.comparative
  arms := [controlArm, lbArm, inArm, proseOnlyArm]
  flags :=
    [⟨"isolated account cannot read operator home", homeUnreadable⟩,
     ⟨"history truncated at base revision", historyTruncated⟩,
     ⟨"analysis artifacts unreachable", artifactsUnreachable⟩,
     ⟨"runner-side store unreachable", runnerStoreUnreachable⟩,
     ⟨"ablation took effect", ablationTookEffect⟩]
  -- From a measured rate: ~20-35k runner tokens per dispatch, observed on a
  -- comparable design. 6-8 problems x 4 arms x 3 repeats, with the control
  -- arm run first as the pilot. The multiplier is included: an estimate
  -- counting only the ablation arms would be wrong by a factor of four.
  estimatedCost := 1400000
  budgetCap := 2000000
  -- Teardown of the isolated account is scheduled independently of the run
  -- succeeding, so a failed experiment does not leave a live second account.
  teardownDeadline := some 1400000

def registration : ProspectiveRegistration Trace Outcome where
  base := base
  replication := replication
  stopRules := [noiseFloorTooHigh, ablationLeaked]
  stopRulesNonempty := by simp
  decision := decision

/-! ## What this experiment does not settle, and one honest residue

* **It tests the rubric, not the memories.** A `rubricValidated` outcome
  licenses reporting the 38% as a measured rate; it does not establish that any
  *particular* memory was necessary.
* **`anyAblationBreaks` is a real possibility**, and would mean the design
  measures sensitivity to perturbation as such. It is named so that it cannot
  be discovered and then narrated as something else.
* **The isolation observables check probe results, not the world.** If a probe
  is wrong, the observable passes. Their trustworthiness is an obligation on
  the harness, discharged by having the probes attempt reads that *must* fail
  and recording the failure — not by attestation. This is the weakest joint in
  the design and is stated rather than hidden.
* **The selection worry does not apply to this sample, but a subtler one
  does.** The first quarter of the problem set is being driven to 100% solved,
  so within it there is no solved/unsolved selection effect. What remains is
  that these are the problems *this* loop, with *this* corpus, could solve —
  and the effort recorded for them is effort under memory conditions we are
  now perturbing. That is the point of the experiment, but it means the
  attempt counts are not a neutral difficulty scale.
* **Effort is measured, meta-level reasoning is not.** `attemptsToClose`
  records how much elbow grease a problem took; it says nothing about the
  meta-level thinking that produced the successful route. A corpus that
  records *which problems were solved* — even with effort attached — still does
  not capture *how the solving was steered*. That gap is not addressed here
  and is the subject of a separate experiment (E7).
* One lane, one runner model, one domain.
-/

end DarkTower.MemoryAblation
