/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: claude-2
-/
import DarkTower.ExperimentPreregistration
import DarkTower.ExperimentalDesign
import Mathlib.Data.Nat.Choose.Basic

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
  /-- Replication seed. Pairing is per (problem, seed): comparing a
  load-bearing run at seed 1 against a control run at seed 2 is not a paired
  comparison, and problem-level pairing alone permits exactly that. -/
  seed : Nat
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

/-- One panel row: a problem, and the two memory ids to be withheld from it.

Both ids are fixed in the registration rather than chosen at dispatch time,
which is what makes "the load-bearing arm withheld the load-bearing memory" a
checkable claim instead of a description of intent. -/
structure PanelEntry where
  problem : String
  /-- The last revision before the problem's solution became reachable. -/
  baseRevision : String
  /-- The memory adjudicated load-bearing for this problem. -/
  lbMemory : String
  /-- The memory adjudicated incidental for this problem. -/
  incMemory : String
  deriving DecidableEq, Repr

/-- The trace: every run, plus the isolation evidence for the account they ran
in, plus runs discarded before analysis and why. -/
structure Trace where
  runs : List Run
  /-- The preregistered panel. Authoritative: the expected observation set is
  `panel × arms × seeds`, and runs outside it are a protocol violation rather
  than data to discard. Fixing it in the registration is what stops selection
  after inspecting candidates from dominating the result.

  Each entry binds a problem to **the two specific memory ids** that will be
  withheld from it. Without that binding the registration cannot tell whether
  anything was ablated at all: a trace with every `withheldMemory = none`
  satisfied `ablationTookEffect` and reached `rubricValidated`, because that
  observable only ever asked whether an *allegedly* withheld memory had
  surfaced. An ablation experiment that validates the rubric while ablating
  nothing is the worst failure available to this design. -/
  panel : List PanelEntry
  /-- The preregistered replication seeds. -/
  seeds : List Nat
  isolation : IsolationProbe
  /-- Discarded runs, held as data so the denominator stays auditable. -/
  discarded : List Run
  deriving Repr

/-- The arms this experiment actually compares.

**`ablateProseOnly` is deliberately absent.** It was registered, budgeted at a
quarter of the run, and never read by the decision rule — the "flag that never
takes effect" failure, committed in an arm where the facility does not guard.
The honest fix is not to invent a decision role for it: it tests a *different*
claim (that the structured use-field drops consequential uses preferentially),
and smuggling a second, underpowered hypothesis into a rubric-validation run is
how side-findings get reported as results. The constructor remains so that
historical traces still parse; the arm is banked for a separately powered
experiment. -/
def measuredArms : List ArmKind :=
  [ArmKind.control, ArmKind.ablateLoadBearing, ArmKind.ablateIncidental]

/-- One seed's paired contrast: which arm needed more attempts, or neither.

Three-way, not Boolean. `lbHarderThanIncAt` returned `some (a > b)`, so EQUAL
attempts became `some false` — an incidental *win* rather than a tie. A problem
where the two arms performed identically on every seed was therefore scored as
a clean win for incidental, biasing the test against the hypothesis it was
built to examine. A tie is the absence of a difference and must be excluded
from `n`, not counted against a side. -/
inductive SeedResult
  | firstHarder
  | tie
  | secondHarder
  deriving DecidableEq, Repr

/-- What a (problem, seed, arm) cell contains.

Three states, not two. `find?` takes the first match and ignores the rest,
which makes a duplicated cell **order-dependent**: the same two runs emitted as
`[20, 1]` and `[1, 20]` classified as `some true` and `some false` respectively.
Duplicates are a protocol violation and must be detected, not averaged away —
and kept diagnostically distinct from absence, since they have different
causes and different fixes even though both force `indeterminate`. -/
inductive CellStatus
  | missing
  | unique (attempts : Nat)
  | duplicate
  deriving DecidableEq, Repr

/-- Exact one-sided sign test at p ≤ 0.05, in `Nat` arithmetic.

`k` successes out of `n` non-tied pairs passes when the binomial tail
`P(X ≥ k | p = ½)` is at most one twentieth. Stated as `20 * tail ≤ 2^n` so
there is no division and therefore no truncation — the defect that flipped a
verdict in the companion experiment. A fixed `+3` threshold was the previous
rule and is not a test at all; this one has a stated error rate. -/
def binomTail (n k : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun i => k ≤ i)).foldl
    (fun acc i => acc + Nat.choose n i) 0

/-- The `k ≤ n` guard is not defensive tidiness — without it the test passes on
malformed input. When `k > n` the tail sum ranges over nothing and evaluates to
`0`, so `20 * 0 ≤ 2 ^ n` holds and `signTestPasses 12 13` returns `true`:
more successes than trials reported as a significant result.

That is the same failure as an empty trace reaching a verdict, a missing cell
reading as "not harder", and a probe counting an unauthenticated `sudo` as a
clean pass — **an absent quantity acting as evidence**. Fifth occurrence in
this programme, and the first inside a statistical test. -/
def signTestPasses (n k : Nat) : Bool :=
  decide (k ≤ n) && decide (20 * binomTail n k ≤ 2 ^ n)


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

/-- Total attempts across an arm. **Retained for reporting only.** It was the
dependent variable and must not be: every arm runs the same problems, so the
design is paired, and summing discards the pairing. A counterexample with every
run at exactly one attempt but four load-bearing rows against one control row
classified as `rubricValidated` — nothing had become harder, only the arm
cardinality had changed. -/
def attemptsIn (t : Trace) (k : ArmKind) : Nat :=
  ((t.armRuns k).map (·.attemptsToClose)).sum

/-- Runs of one problem under one arm. -/
def cell (t : Trace) (p : String) (k : ArmKind) : List Run :=
  t.runs.filter (fun r => r.problemId = p && r.arm = k)

/-- Attempts summed within a cell, and the cell's size, kept **separate**.

Deliberately not a mean: dividing here would truncate, and independent
truncation of two quantities compared near a threshold is exactly the defect
that flipped a verdict in the companion experiment. Comparisons below
cross-multiply instead. -/
def cellAttempts (t : Trace) (p : String) (k : ArmKind) : Nat × Nat :=
  let rs := t.cell p k
  ((rs.map (·.attemptsToClose)).sum, rs.length)

/-- Attempts for one exact (problem, seed, arm) triple, or `none` if that cell
was never run.

`Option`, not a default: a missing cell is **absent data**, and scoring it as a
number would let absence act as evidence. That failure has recurred through
this programme — an empty trace reaching a substantive verdict, a discoverability
category scoring zero because the channel could not represent it, a probe
counting an unauthenticated `sudo` as a clean pass. -/
def cellAt (t : Trace) (p : String) (s : Nat) (k : ArmKind) : CellStatus :=
  match t.runs.filter (fun r => r.problemId = p && r.seed = s && r.arm = k) with
  | []      => CellStatus.missing
  | [r]     => CellStatus.unique r.attemptsToClose
  | _ :: _  => CellStatus.duplicate

/-- Is arm `k` harder than control on this exact (problem, seed) pair?

`none` when either cell is missing — **not** `false`. codex-1's finding: with a
Bool, a missing cell reads as "not harder", which is negative evidence drawn
from no observation at all. Seed-level pairing rather than problem-level,
because comparing LB-seed-1 against control-seed-2 is not a paired comparison. -/
def harderAt (t : Trace) (p : String) (s : Nat) (k : ArmKind) : Option Bool :=
  match t.cellAt p s k, t.cellAt p s ArmKind.control with
  | CellStatus.unique a, CellStatus.unique c => some (a > c)
  | _, _                                     => none

/-- **Load-bearing against incidental, on the same (problem, seed).**

codex-1's improvement, adopted. Comparing *counts* of LB-vs-control against
IN-vs-control compares two summaries; comparing LB against IN on the *same*
pair is a genuine paired contrast and strictly more powerful. It is also
closer to the claim, which is about the rubric's ability to separate the two
categories, not about either category's relation to control. -/
def seedResult (t : Trace) (p : String) (s : Nat) : Option SeedResult :=
  match t.cellAt p s ArmKind.ablateLoadBearing,
        t.cellAt p s ArmKind.ablateIncidental with
  | CellStatus.unique a, CellStatus.unique b =>
      some (if a > b then SeedResult.firstHarder
            else if b > a then SeedResult.secondHarder
            else SeedResult.tie)
  | _, _ => none

/-- Every (problem, seed) pair the registration commits to observing. -/
def expectedPairs (t : Trace) : List (String × Nat) :=
  t.panel.flatMap (fun e => t.seeds.map (fun s => (e.problem, s)))

/-- Pairs on which an arm needed more attempts than control. Counted over
pairs, never over runs, so cardinality cannot manufacture a difference. -/
def pairsHarderUnder (t : Trace) (k : ArmKind) : Nat :=
  ((t.expectedPairs.map (fun (p, s) => t.harderAt p s k)).filter
    (fun o => o = some true)).length

/-- Pairs where the comparison could not be made because a cell is missing.
Any of these must force `indeterminate`. -/
def incompletePairs (t : Trace) (k : ArmKind) : Nat :=
  ((t.expectedPairs.map (fun (p, s) => t.harderAt p s k)).filter
    (fun o => o = none)).length

/-! ### The unit of analysis is the PROBLEM, not the (problem, seed) pair

Seeds are repeats *within* a problem, not independent observations of the
rubric. Running a sign test over 18 seed-level pairs would treat three repeats
of one problem as three independent facts about whether the adjudication
separates load-bearing from incidental memories — **pseudoreplication**, and it
would have inflated `n` threefold and made a null look significant.

So the seed-level contrasts are aggregated to one sign per problem, and the
test runs over problems. The resulting critical values are severe and honest:
at six problems, load-bearing must beat incidental on **all six**.

| problems (non-tied) | required wins |
|---|---|
| 6 | 6 |
| 7 | 7 |
| 8 | 7 |
-/

/-- Per-problem sign of an arm against CONTROL, three-way like `seedResult`. -/
def signVsControl (t : Trace) (p : String) (k : ArmKind) : Option Bool :=
  let votes := t.seeds.filterMap (fun s =>
    match t.cellAt p s k, t.cellAt p s ArmKind.control with
    | CellStatus.unique a, CellStatus.unique c =>
        some (if a > c then SeedResult.firstHarder
              else if c > a then SeedResult.secondHarder
              else SeedResult.tie)
    | _, _ => none)
  let up := (votes.filter (· = SeedResult.firstHarder)).length
  let dn := (votes.filter (· = SeedResult.secondHarder)).length
  if up ≥ 2 then some true else if dn ≥ 2 then some false else none

/-- Non-tied problems for an arm-vs-control comparison. -/
def nonTiedVs (t : Trace) (k : ArmKind) : Nat :=
  (t.panel.filterMap (fun e => t.signVsControl e.problem k)).length

/-- Problems where the arm cost more attempts than control. -/
def winsVs (t : Trace) (k : ArmKind) : Nat :=
  ((t.panel.filterMap (fun e => t.signVsControl e.problem k)).filter id).length

/-- One problem's verdict: the majority direction of its seed-level contrasts.

`none` when the seeds split evenly or no contrast could be formed — a tie, to be
excluded from `n` rather than counted against either side. -/
def problemSign (t : Trace) (p : String) : Option Bool :=
  let votes := t.seeds.filterMap (fun s => t.seedResult p s)
  let lb := (votes.filter (· = SeedResult.firstHarder)).length
  let inc := (votes.filter (· = SeedResult.secondHarder)).length
  if lb ≥ 2 then some true
  else if inc ≥ 2 then some false
  else none

/-- Problems with a resolved direction — the sign test's `n`. -/
def nonTiedProblems (t : Trace) : Nat :=
  (t.panel.filterMap (fun e => t.problemSign e.problem)).length

/-- Problems where load-bearing ablation cost more attempts than incidental —
the sign test's `k`. -/
def lbWinsProblems (t : Trace) : Nat :=
  ((t.panel.filterMap (fun e => t.problemSign e.problem)).filter id).length


end Trace

/-! ## Observables

Every observable here is checked against recorded probe evidence rather than
against an assertion. `check_sound` then holds definitionally, and the honest
residue — that the probes must themselves be trustworthy — is stated in the
closing section rather than hidden inside a tautology.
-/

/--
**The expectation set is not vacuous.**

Panel and seeds must both be non-empty and duplicate-free. Without this, the
completeness guard passes trivially: an empty panel yields no expected pairs,
so nothing is missing, so the experiment reports a clean comparison over no
observations at all. codex-1 raised this while validating the pairing fix —
a guard that ranges over a set you control is only as strong as the set.

Duplicate-free because `panel × seeds` is generated by `flatMap`, so a repeated
entry silently doubles the weight of one problem in a statistic that counts
pairs.

And `lbMemory ≠ incMemory` per entry, because nothing else prevents both
ablation arms being registered to withhold the *same* memory. The withholding
check would accept that happily, and the experiment would then issue a
substantive comparison between two labels for one intervention — a difference
that could only ever be noise, reported as a rubric verdict.
-/
def expectationWellFormed : Observable Trace where
  name := "panel and seeds are non-empty and duplicate-free"
  holds := fun t =>
    t.panel ≠ [] ∧ t.seeds ≠ [] ∧ (t.panel.map (·.problem)).Nodup ∧ t.seeds.Nodup
      ∧ ∀ e ∈ t.panel, e.lbMemory ≠ e.incMemory
  check := fun t =>
    !t.panel.isEmpty && !t.seeds.isEmpty
      && decide (t.panel.map (·.problem)).Nodup && decide t.seeds.Nodup
      && t.panel.all (fun e => e.lbMemory != e.incMemory)
  check_sound := by
    intro t h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨fun e => by simp [e] at h1,
            fun e => by simp [e] at h2,
            of_decide_eq_true h3,
            of_decide_eq_true h4, ?_⟩
    intro e he
    have := List.all_eq_true.mp h5 e he
    simpa using this

/--
**Each run withheld exactly what the registration said it would.**

`ablationTookEffect` asks only whether an allegedly withheld memory surfaced. It
is satisfied by a trace in which nothing was withheld — every `withheldMemory`
`none`, every `withheldPresent` false — which then reached `rubricValidated`.
That is an ablation study validating a rubric without performing an ablation.

This observable closes it by binding each arm to the panel: control withholds
nothing, and each ablation arm withholds precisely the id registered for that
problem and no other.
-/
def withholdingAsRegistered : Observable Trace where
  name := "each run withheld exactly the registered memory for its arm"
  holds := fun t => ∀ r ∈ t.runs, ∀ e ∈ t.panel, r.problemId = e.problem →
    (r.arm = ArmKind.control → r.withheldMemory = none) ∧
    (r.arm = ArmKind.ablateLoadBearing → r.withheldMemory = some e.lbMemory) ∧
    (r.arm = ArmKind.ablateIncidental → r.withheldMemory = some e.incMemory)
  check := fun t => t.runs.all fun r => t.panel.all fun e =>
    !(r.problemId == e.problem) ||
      (match r.arm with
       | ArmKind.control           => r.withheldMemory == none
       | ArmKind.ablateLoadBearing => r.withheldMemory == some e.lbMemory
       | ArmKind.ablateIncidental  => r.withheldMemory == some e.incMemory
       | ArmKind.ablateProseOnly   => false)
  check_sound := by
    intro t h r hr e he hpe
    have h1 := List.all_eq_true.mp h r hr
    have h2 := List.all_eq_true.mp h1 e he
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h2
    rcases h2 with hne | harm
    · exact absurd hpe (by simpa using hne)
    · refine ⟨?_, ?_, ?_⟩
      · intro hc; rw [hc] at harm; simpa using harm
      · intro hl; rw [hl] at harm; simpa using harm
      · intro hi; rw [hi] at harm; simpa using harm

/-- Every run used the pre-solution revision bound to its panel entry.

`Run.baseRevision` was the third field whose promised semantics previously
existed only in prose.  A trace in which every run used a post-solution
revision could reach `rubricValidated`; binding the revision into `PanelEntry`
and checking it here makes that trace invalid data rather than an easy proof. -/
def revisionsAsRegistered : Observable Trace where
  name := "each run used the registered pre-solution revision"
  holds := fun t => ∀ r ∈ t.runs, ∀ e ∈ t.panel,
    r.problemId = e.problem → r.baseRevision = e.baseRevision
  check := fun t => t.runs.all fun r => t.panel.all fun e =>
    !(r.problemId == e.problem) || r.baseRevision == e.baseRevision
  check_sound := by
    intro t h r hr e he hpe
    have h1 := List.all_eq_true.mp h r hr
    have h2 := List.all_eq_true.mp h1 e he
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h2
    rcases h2 with hne | hrev
    · exact absurd hpe (by simpa using hne)
    · simpa using hrev

/--
**No two runs shared a session.**

`Run.sessionId` is documented as distinct per run, so that repeats carry no
conversational continuity — an agent that remembers its earlier attempt is not
an independent replicate, and would make the noise floor an underestimate.
Nothing checked it. A trace with every run set to one shared session still
reached `rubricValidated`, which permits exactly the continuity the field
exists to exclude, across the control and ablation arms alike.

The eighth defect found in this registration, and the second of its kind: an
invariant stated in a docstring and enforced nowhere. A comment is not a
constraint.
-/
def sessionsDistinct : Observable Trace where
  name := "no two runs shared a session"
  holds := fun t => (t.runs.map (·.sessionId)).Nodup
  check := fun t => decide (t.runs.map (·.sessionId)).Nodup
  check_sound := by intro t h; exact of_decide_eq_true h

/-! ### Completeness — three observables, not one

Runs must agree exactly with `panel × arms × seeds`. Expressed as three checks
rather than one multiset equality, confirmed by codex-1: jointly they are
equivalent to exact agreement, while separately they preserve an actionable
diagnosis. A single equality failure says only "the panel does not match"; these
say *which*, and the three have different causes and different fixes.

- an **omission** means a run was lost or never dispatched;
- an **extra** means something ran that was never registered — the selection
  hazard the panel exists to prevent;
- a **duplicate** means the harness emitted one cell twice, which is the
  order-dependence defect that made `find?` unusable.
-/

/-- Every expected cell was observed. -/
def noOmissions : Observable Trace where
  name := "every expected (problem, seed, arm) cell is present"
  holds := fun t => ∀ e ∈ t.panel, ∀ s ∈ t.seeds, ∀ k ∈ measuredArms,
    t.cellAt e.problem s k ≠ CellStatus.missing
  check := fun t =>
    t.panel.all fun e => t.seeds.all fun s => measuredArms.all fun k =>
      t.cellAt e.problem s k != CellStatus.missing
  check_sound := by
    intro t h p hp s hs k hk
    have h1 := List.all_eq_true.mp h p hp
    have h2 := List.all_eq_true.mp h1 s hs
    have h3 := List.all_eq_true.mp h2 k hk
    simpa using h3

/-- No expected cell was observed more than once. -/
def noDuplicates : Observable Trace where
  name := "no expected cell was observed twice"
  holds := fun t => ∀ e ∈ t.panel, ∀ s ∈ t.seeds, ∀ k ∈ measuredArms,
    t.cellAt e.problem s k ≠ CellStatus.duplicate
  check := fun t =>
    t.panel.all fun e => t.seeds.all fun s => measuredArms.all fun k =>
      t.cellAt e.problem s k != CellStatus.duplicate
  check_sound := by
    intro t h p hp s hs k hk
    have h1 := List.all_eq_true.mp h p hp
    have h2 := List.all_eq_true.mp h1 s hs
    have h3 := List.all_eq_true.mp h2 k hk
    simpa using h3

/-- No run lies outside the preregistered expectation set.

This is what makes the panel *authoritative* rather than advisory. Without it a
run on an unregistered problem is simply data; with it, that run is a protocol
violation — which is what prevents selection after inspecting candidates from
reaching the result. -/
def noExtras : Observable Trace where
  name := "no run falls outside panel × seeds × arms"
  holds := fun t => ∀ r ∈ t.runs,
    r.problemId ∈ t.panel.map (·.problem) ∧ r.seed ∈ t.seeds ∧ r.arm ∈ measuredArms
  check := fun t =>
    t.runs.all fun r =>
      (t.panel.map (·.problem)).contains r.problemId && t.seeds.contains r.seed
        && measuredArms.contains r.arm
  check_sound := by
    intro t h r hr
    have hr' := List.all_eq_true.mp h r hr
    simp only [Bool.and_eq_true] at hr'
    obtain ⟨⟨h1, h2⟩, h3⟩ := hr'
    exact ⟨List.mem_of_elem_eq_true h1,
           List.mem_of_elem_eq_true h2,
           List.mem_of_elem_eq_true h3⟩

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

/-! ## The validity boundary

Validation accumulates every protocol error.  There is no first-error path and
no constructor which turns a raw `Trace` into evidence suitable for analysis.
-/

/-- Every reason a raw trace can be refused before statistical interpretation. -/
inductive ProtocolError
  | operatorHomeReadable
  | futureCommitReachable
  | analysisArtifactReachable
  | runnerStoreReachable
  | expectationMalformed
  | expectedCellMissing
  | expectedCellDuplicated
  | unregisteredRun
  | ablationLeaked
  | wrongMemoryWithheld
  | sharedSession
  | wrongBaseRevision
  | controlClosureFloorTooHigh
  deriving DecidableEq, Repr

private def errorUnless (condition : Bool) (error : ProtocolError) :
    List ProtocolError :=
  if condition then [] else [error]

/-- All protocol failures in deterministic registration order. -/
def validateErrors (t : Trace) : List ProtocolError :=
  errorUnless t.isolation.homeReadDenied .operatorHomeReadable ++
  errorUnless t.isolation.noFutureCommits .futureCommitReachable ++
  errorUnless t.isolation.noAnalysisArtifacts .analysisArtifactReachable ++
  errorUnless t.isolation.noRunnerSideStore .runnerStoreReachable ++
  errorUnless (expectationWellFormed.check t) .expectationMalformed ++
  errorUnless (noOmissions.check t) .expectedCellMissing ++
  errorUnless (noDuplicates.check t) .expectedCellDuplicated ++
  errorUnless (noExtras.check t) .unregisteredRun ++
  errorUnless (ablationTookEffect.check t) .ablationLeaked ++
  errorUnless (withholdingAsRegistered.check t) .wrongMemoryWithheld ++
  errorUnless (sessionsDistinct.check t) .sharedSession ++
  errorUnless (revisionsAsRegistered.check t) .wrongBaseRevision ++
  errorUnless
    (decide (4 * (t.notClosedIn ArmKind.control) ≤
      (t.armRuns ArmKind.control).length)) .controlClosureFloorTooHigh

/-- A trace which crossed every protocol boundary exactly once.

The constructor is intentionally not hidden: its proof field still makes hand
construction equivalent to proving the complete validator empty.  Runtime code
obtains values through `validate`. -/
structure ValidatedTrace where
  raw : Trace
  noErrors : validateErrors raw = []

/-- Validate once, returning all errors or the only type accepted by `classify`. -/
def validate (t : Trace) : Except (List ProtocolError) ValidatedTrace :=
  let errors := validateErrors t
  if h : errors = [] then
    .ok ⟨t, h⟩
  else
    .error errors

/-- A successful validator result certifies that every accumulated check passed. -/
theorem validate_ok_noErrors {t : Trace} {v : ValidatedTrace}
    (h : validate t = .ok v) : validateErrors t = [] := by
  simp only [validate] at h
  split at h
  · assumption
  · simp_all

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
  -- Guard order matters: every validity precondition is discharged before any
  -- comparison is attempted, so a substantive verdict cannot be reached on
  -- data that should never have been analysed.
  --
  -- 1. Isolation. If the runner could reach the answer, nothing else means
  --    anything.
  if ! (t.isolation.homeReadDenied && t.isolation.noFutureCommits
        && t.isolation.noAnalysisArtifacts && t.isolation.noRunnerSideStore) then
    Outcome.indeterminate
  -- 2. The expectation set is real. A guard that ranges over a set you control
  --    is only as strong as that set: an empty panel makes every completeness
  --    check pass vacuously.
  else if ! expectationWellFormed.check t then Outcome.indeterminate
  -- 3. Completeness, reusing the observables rather than restating their
  --    logic: omissions, extras and duplicates each invalidate, and each is
  --    checked separately so a failure says which.
  else if ! (noOmissions.check t && noDuplicates.check t && noExtras.check t) then
    Outcome.indeterminate
  -- 4. The ablation actually ablated.
  else if t.runs.any (·.withheldPresent) then Outcome.indeterminate
  -- 4b. Something was actually withheld, and it was what the registration
  --     named. Without this a trace that ablated NOTHING passes guard 4 and
  --     can reach `rubricValidated`.
  else if ! withholdingAsRegistered.check t then Outcome.indeterminate
  -- 4c. Repeats are genuinely independent. A shared session means the runner
  --     remembers its earlier attempt, which is not a replicate.
  else if ! sessionsDistinct.check t then Outcome.indeterminate
  -- 5. Ceiling check: these problems are known to close, so a control arm that
  --    fails to reproduce closure signals a broken harness rather than a small
  --    effect.
  else if 4 * (t.notClosedIn ArmKind.control) > (t.armRuns ArmKind.control).length then
    Outcome.indeterminate
  else
    -- The test. `n` is NON-TIED PROBLEMS, never seed-level pairs: seeds are
    -- repeats within a problem, and counting them as independent would treble
    -- `n` and turn a null significant.
    let n := t.nonTiedProblems
    let k := t.lbWinsProblems
    if signTestPasses n k then Outcome.rubricValidated
    -- Both arms exceeding control while the primary test does not pass means
    -- the design is registering perturbation sensitivity as such. Note this is
    -- NOT a finding that load-bearing equals incidental: failure to reject is
    -- not equality, and the wording here is chosen to avoid implying it.
    else if signTestPasses (t.nonTiedVs ArmKind.ablateLoadBearing)
                           (t.winsVs ArmKind.ablateLoadBearing)
            && signTestPasses (t.nonTiedVs ArmKind.ablateIncidental)
                              (t.winsVs ArmKind.ablateIncidental) then
      Outcome.anyAblationBreaks
    else Outcome.rubricUnsupported

def decision : DecisionRule Trace Outcome where
  name := "arm-wise non-closure against the control floor, thresholds fixed pre-hoc"
  classify := classify

/-! ## Replication

**The pilot and the confirmation run are separate traces, and the confirmation
seeds carry all three arms.**

An earlier version read the plan as "pilot seeds index the control arm,
confirmation seeds index the ablation arms". That is incompatible with the
paired design that replaced it: every load-bearing or incidental observation
needs a control observation at the *same* `(problem, seed)`, so splitting the
arms across disjoint seed sets would leave every paired comparison incomplete —
and `noExtras` would additionally reject the pilot controls as unregistered
runs.

So:

* **pilot seeds** produce a *separate* pilot trace, all three arms, inspected
  for harness sanity before the confirmation run and never pooled with it;
* **confirmation seeds** produce the analysed trace, all three arms on every
  seed, which is what makes `(problem, seed)` pairing possible.

Disjointness still does the work it was there for: the confirmation seeds are
fixed before the pilot is looked at, so a floor cannot be re-estimated after
the effect is seen.
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
  -- Three arms, not four: the prose-only arm tested a separate hypothesis and
  -- was never read by the decision rule. Banked rather than given a role.
  arms := [controlArm, lbArm, inArm]
  flags :=
    [⟨"isolated account cannot read operator home", homeUnreadable⟩,
     ⟨"history truncated at base revision", historyTruncated⟩,
     ⟨"analysis artifacts unreachable", artifactsUnreachable⟩,
     ⟨"runner-side store unreachable", runnerStoreUnreachable⟩,
     ⟨"ablation took effect", ablationTookEffect⟩,
     ⟨"expectation set non-empty and duplicate-free", expectationWellFormed⟩,
     ⟨"no expected cell missing", noOmissions⟩,
     ⟨"no expected cell observed twice", noDuplicates⟩,
     ⟨"no run outside the registered panel", noExtras⟩,
     ⟨"each run withheld the registered memory", withholdingAsRegistered⟩,
     ⟨"no two runs shared a session", sessionsDistinct⟩]
  -- From a measured rate: ~20-35k runner tokens per dispatch, observed on a
  -- comparable design. 6-8 problems x 3 arms x 3 repeats, with the control
  -- arm run first as the pilot. The multiplier is included: an estimate
  -- counting only the ablation arms would be wrong by a factor of four.
  estimatedCost := 1400000
  budgetCap := 2000000
  -- Teardown of the isolated account, scheduled independently of the run
  -- succeeding, so a failed experiment does not leave a live second account.
  --
  -- Previously `some 1400000` — which was the TOKEN ESTIMATE pasted into a
  -- deadline field. The facility checks only `isSome`, so it passed readiness
  -- while carrying a number in the wrong unit entirely. 86400 is one day in
  -- SECONDS, which is the unit intended; that the field cannot say so is a
  -- gap worth raising against the facility rather than papering over here.
  teardownDeadline := some 86400

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
