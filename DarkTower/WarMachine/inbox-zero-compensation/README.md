# INBOX ZERO compensating safety, 2026-09-14

Sibling of `InboxZeroWitness.lean`, preserving its original atomic T2 unchanged.
Grounding: `futon3/library/workshop/compensate-when-exclusion-is-unobtainable.flexiarg`.
This proves the **restated model law**, not production detector or revert
correspondence: `:runtime-correspondence :not-proven`. No runtime fields changed.

## The bound is part of the theorem

- `detectionBound w D`: if an edit occurred, the comparator detects it by
  `committedAt + D`, assuming detection delay at most D.
- `detectionFromEdit w editTime C D`: detection is by `editTime + C + D`.
  C bounds edit-to-commit delay. A post-commit bound alone says nothing about
  how long an edit waited before that commit.
- `compensation`: a detected race with **successful restoration** leaves
  `commitSurvives = false` and a repo-bound `racedWithEdit` record.
- `boundedSurvival w D U t`: for every t >= `committedAt + D + U`, no commit
  effect survives, provided undo succeeds and its delay is at most U.
- `survivalFromEdit`: the corresponding end-to-end bound is C + D + U.
- `boundedCompensation` connects that temporal claim to the terminal result and
  typed race record. Detection latency is NOT silently substituted for total
  compensation latency.

Inside the window the optimistic commit can exist: `fixtureTransientCommit`
proves that it does in the example. Compensation does not retract an external
observer's earlier exposure, undo hooks/remote actions, or erase git history.
The quantified survival claim concerns the modeled commit's effect after the
window. No numerical cost for transient harm is invented.

## What the model assumes rather than proves about the consumer

`Window.edits` counts all edits between snapshot/check and commit. The post-check
version is snapshot + edits; monotone versions cannot hide an edit. Detection
compares these versions. A content hash with a change-and-restore (ABA) window,
a partial tree scan, untracked files omitted from measurement, or an unobserved
editor write does NOT automatically implement this model. The model fixture is
an edit-after-snapshot shape (revision 10 -> 11), not a pinned production readback.
Physical detector completeness and measured timing need separate runtime evidence.

`Undo.restored` means the optimistic commit effect is removed while the editor's
post-edit revision is preserved (`editorChangesPreserved`). It does NOT mean
resetting to the stale snapshot. A git revert/reset must independently demonstrate
this semantic contract; destructive loss of the live edit is not compensation.
The unsuccessful branch is explicit: `Undo.failed` retains the commit effect and
emits `compensationFailed`. `failedUndoCanSurvive` is a counterexample to
unconditional safety. The consumer must hold/escalate on such a result, not
claim T2'b. Finite Nat delays are model inputs, not evidence that an I/O operation
actually completes within those bounds.

The original step is used as a *planned decision* at the check. In compensating
mode its commit is optimistic; the edit window follows that check. In
`refuseWithoutExclusion` mode no commit is issued and a planned commit instead
produces `atomicFeelCommitUnavailable`. `strictRefusal` proves no issued effect
in that mode. Callers with real exclusion can still use the original atomic T2;
this sibling neither changes nor rebrands it.

## Composition with the loop

T1 (`typedTermination`, `cycleTypedTermination`, `cycleLength`) still gives finite
per-repo outputs with typed records for every non-clean result, including failed
compensation. T3 (`progress`) gives surviving clean success OR a typed blocker;
a race/failed undo is a blocker, not a clean success. `flagsNonincreasing` and
`cycleFlagsNonincreasing` count unresolved repos, not cumulative ledger entries.
No unrelated new observations are modeled during that traversal.

T4 (`zeroFixedPoint`, `cycleZero`) leaves all-clean repo states fixed, emits no
commit and no new record, and reports the model's `zeroWitnessed` meter. Edit
windows here belong only to attempted commits; this is not a claim that an
external editor cannot dirty a clean repo after observation. `recordsPreserved`
and `recordAppended` preserve the old ledger and append every returned finding.

## Executed checks

```sh
python3 scripts/check-inbox-zero-compensation.py
```

Targeted build and direct elaboration exit 0, no errors/warnings, all 22 printed
axiom reports exclude `sorryAx`. Standard Lean axioms are reported, not suppressed.
Six deliberately false negative claims each exit 1 with a logical diagnostic:

1. MissedEdit: the edit-after-snapshot case goes undetected.
2. SurvivesDeadline: the commit survives the successful compensation deadline.
3. DetectionOnlyBound: the commit is gone at detection time, ignoring undo time.
4. FailedUndo: unsuccessful restoration nevertheless guarantees no survivor.
5. LostEditorChange: restoration reverts to revision 10 and loses revision 11.
6. ZeroCommits: clean input emits a commit.

`controls-2026-09-14.json` retains argv, stdout/stderr, exits and model digest.
Negative fixtures are intentionally not normal build targets. The driver refuses
unexpected exits, missing-import/nonlogical errors and timeouts. No full suite,
production run or runtime edits were performed. Python compilation and diff
checks passed. `input-pins.json` pins the unchanged atomic model and pattern
source used for this handoff. Independent review remains separate.
