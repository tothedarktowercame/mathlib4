# INBOX ZERO loop witness — 2026-09-14

`../InboxZeroWitness.lean` models the loop, separately from ChipBoardWitness's
executor. It elaborates with no errors or warnings. This is **model-only**:
`:runtime-correspondence :not-proven`. No runtime status field is changed.

## What is proved

| Requested law | Declaration | Exact scope |
|---|---|---|
| T1 typed termination | `typedTermination`, `cycleTypedTermination`, `cycleLength` | Finite traversal returns one output per input; every non-clean output carries a typed record naming that output's repository. |
| T2 safety | `inFlightNeverCommitted` | The atomic transition never commits when its execution-time state is in-flight, regardless of stale observation. |
| T3 progress | `progress` | Dirty and committable produces a clean committed output or a repo-bound typed refusal naming the blocker. |
| T3 monotonicity | `flagsNonincreasing`, `repeatedFlagsNonincreasing` | Outstanding non-clean repository count cannot increase through a cycle or any finite repetition without external state changes. |
| T4 zero fixed point | `zeroFixedPoint`, `zeroAppendsNoRecords` | All-clean state projection is unchanged; zero commit effects, zero new records, report `zeroWitnessed`. |
| Ledger preservation | `refusalsAppended`, `refusalRecorded` | Old ledger is a prefix; every emitted record is appended. |

`CycleInput` represents the typed record set with unique repo names. `cycle`
returns outputs, the appended ledger and the meter report. The list laws are
stronger than the unique-name restriction: they also hold per entry of a list.
Dirty age is retained on refusal. In-flight is conservatively unresolved and
gets a typed refusal; it is never silently classified as clean.

## Assumptions and limits

- `current` is the execution-time FEEL/guard state; `observed` can be stale.
  The guarded commit is **atomic in this model**. A production FEEL check alone
  does not establish safety across a check/use race. The consumer needs a lock
  or an equivalent independently checked exclusion/transaction contract.
- `CommitResult` supplies success or a typed refusal. The model does not prove
  that git terminates, that a claimed success cleaned the repository, or that
  an externally supplied blocker describes reality. A timeout would need to
  return a typed refusal through this port rather than hang indefinitely.
- T1 is totality of this finite function, not termination of arbitrary I/O.
- No-new-dirt is explicit in `nextInputs`: only previous outputs become next
  current states. Permission/commit outcomes are retained for the repeat model;
  the single-cycle theorem holds for arbitrary choices of these fields.
- Flags count unresolved repos, **not** historical ledger entries. Repeated
  refusals can grow the ledger. Eventual zero, fairness, no starvation and
  idempotent/deduplicated refusal publication are not claimed.
- `exampleProgress` is a **three-repository model fixture**, with 2 flags -> 1,
  one commit and one `commitFailed` blocker. It is not a readback of the reported
  12-repository live run. No production digest or registry identity is invented.
- `zeroWitnessed` names the model's meter result. It is not a Lean attestation
  of production correspondence or a replacement for a pinned live certificate.

## Reproduce and interpret the gates

From the mathlib4 source checkout (its own `.lake/packages`):

```sh
python3 scripts/check-inbox-zero-witness.py
```

The checker first builds only `DarkTower.WarMachine.InboxZeroWitness`, then
elaborates it directly and inspects its axiom printouts. Dependencies use Lake's
normal cached source-checkout build; no APM package authority is modified.
The retained transcript has build exit 0, model exit 0, and these five induced
negative controls each exit 1:

- T1Silent: dirt silently returned without a typed record.
- T2StaleFeel: commit authorized despite current in-flight state.
- T3SilentProgress: idle committable dirt gets neither commit nor blocker.
- T3NewDirt: output introduces dirt from a clean state without observation.
- T4ZeroCommit: zero-state output commits anyway.

These are deliberately false claims about mutated outputs. Their compiler
failures must be logical refusals (`unsolved goals` or a false proposition
reported by `decide`), not missing imports or environmental failures. The driver
returns 0 only when all expected exits and diagnostics match; timeout/resource
abort is a failed gate, not a theorem counterexample. Negative fixtures are not
members of the normal positive build target.

All 18 printed theorem dependencies are free of `sorryAx` (standard `propext`,
`Quot.sound`, and in the fixed-point proof `Classical.choice`, are reported).
`controls-2026-09-14.json` retains stdout, stderr, exit codes, argv and model SHA;
`build-2026-09-14.log` retains the successful targeted build. No whole-project
suite or live cycle was run. Independent review is the next evidence boundary.
