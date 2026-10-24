# R20 run-prefix extension receipt

Date: 2026-10-24 UTC

Author: codex-9; reviewer: codex-11

Branch: `wm-run-prefix-extension`

Worktree: `/home/joe/worktrees/mathlib4-run-prefix-extension`

## Pins

- Base `darktower`: `be3da9b07b03ef6ce99428e1b0a35bfbe86f1888`
- Code commit: `e4c9535af1`
- Module SHA-256: `0d098ee721f129a95869317bb852b9e253597c7bb2136c3ba7633321322309c5`
- Negative-control SHA-256: `7392cc43b1f4864aaed082a4b8cc3081cbdb481ffa71bd5b8c0cb0c7742b84a3`
- `.lake` was verified as a symlink to `/home/joe/code/mathlib4/.lake` before building.

## Result

`runCertified_succ_iff` proves, on the same supplied sequence `c`:

```text
RunCertified L relation c (n + 1) ↔
  RunCertified L relation c n ∧
  ClickCertified L relation (c (n + 1)) ∧
  Carries L (c n) (c (n + 1))
```

`ClickCertified` is only a name for the existing per-click triple:
`FocusCertified`, `PriorFromCounts`, and `BetaFromValence`. No predicate was
weakened or changed. `runCertified_mono` restricts a certified supplied
sequence from bound `n` to any `m ≤ n`.

`example_two_click_decomposes` instantiates the iff at `n = 0` with
`R20RunExample.example_runCertified`. The replay control constructs the same
locally valid successor shape with run id zero. `replayedClick_certified`
proves its per-click triple; existing `R20RunExample.replayedRun_breaks_run`
and `per_click_validity_does_not_extend` prove that the missing boundary still
prevents extension.

This is conditional finite-prefix composition. It proves neither successor
existence, arbitrary/infinite runtime liveness, nor a theta-to-construction
consumer binding.

## Positive build

Command from the worktree:

```text
lake build DarkTower.WarMachine.R20RunPrefixExtension
```

Exit `0`; tail:

```text
ℹ [8530/8530] Built DarkTower.WarMachine.R20RunPrefixExtension (2.1s)
Build completed successfully (8530 jobs).
```

The build replayed dependencies and printed their pre-existing warnings,
including `Holes.lean` declarations with `sorry`. The new module itself has no
`sorry`, `admit`, axiom declaration, warning, or error. Its four printed
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; none
reports `sorryAx`.

Source check:

```text
rg -n "sorry|admit|axiom" DarkTower/WarMachine/R20RunPrefixExtension.lean
```

Exit `0`; the only matches are four `#print axioms` commands. `git diff
--check` exited `0`.

## Deliberate negative

File: `/home/joe/notes/wm-next/loop-plan/PrefixExtensionNegative.lean`.
It supplies the proved valid zero prefix and locally certified replayed
successor to `runCertified_succ_iff`, then deliberately tries to fill the
required replay boundary with the good non-replayed boundary.

Command:

```text
lake env lean /home/joe/notes/wm-next/loop-plan/PrefixExtensionNegative.lean
```

Exit `1`, expected:

```text
error: Type mismatch
  R20RunExample.example_carries
has type
  Carries flatLevel R20RunExample.click0 R20RunExample.click1
but is expected to have type
  Carries flatLevel (replayedClicks 0) (replayedClicks (0 + 1))
```

The failure is the exact missing carry for the same supplied successor; a
valid boundary for a replacement successor cannot be substituted.

No Clojure, runtime, click, reload, live state, graph, or existing Lean source
was changed.
