+# Theta prediction consumer execution receipt

Date: 2026-10-24 UTC  
Author: codex-9  
Branch: `wm-theta-prediction`  
Worktree: `/home/joe/worktrees/mathlib4-theta-prediction`

## Pins and scope

- Base darktower: `d6e80d4578ec3571a34aedf5a36b3155b10373db`.
- Code commit: `9f619afa7bed5c8a0c6e012b4c8060108545359c`.
- The worktree `.lake` is a symlink to `/home/joe/code/mathlib4/.lake`.
- New module only: `DarkTower/WarMachine/ThetaPredictionConsumer.lean`.
- No existing predicate or semantics was changed.

The fixture is explicitly synthetic: one `Unit` occurrence over a finite Bool
token domain, initial state empty, a pattern producing `true`, and a
deterministic observation distinguishing the produced state as `.focused`.
`ThetaReading r` and admitted history `xs` remain parameters.

## Result

`oneStep` is composed from the existing functions:

```text
PatternTheta.interpretWithTheta
→ CascadeCoApplyG.coKernel
→ CascadeEFE.prediction
→ CascadeEFE.push
```

`oneStep_focused_eq_theta` proves the exact one-step focused mass is
`(PatternTheta.thetaOf r xs : Real)`.
`admitted_success_raises_prediction` rewrites both predictions with that exact
equation and uses the existing `PatternTheta.success_raises` theorem for
`xs ++ [true]`.

The controls `frozen_theta_prediction_eq` and
`frozen_theta_not_strict` establish that an unchanged theta cannot support the
strict-increase conclusion.

This proves only that the existing canonical mathematical prediction responds
to an admitted parameter update in this enabled, distinguishable synthetic
case. It does not prove G or winner monotonicity, runtime causality or witness
authority, or bind a pattern occurrence/full predicted distribution to the same
R20 `Click`, its scalar `reach`, or its ports. That cross-model binding remains
open.

## Positive build and axioms

Command, cwd `/home/joe/worktrees/mathlib4-theta-prediction`:

```text
lake build DarkTower.WarMachine.ThetaPredictionConsumer
```

Exit: `0`. Tail:

```text
Built DarkTower.WarMachine.ThetaPredictionConsumer
oneStep_focused_eq_theta:
  [propext, Classical.choice, Quot.sound]
admitted_success_raises_prediction:
  [propext, Classical.choice, Quot.sound]
frozen_theta_not_strict:
  [propext, Classical.choice, Quot.sound]
Build completed successfully (8513 jobs).
```

There is no `sorry` or `sorryAx` in the new module or its printed theorem
axioms. The build replayed pre-existing `sorry` warnings from
`DarkTower/WarMachine/Holes.lean`; none appears in these theorem dependencies.

Full log:
`/home/joe/notes/wm-next/loop-plan/theta-prediction-logs/build.log`  
SHA-256:
`eaa2024db51e11dc074e70de00b8f45e27de5105b847b7a9c25a99be20146dcc`.

## Deliberately false theorem

Scratch:
`/home/joe/notes/wm-next/loop-plan/ThetaPredictionFalse.lean`  
SHA-256:
`91deda1a738e2dd95a2e1e4290e51a0da63daa3c8c0a7ba47c097021bd1f761a`.

Command:

```text
lake env lean /home/joe/notes/wm-next/loop-plan/ThetaPredictionFalse.lean
```

Expected exit: `1`. Lean rejects the self-strict frozen-theta claim because
`frozen_theta_not_strict r xs` has type `¬ (p < p)`, while the false theorem
requires `p < p`.

Log:
`/home/joe/notes/wm-next/loop-plan/theta-prediction-logs/false-theorem.log`  
SHA-256:
`214395fc9eddd6050dc52288f4cfe81ffd9c75bdfdf24f65a2dee52397f9a1e7`.

## Source and diff checks

Commands:

```text
git diff --check
rg -n '\bsorry\b|sorryAx' DarkTower/WarMachine/ThetaPredictionConsumer.lean
git status --short
```

Before the code commit, `git diff --check` exited 0 and the `rg` check found
nothing. After the receipt commit, the worktree is expected clean. No Clojure,
runtime, graph, click, reload, or live-state operation was performed.

