# L1 pattern-theta carry receipt

- Base: `7b59369f10bca6f5bf144b6ecb51b2743641de42`
- Patch: `4efa8bafe5a6194bc22c634e1be48663c79ea66f`
- Branch: `wm-l1-theta-carry`
- Worktree: `/home/joe/worktrees/mathlib4-l1-theta-carry`
- Environment: Lake `5.0.0-src+fd00994`, Lean `4.31.0-rc1`; `.lake` links
  to `/home/joe/code/mathlib4/.lake`. No competing `lake` or Lean build was
  running before the worktree was created.

## Statement fixed before implementation

The positive statement was that a mandatory click carrier names a pattern
explicitly, ties its current count to a published `PatternTheta.ThetaReading`
plus that pattern's admitted history, computes `after` with the existing
`PatternTheta.advanceWitnessed`, and is consumed as the successor's `before`.

The controls fixed before implementation were:

- a witnessed success increments that pattern's alpha count;
- an unwitnessed outcome changes no count;
- resetting the successor to the reading prior is refused by `Carries`;
- the existing two-click `R20RunExample` remains certified.

`PatternIdentity` is a nominal type distinct from `Policy`. The caller supplies
it explicitly; no action-to-pattern inference is introduced.

## Results

- `run_theta_step`: every `RunCertified` boundary consumes the predecessor's
  retained theta `after` state.
- `thetaWitnessedSuccess_moves_count`: the example pattern moves from `(1,1)`
  to `(2,1)` after a witnessed success.
- `thetaWitnessedSuccess_consumed`: click 1 starts from `(2,1)`.
- `thetaUnwitnessed_unchanged`: click 1's unwitnessed event is inert.
- `thetaReset_refused`: replacing click 1's starting state by the published
  `(1,1)` prior contradicts `Carries.theta`.
- `R20RunExample.example_runCertified` still builds.

Omission is structurally excluded: `Click.theta : ThetaCarrier` is mandatory,
not an `Option`, and no Jeffreys/default construction is provided. The carrier's
`after_eq` is the existing `advanceWitnessed`; an arbitrary supplied after-state
cannot inhabit it.

## Command and exit

Launched through the durable build runner:

```text
python3 /home/joe/code/futon3c/scripts/bg.py launch \
  "lake build DarkTower.WarMachine.R20Run DarkTower.WarMachine.R20RunExample DarkTower.WarMachine.R20HabitPrior > /home/joe/notes/wm-next/L1-theta-carry/final-build.log 2>&1" \
  --agent codex-9 --label l1-theta-final \
  --dir /home/joe/worktrees/mathlib4-l1-theta-carry
```

Exit: 0. Tail: `Build completed successfully (8529 jobs)`.

The log prints these axioms:

- `run_theta_step`: `[propext, Classical.choice, Quot.sound]`
- `thetaWitnessedSuccess_moves_count`: `[propext, Quot.sound]`
- `thetaWitnessedSuccess_consumed`: `[propext, Classical.choice, Quot.sound]`
- `thetaUnwitnessed_unchanged`: `[propext, Quot.sound]`
- `thetaReset_refused`: `[propext, Classical.choice, Quot.sound]`
- `R20RunExample.example_runCertified`: `[propext, Classical.choice,
  Quot.sound]`

No changed source contains `sorry` and no printed theorem contains `sorryAx`.

Build-log sha256:

```text
983121fa183a6747e41648c714ab38a9f7ddf2535ebe8bbead4edd6005d9b200  final-build.log
```
