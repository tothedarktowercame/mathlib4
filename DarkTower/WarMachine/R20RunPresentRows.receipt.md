# R20 `Carries` required-row receipt

- Base: `89f548db05ee40bd995df9bdbdc4d4d9871a5ed5`
- Patch: `69198075ca47a330034dc5f92d1521e1d05d140d`
- Branch: `wm-c5-present-rows`
- Worktree: `/home/joe/worktrees/mathlib4-c5-present-rows`
- Environment: Lake `5.0.0-src+fd00994`, Lean `4.31.0-rc1`; `.lake` is a
  symlink to `/home/joe/code/mathlib4/.lake`. Before building, `pgrep` found no
  other `lake`, `lean`, or `bg.py` build.

## Base negative control

`/home/joe/notes/wm-next/C5-present-rows/base-vacuous.lean` reproduces the five
fields of `Carries` at the base commit verbatim as `BaseCarries`. It constructs
two clicks with every record absent and proves they carry solely because the
four equations' hypotheses are false.

Command:

```text
lake env lean /home/joe/notes/wm-next/C5-present-rows/base-vacuous.lean
```

Result: exit 0. `base_absent_rows_carry` has only `[propext,
Classical.choice, Quot.sound]`.

## Patched negative and positive controls

`absentRequiredRows_refused` proves that the same pair of all-absent clicks
cannot satisfy the strengthened `Carries`. The old five-field constructor was
also attempted directly in
`/home/joe/notes/wm-next/C5-present-rows/patched-vacuous-rejected.lean`:

```text
lake env lean /home/joe/notes/wm-next/C5-present-rows/patched-vacuous-rejected.lean
```

Result: exit 1 as intended. Lean reports that `Carries.mk` now has 11 fields
and leaves the required-row existence goals false.

The positive control is the existing two-click witness
`R20RunExample.example_runCertified`; it rebuilt successfully without changing
any carry equation or `runAdvances`.

## Build and axioms

Launched with the required durable runner:

```text
python3 /home/joe/code/futon3c/scripts/bg.py launch \
  "lake build DarkTower.WarMachine.R20Run DarkTower.WarMachine.R20RunExample > /home/joe/notes/wm-next/C5-present-rows/final-build.log 2>&1" \
  --agent codex-9 --label c5-present-final \
  --dir /home/joe/worktrees/mathlib4-c5-present-rows
```

Result: exit 0, `Build completed successfully (3381 jobs)`.

Printed axioms:

- `carries_rows_present`: `[propext, Classical.choice, Quot.sound]`
- `absentRequiredRows_refused`: `[propext, Classical.choice, Quot.sound]`
- `example_carries`: `[propext, Classical.choice, Quot.sound]`
- `R20RunExample.example_runCertified`: `[propext, Classical.choice,
  Quot.sound]`

No printed theorem contains `sorryAx`.

## Artifact hashes

```text
45a358b332c4512d6419c6600ce4b5e905e3d412cfed3d025a3f32a1147c642d  base-vacuous.lean
77c4d4e185231198e526f1d13fa14005cb3cdca0861062574be6a286070d4a79  base-vacuous.log
bf1e5b818951dfadd43a2b1f3343589cf69c9ec0402754ba6a9e7b72e3c485fe  patched-vacuous-rejected.lean
c0f32d743b696cc37da8dafd57f4fe37f5b6557147d03e9dea62b9f02985648d  patched-vacuous-rejected.log
5c36835590db6692c4d1893343db193e6d3eef7708590f47453a3d865993d721  final-build.log
```
