# R20 checked-map carry execution receipt

- Date: 2026-10-24 UTC
- Base: `8d17201e204dc2d6548ada510092a6ea8e089e44`
- Branch: `wm-r20-checked-map-carry`
- Worktree: `/home/joe/worktrees/mathlib4-r20-checked-map-carry`
- Module SHA-256: `840e6355bfaf0d82e8e77bc6e629c4b82de51c3f4d25e6707ce4a2a975b37b6f`
- Negative-control SHA-256: `30ae92704ff4617fa9ddf7a2ea2ae27622e991e9e2d6db908c2a8f067aafbdc0`

## Result and indexing

`CheckedMapRun ... n` wraps the same supplied R20 click sequence through
click `n` inclusive. At click `i`:

- `input i` is the exact checked proof map before its report;
- `output i = update (input i) (report i)`;
- `observation run i` is `returnObs` of that same update;
- for `i < n`, `input (i+1) = output i`.

The wrapper stores the original `RunCertified` proof unchanged, and
`runCertified` projects it for the identical click function. No original row,
wiring, prior, theta, valence, or carry obligation is weakened.

Proved consequences include exact boundary equality, same-step observation
soundness, persistence of every initially closed statement, and
`input n = foldReports initial [report 0, ..., report (n-1)]`. `extend` is
conditional on the existing next-click certificate and `Carries`; it asserts
neither successor existence nor liveness.

## Witness and controls

The existing `R20RunExample` two-click certified sequence is enriched rather
than replaced. Click 0 admits the checked adapter from `censoredHelper`; click
1 admits the checked foundation. The actual second `returnObs` closes consumer
via the existing `viaFoundation` reduction. The original R20 certificate is
projected from this wrapper.

- Resetting input 1 to `m0` fails because output 0 contains `adapterArt`.
- Claiming consumer in the same-step observation of `foundationOnly` fails
  because no adapter is present.
- A separate two-click wrapper with both reports absent keeps every map
  exactly `m0` and remains accepted.

These are supplied synthetic checked reports, not runtime decoding or fresh
learning-success admission. Old closures are only retained closures.

## Commands and exits

1. `lake env lean DarkTower/WarMachine/R20CheckedMapCarry.lean` — exit 0.
2. `lake build DarkTower.WarMachine.R20CheckedMapCarry` — exit 0; 8541 jobs.
3. `lake env lean ~/notes/wm-next/loop-plan/r20-checked-map-carry/FalseResetAndObservation.lean`
   — expected exit 1 with two type mismatches: each available theorem has
   type `claimed equality/membership → False`, while the scratch file requests
   the false equality/membership itself.

Imported modules emit existing warnings, including `Holes.lean` sorry
warnings. This module contains no `sorry`; its printed theorem closures have
no `sorryAx`.

## Printed axioms

The wrapper projection, fold law, closure persistence, observation soundness,
positive witness, and reset control use only `propext`, `Classical.choice`,
and `Quot.sound`.

## Boundaries

This uses the existing `R20Run.RunCertified`,
`R20RunPrefixExtension.runCertified_succ_iff`,
`CheckedProblemMap.update`, and `CheckedReturnObservation.returnObs` at the
pinned base. It proves checked proof-map continuity only. There is no runtime
identity/refinement theorem, executable closure, probability or preference
choice, theta-to-scorer binding, learning admission, or infinite-run claim.
