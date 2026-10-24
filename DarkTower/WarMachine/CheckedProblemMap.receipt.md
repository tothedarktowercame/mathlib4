# Checked problem map execution receipt

- Date: 2026-10-24 UTC
- Base: `196285e3d5406afaa3f5c82d1181b135fa425f7f` (`darktower`)
- Branch: `wm-checked-problem-map`
- Worktree: `/home/joe/worktrees/mathlib4-checked-problem-map`
- Module SHA-256: `8692281f6ed9b2f55567377b1701c3f19a5f9693e5ea6695622062f02e605b32`
- Negative-control SHA-256 (`FalseClosure.lean`): `c6d690e5353b094e613f9acf6455247f66ba2ef5b6930678e14f0250df30d944`
- Logs: `~/notes/wm-next/loop-plan/checked-problem-map/{build,axioms,false-closure}.log`

## Result and scope

A fixed finite type `S` of statement IDs is interpreted by `I : S → Prop`.
An `Artifact` carries a proof of `I stmt`. A `Reduction` carries a head, a
`Finset` of tails and a proof that all tails jointly imply the head. Several
reductions with one head are alternative routes. `Closed m` is the least
derivation (the least set closed under these Horn rules).

- `closed_sound`: every closed ID has a proof of its interpretation.
- `closed_least`, `closed_ruleClosed`: `Closed m` is the least rule-closed set.
- `update m : Option ReturnReport → ProblemMap` admits only the report's
  `checked` part (artifacts and reductions). Label and `claimedClosed` are data.
  `none` (absent return) is the identity.
- `closed_update` (monotone), `update_sound`, `update_obligations`,
  `open_update` (unresolved obligations only shrink), retention of artifacts
  and reductions, `update_report_irrelevant` (label and claims do not affect
  the map), `closed_update_unchecked` (an empty checked part closes exactly
  what was closed before).

Controls, all on a six-ID universe whose interpretations are all true, so every
non-closure is structural:
- `reduction_not_discharge`: a checked reduction for the consumer exists and
  the consumer is open.
- `foundation_adapter_discharge`: foundation and adapter artifacts close the
  consumer, and `interp .consumer` follows.
- `one_alternative_suffices`: the consumer closes while the alternative route's
  tail `hard` stays unclosed.
- `foundation_without_adapter_unclosed`: the foundation alone, labelled closed
  and claiming the consumer, does not close it.
- `unseeded_cycle_unclosed`: the cycA/cycB cycle stays unclosed.
- `prediction_or_absent_unclosed`: a prediction-only report and an absent
  report both leave the consumer unclosed.
- `censored_helper_admitted`: a censored report's checked adapter is admitted;
  the consumer stays unclosed.

Not in scope: runtime receipt authenticity, a decoder from runtime records,
any equation between IDs and live Lean names or commits, executable or
decidable closure, counting/learning semantics, probabilities, scores,
preferences.

## Commands and exits

1. `lake env lean DarkTower/WarMachine/CheckedProblemMap.lean`: exit 0, no output.
2. `lake build DarkTower.WarMachine.CheckedProblemMap`: exit 0, 618 jobs.
3. `lake env lean ~/notes/wm-next/loop-plan/checked-problem-map/Axioms.lean`: exit 0.
4. `lake env lean ~/notes/wm-next/loop-plan/checked-problem-map/FalseClosure.lean`:
   expected exit 1. `false_foundation_only_closes` fails with a type mismatch
   against the proved `¬ Closed …`. `false_cycle_closes` fails with an unsolved
   goal: the cycB artifact is not among the map's artifacts.

The module contains no `sorry`.

## Printed axioms

All 14 listed theorems: `[propext, Quot.sound]`. No `sorryAx`, no `Classical.choice`.

## Source boundary

- Least model of Horn rules: Aczel 1977, "An introduction to inductive
  definitions", Handbook of Mathematical Logic; van Emden and Kowalski 1976.
- AIF: Parr et al. 2022 ch. 7 treats a closure verdict as an observation
  through a likelihood. Proof-map soundness is the domain refinement that
  grounds that observation; it is not derived from active inference.
- Existing machinery searched and not reused, because none carries proofs over
  joint tails: `FiniteListGraphClosure`, `ConstructionReceipt`,
  `CertificateStates`, `R15StrategicTarget.withRepairs`.
