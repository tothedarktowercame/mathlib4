+# Coherent theta candidate execution receipt

Date: 2026-10-24 UTC  
Author: codex-9  
Branch: `wm-aif-coherent-theta`  
Worktree: `/home/joe/worktrees/mathlib4-aif-coherent-theta`

## Pins and scope

- Base darktower: `c1690c87cbc5d4a2e099d1e8674b5ba3e942ba04`.
- Code commit: `0e77696543e3b4583e5615bb8c8d0d6399c32723`.
- Worktree `.lake`: symlink to `/home/joe/code/mathlib4/.lake`.
- New module only: `DarkTower/WarMachine/CoherentThetaCandidate.lean`.
- No existing scorer, R20 predicate/equation, runtime source, or state changed.

## Source contract

Read local Parr et al., *Active Inference* (2022):

- `futon2/holes/labs/wm-contract/refs/parr2022.txt:7214-7235`,
  equations 7.9–7.10: parameter belief `Q(theta)`, categorical Dirichlet
  (pseudo-)counts, and the normalized-concentration mean approximation.
- `futon2/holes/labs/wm-contract/refs/parr2022.txt:7301-7325`, equation 7.11:
  expected free energy gains an expected parameter-information-gain term,
  rearranged as novelty.

Also read `PatternTheta.lean:14-26,66-108,159-168` and
`PatternThetaNovelty.lean:9-30,42-84,93-127`. The latter explicitly identifies
`novelty = 1/(2(a+b))` as an asymptotic binary Dirichlet approximation, not
exact expected information gain. Applying the Beta model to pattern transitions
is the existing declared modelling choice; the sources do not name cascade
patterns.

## Implemented behaviour

`Coherent candidate` requires every interpreted pattern theta to equal the
posterior mean of that same pattern's positive novelty concentrations.

`ofReadings` takes supplied structural fields, published `ThetaReading`
values, already-admitted histories, and supplied initial/observation kernels.
It derives:

- each pattern with existing `PatternTheta.interpretWithTheta`;
- each count pair as prior success/failure concentrations plus existing
  `successes`/`failures`.

`ofReadings_coherent` proves the constructor satisfies `Coherent`.

For the explicitly synthetic, enabled singleton consumer at horizon one,
`coherent_admitted_success_moves_both` proves for arbitrary reading `r` and
history `xs`:

1. the existing canonical focused prediction strictly rises for
   `xs ++ [true]`, via `ThetaPredictionConsumer.admitted_success_raises_prediction`;
2. the one-step novelty strictly falls, via
   `PatternThetaNovelty.success_decreases`.

The theorem does not generalise total novelty across multiple steps, where the
changed transition can change state visitation.

Controls proved:

- `staleCounts_incoherent`: fresh theta with old counts;
- `frozenThetaFreshCounts_incoherent`: old theta with fresh counts;
- `lessTried_incoherent` and `moreTried_incoherent`: the existing arithmetic
  novelty examples use theta 1 with count means 1/2 and 2/3 respectively.

The existing `less_tried_positive_fire_lower_G` remains valid as a permissive
arithmetic theorem; these controls only show those fixtures are not
single-posterior coherent model instances.

This predicate does not enforce itself in `scoreCascadeCoN`, establish
admission evidence/runtime compliance, or bind an occurrence/full prediction
to an R20 `Click`, scalar `reach`, or selection port.

## Build and axioms

Command, cwd `/home/joe/worktrees/mathlib4-aif-coherent-theta`:

```text
lake build DarkTower.WarMachine.CoherentThetaCandidate
```

Exit: `0`; `8516` jobs completed.

Printed theorem axioms for P1, P2, and all incoherence controls are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No new theorem depends on `sorryAx`. The build replayed known, pre-existing
`sorry` warnings from `Holes.lean`; none occurs in this module or its printed
dependencies.

Build log:
`/home/joe/notes/wm-next/loop-plan/coherent-theta/logs/build.log`  
SHA-256:
`0e85f4b0dc34d49747e919438705b6f56ef834c1877d0e45a74f5b6611b659d0`.

## Deliberately false coherence theorem

Scratch:
`/home/joe/notes/wm-next/loop-plan/coherent-theta/FalseCoherence.lean`  
SHA-256:
`41d62dbec1a7bf27d0c9023816af6e6b0aeaabace57e69beb92eda2d12e1a440`.

Command:

```text
lake env lean /home/joe/notes/wm-next/loop-plan/coherent-theta/FalseCoherence.lean
```

Expected exit: `1`. Lean rejects the claim that `staleCounts r xs` is
coherent because the supplied proof has the negated type
`not (Coherent (staleCounts r xs))`.

Log:
`/home/joe/notes/wm-next/loop-plan/coherent-theta/logs/false-coherence.log`  
SHA-256:
`b33ecf26b7ee3b3f26369b8eb383724061cad307d7282ad0424c80bfbe68fd8e`.

## Source checks

Commands:

```text
git diff --check
rg -n '\bsorry\b|sorryAx' DarkTower/WarMachine/CoherentThetaCandidate.lean
git status --short
```

`git diff --check` exited 0; the source scan found nothing. Module SHA-256:
`b41917691e9d1a0a24000fa790b21ec5333c91fcb3c9a8f1fa78ae5e9c37f67b`.

