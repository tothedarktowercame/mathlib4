+# Finite joint AIF objective identity receipt

Date: 2026-10-24 UTC  
Author: codex-9  
Branch: `wm-aif-joint-identity`  
Worktree: `/home/joe/worktrees/mathlib4-aif-joint-identity`

## Pins and scope

- Base darktower: `ce7a2169ad8c16a7a71865cd262bf77d511620a8`.
- Code commit: `3f783c9e6500047d174693ef64b79514a1b73f29`.
- Worktree `.lake`: symlink to `/home/joe/code/mathlib4/.lake`.
- New module only:
  `DarkTower/WarMachine/AIFJointObjectiveIdentity.lean`.
- No existing definitions, R20 predicates, runtime source, or state changed.

## Literature boundary

Read local da Costa et al. 2020
`futon2/holes/labs/wm-contract/refs/dacosta2020.txt:775-835`:

- equation 13 states hidden-state/parameter risk plus ambiguity;
- equation 14 gives evidence and expected-information-gain forms;
- equation 15 replaces state risk with outcome risk only under its explicit
  small posterior-divergence approximation;
- equation 16 separates extrinsic and intrinsic terms.

Read Parr et al. 2022
`futon2/holes/labs/wm-contract/refs/parr2022.txt:7301-7325`, equation
7.11, which presents outcome risk, ambiguity, parameter information gain,
salience, novelty, and pragmatic value.

The theorem is therefore described only as the exact finite algebra of the
**outcome-risk specialization**. It is not claimed to be universally identical
to da Costa equation 13's state-risk form.

## Implemented identity

The theorem `outcomeRisk_add_ambiguity_eq` takes:

- a normalized finite latent prior `ProbabilityKernel Unit Z`;
- a normalized finite conditional observation kernel
  `ProbabilityKernel Z O`;
- a normalized finite outcome preference `ProbabilityKernel Unit O`;
- strict positivity of each preference mass.

Zero prior and observation-kernel masses remain permitted.

Its left side is exactly the existing
`PolicyExpectedFreeEnergy.finiteRisk` of the existing
`predictedOutcome`, plus existing
`PolicyExpectedFreeEnergy.ambiguity`. Its right side is existing
`CascadeEFE.pragmaticCost` (expected negative log preference) minus existing
`CascadeEFE.information`.

The information functional is the induced joint KL:

```text
sum_(z,o), joint(z,o) * log (joint(z,o) / (prior(z) * outcome(o)))
```

with the existing zero-joint-mass branch. It is not defined as entropy minus
ambiguity. The proof establishes adapters `outcomeOf_eq_push`,
`ambiguity_eq`, and `finiteRisk_eq`, then applies the already-proved
`CascadeEFE.step_decomposition`. This avoids introducing a parallel scoring
functional.

Synthetic controls:

- `independent_information_zero`: uniform latent prior with an observation
  independent of the latent has joint MI zero;
- `informative_information_eq_log_two`: a deterministic identity observation
  of a uniform Bool latent has MI `log 2`;
- `informative_omitting_information_is_false`: in that informative model,
  risk plus ambiguity cannot equal expected negative log preference when the
  nonzero information term is omitted.

These fixtures are mathematical controls, not runtime evidence. The packet
does not adopt a continuous parameter model, product-preference constant,
outer model, selection rule, or R20 binding.

## Build and axioms

Command, cwd `/home/joe/worktrees/mathlib4-aif-joint-identity`:

```text
lake build DarkTower.WarMachine.AIFJointObjectiveIdentity
```

Exit: `0`; `3356` jobs completed.

Printed axioms for the main identity and all controls:

```text
[propext, Classical.choice, Quot.sound]
```

No theorem in the new module uses `sorryAx`. The build replayed known
pre-existing `sorry` warnings from `Holes.lean`; none occurs in the new
module or its printed dependencies.

Build log:
`/home/joe/notes/wm-next/loop-plan/joint-identity/logs/build.log`  
SHA-256:
`3a113a8ec4cdb8a4db5634b423f1a3e8c61980254ff43baed5ab36e8a9e375f7`.

## Deliberately false omitted-information claim

Scratch:
`/home/joe/notes/wm-next/loop-plan/joint-identity/FalseOmittedInformation.lean`  
SHA-256:
`570389bf0fb3968e76e56cc769b37a7033ade01e2808401f50de17ed33432dcf`.

Command:

```text
lake env lean /home/joe/notes/wm-next/loop-plan/joint-identity/FalseOmittedInformation.lean
```

Expected exit: `1`. Lean reports that
`informative_omitting_information_is_false` has the negated equality type,
while the deliberate theorem requests the equality.

Log:
`/home/joe/notes/wm-next/loop-plan/joint-identity/logs/false-omitted-information.log`  
SHA-256:
`950cc787fa29fa6d8b64e0381026e1036106f69a242b0e35809f7631e5f50ca6`.

## Source checks

Commands:

```text
git diff --check
rg -n '\bsorry\b|sorryAx' DarkTower/WarMachine/AIFJointObjectiveIdentity.lean
git status --short
```

`git diff --check` exited 0 and the source scan found nothing. Module
SHA-256:
`575e081dde53bfa730da767ea49c5281073e8aa5a5df61e4a2607e15159df6f7`.

