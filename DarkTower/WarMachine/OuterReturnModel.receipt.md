# Outer return model execution receipt

- Date: 2026-10-24 UTC
- Base: `196285e3d5406afaa3f5c82d1181b135fa425f7f`
- Branch: `wm-outer-return-model`
- Worktree: `/home/joe/worktrees/mathlib4-outer-return-model`
- Module SHA-256: `97fb85a9117dceb1983718b05ddaeb5feb8fdd0ee7e35679913f8957cce09e69`
- Negative-control SHA-256: `b52f4acaeb3c62ef611e25732c93dcfa265320718c6909ae8afb71b75c50240e`

## Result

The model uses the dependent outcome `Sigma Result`: a supplied normalized
verdict kernel and, for each verdict, a supplied normalized joint result
kernel. `NonqualifyingSingleton` states the proposed discipline that every
nonqualifying verdict has exactly one not-applicable result; the probability
construction does not infer that discipline or invent its value.

Proved properties:

- the conditional joint and latent-integrated predictive are normalized;
- summing a result branch recovers its verdict probability exactly;
- integration reuses `CascadeEFE.push`;
- the old closed-only gate loses mass whenever a nonqualifying verdict has
  positive probability;
- a synthetic shared finite latent gives joint diagonal probability `1/2`,
  not the marginal product `1/4`;
- an observed not-applicable value is distinct from an unreported `Option.none`.

Consumer results are supplied jointly, so no independence is assumed. The
module chooses no weights, priors, preferences, kinds, truth authority, or
learning update. An exhaustion value remains only a proposed within-budget
label absent external checked evidence.

## Commands

1. `lake env lean DarkTower/WarMachine/OuterReturnModel.lean` — exit 0.
2. `lake build DarkTower.WarMachine.OuterReturnModel` — exit 0; 3360 jobs.
3. `lake env lean ~/notes/wm-next/loop-plan/outer-return-model/FalseClosedGateNormalised.lean`
   — expected exit 1 with goal `False`: rewriting the claimed mass-one gate
   with the proved half-mass control leaves `1/2 = 1`.

Imported `Holes.lean` reports its existing sorry warnings. This module has no
`sorry`, and its printed theorem axioms have no `sorryAx`.

## Axioms

The normalization, marginal, gating, and dependence theorems print only:
`propext`, `Classical.choice`, `Quot.sound`.

## Sources and boundary

- Parr et al. 2022, `refs/parr2022.txt:7214-7236,7295-7345`, equations
  7.9–7.11.
- Da Costa et al. 2020, `refs/dacosta2020.txt:809-822`, equation 15's explicit
  outcome-risk approximation boundary.
- Existing finite kernels and `CascadeEFE.push` at the pinned base above.

Conditional-kernel normalization is exact. The labels and dependent domains
are supplied modelling proposals, not source-mandated runtime semantics.
