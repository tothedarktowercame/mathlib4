# AIF objective composition execution receipt

- Date: 2026-10-24 UTC
- Base: `e7a7c03080153d459c2bace7dbe128b492da8b17`
- Branch: `wm-aif-objective-composition`
- Worktree: `/home/joe/worktrees/mathlib4-aif-objective-composition`
- Module SHA-256: `39091c41f23ae9ffa4fbe831d8b6ef19168842b6a0fc81251c345f7b596fedc9`
- Negative-control SHA-256: `87c52a4d2316f7ef9c96d2e552993137e8f695e33986d354612a563281d0f69a`

## Result and scope

`supplied_kernel_objective` composes the existing outcome-risk identity,
neutral-detail cost identity, and injective report-information theorem. For
supplied finite kernels and injective `x ↦ (g x, w x)`, it proves
`finiteRisk(encoded) + ambiguity(encoded) = pragmaticCost(g-marginal, C) -
information(raw report) + log |W|`.

The module proves the marginal adapter. Zero raw masses and unreachable
encoded pairs remain admitted. A same-detail two-candidate order theorem
cancels only the shared detail constant. A synthetic constant-`g`, informative
raw-report control proves that scored-only information changes the objective;
it makes no claim that an actual choice changes.

This is conditional finite probability algebra, not closure-model
implementation, runtime correspondence, preference adoption, or full AIF/R20
certification. Product preference remains a supplied domain proposal.

## Commands and exits

1. `lake env lean DarkTower/WarMachine/AIFObjectiveComposition.lean` — exit 0.
2. `lake build DarkTower.WarMachine.AIFObjectiveComposition` — exit 0; 3359
   jobs, focused module built.
3. `lake env lean ~/notes/wm-next/loop-plan/objective-composition/FalseCollapse.lean`
   — expected exit 1. Lean reports that the proved disequality has type
   `equality → False`, not the requested false equality.

Imported `Holes.lean` emits its pre-existing sorry warnings. The new module
contains no `sorry`; printed theorem axioms contain no `sorryAx`.

## Printed axioms

For the adapter, composition, order, and scored-collapse control the axioms are
`[propext, Classical.choice, Quot.sound]`.

## Source boundary

- Da Costa et al. 2020, `refs/dacosta2020.txt:787-835`, equations 14–16.
- Parr et al. 2022, `refs/parr2022.txt:7301-7325`, equation 7.11.
- Reviewed modules: `AIFJointObjectiveIdentity`, `AIFNeutralDetail`, and
  `AIFReportEncoding` at the base above.

Da Costa equation 15's outcome-risk substitution remains an approximation
boundary. The theorem is exact for the finite outcome-risk expression stated.
