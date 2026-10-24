# AIF report-encoding execution receipt

- UTC date: 2026-10-24
- Base: `549d1a13e7c1384cd7238a4240db4d5c3b196749`
- Branch: `wm-aif-report-encoding`
- Worktree: `/home/joe/worktrees/mathlib4-aif-report-encoding`
- Source SHA-256: `1276687c08566de2afe8944ccd956e6c224803595f3711bcd7bc964949e48ab6`
- Scratch negative SHA-256: `4ba25b311f5b639c92c76714f5668b68f8cdb5a1c483042288ee4fa36e6cef03`

## Scope

`information_report_encoding` post-composes an arbitrary finite conditional
observation kernel with a supplied deterministic injective function and proves
that the existing `CascadeEFE.information` is unchanged. The proof permits
zero masses and report values outside the encoding range. It proceeds through
proved outcome-mass, entropy, and ambiguity adapters; information is not
redefined.

Synthetic controls establish that Boolean relabelling preserves information,
a constant report loses the information in a revealed Boolean, and reporting
both independent latent bits has strictly more information than reporting only
the first bit. The last observation is an augmentation, not an encoding of the
first report alone.

This is finite probability algebra. It makes no runtime, provenance, R20,
preference, prior-authenticity, or action-selection claim.

## Commands and exits

From the worktree:

1. `lake env lean DarkTower/WarMachine/AIFReportEncoding.lean` — exit 0.
2. `lake build DarkTower.WarMachine.AIFReportEncoding` — exit 0; 3357 jobs,
   module built. Imported `Holes.lean` prints its pre-existing sorry warnings;
   none occurs in this module or its printed theorem axioms.
3. `lake env lean ~/notes/wm-next/loop-plan/report-encoding/FalseConstantLossless.lean`
   — expected exit 1. Lean rejects the final equality because positivity of the
   informative report yields `0 ≠ information`, while the false theorem needs
   `0 = information`.

## Axioms

Printed by the module for the main theorem and all three controls:

`[propext, Classical.choice, Quot.sound]`

There is no `sorryAx`.

## Sources

- Da Costa et al. 2020, `refs/dacosta2020.txt:787-835`, equations 14–16.
- Parr et al. 2022, `refs/parr2022.txt:7301-7325`, equation 7.11.
- Existing definitions: `CascadeEFE.information`, `joint`, `push`,
  `ambiguity`, and `information_entropy_identity` at base revision above.

The cited sources motivate the information term. Injective report preservation
is the probability-algebra condition required by the proposed representation,
not a literature-mandated observation encoding.
