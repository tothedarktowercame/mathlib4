+# Neutral detail receipt

Date: 2026-10-24 UTC. Author: codex-9.

- Branch: `wm-aif-neutral-detail`
- Worktree: `/home/joe/worktrees/mathlib4-aif-neutral-detail`
- Base: `8e5594602e3f982f3f53d0982a5bbad6afbedd57`
- Code: `e2b9b12239f361516d04044d2a11996460255901`

## Scope and result

The new `AIFNeutralDetail.lean` constructs a normalized, strictly positive
product preference from symbolic normalized positive `C : Y` and the uniform
distribution on one finite nonempty fixed `W`. For an arbitrary normalized
joint prediction on `Y × W` (no independence; zero/unreachable pairs allowed),
`neutral_detail_cost` proves with existing `CascadeEFE.pragmaticCost`:

```text
cost(q, C × U_W) = cost(marginalY(q), C) + log(card W).
```

`same_detail_order_iff` proves pairwise order preservation for two candidates
on the same `W` after subtracting arbitrary separately supplied information
terms. It assumes no MI preservation.

Controls: `correlated` has zero off-diagonal masses and satisfies the identity;
the no-constant equality is false for `card W = 2`; Unit versus Bool detail
domains give constants 0 versus `log 2`, so differing cardinalities do not
license cancellation.

The product choice is proposed mathematics, not mandated/adopted preference.
Parr anchors read: `refs/parr2022.txt:6743-6747,13534-13568`. The module
preserves the outcome-risk qualification of `AIFJointObjectiveIdentity`.
No scorer/R20/runtime definition changed.

## Gates

`lake build DarkTower.WarMachine.AIFNeutralDetail`: exit 0, 3357 jobs.
Printed axioms for main identity/order/controls: only `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx`.

Build log SHA-256:
`b24bb9045abb1466263494debc0a0dd5ea63141e8374794e5e51b944da0c5722`.

Deliberate false command:
`lake env lean ~/notes/wm-next/loop-plan/neutral-detail/FalseNoConstant.lean`;
exit 1 with equality-versus-inequality type mismatch.
Log SHA-256:
`f01b7463410fa01d5ed4630fea4079fd45d125b7509d726b6622f98f934ce03c`.

`git diff --check` exited 0; source scan found no `sorry`/`sorryAx`.
Module SHA-256:
`41a37cb185c5fc263aa4f661263b6e79e57a97852309b39e9cce8721223a1f89`.

