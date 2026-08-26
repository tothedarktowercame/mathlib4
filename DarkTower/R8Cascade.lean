import DarkTower.BV

/-!
# A hand-built cascade as a BV structure: the R8 build sequence

Joe, 2026-08-26: *"we've also at times thought about cascades as BV diagrams …
Another strategy for us could be to hand build an example around our R8 etc
items, and develop the dependency and build sequence as a diagram, backed by
patterns — which would make it a cascade."*

This is that example, and it is the first cascade in the stack written at
**policy grade**: `π` is the whole structure, not an atomic action.

## Status: TERMS ELABORATE; FULL BUILD UNRUN

`Mathlib` is not built in this checkout (`.lake/build/lib/Mathlib/` is empty),
so `lake build` has not been run here.

What HAS been checked (2026-08-26): every definition below was elaborated by a
real Lean elaborator against a faithful transcription of the `DarkTower.BV`
inductive, using the toolchain at `/home/joe/code/apm-lean` (v4.29.0-rc8, which
carries a built Mathlib as a package). All terms typecheck and `open BV`
resolves the constructors as written. The cascade terms use nothing from
Mathlib, so that check covers their whole content.

What has NOT been checked: that this file builds in-place under this checkout's
v4.31.0-rc1 with `import DarkTower.BV`, which pulls `import Mathlib`. That is a
question about the surrounding build, not about the terms. To settle it:

    lake exe cache get && lake build DarkTower.R8Cascade

(`cache get` fetches prebuilt oleans; per `AGENTS.md`, Mathlib is not to be
rebuilt locally.)

## Why the connectives carry the argument

* `seq` is **non-commutative** — it is the only connective that says *this
  before that*, which is the whole content of a build order.
* `copar` is a conjunction of requirements with **no order**: work that may
  proceed alongside, both needed.
* `par` is an **alternative**: exactly one branch is taken.

So a build plan written in BV cannot hide a sequencing claim it has not made.
An ordering that turns out to be arbitrary shows up as a `copar` that was
written as a `seq`.
-/

namespace DarkTower
namespace R8

open BV

/-- Atoms are shelf pattern ids. Backing every step by a pattern is what makes
this a *cascade* rather than a task list — each atom names the pattern that
warrants the step, and every id below was checked against
`minilm_pattern_embeddings.json` on 2026-08-26. -/
abbrev Step := String

/-- The choice that gates everything downstream: what does `π` range over?
Written as `par` because these are alternatives — the stack has two candidate
answers already built, BV's own `seq` and the constructor's semilattice
`:descent`, and they give different rollouts and therefore different `G`. -/
def piRangesOver : BV Step :=
  par (atom "orchestration/pattern-warranted-choice-point")
      (atom "structure/hinge-point")

/-- `fold-eval` (b): the multi-move rollout over the cascade, unbuilt as of
2026-08-26. Depends on `piRangesOver` having been settled. -/
def evalB : BV Step :=
  atom "aif/expected-free-energy-scorecard"

/-- R8's three registration gates, in the order its promotion test states them:
mismatch emitted per tick; a tick run replayed both ways; the null control
fails. These are genuinely sequential — each reads the previous one's output. -/
def r8Gates : BV Step :=
  seq (atom "war-room/wr-27-a-loop-is-born-instrumented-for-its-gain")
      (seq (atom "aif/no-self-certification")
           (atom "aif/admissibility"))

/-- The policy-grade spine: settle what `π` is, then build the rollout, then
run the gates. Nothing here may be reordered. -/
def spine : BV Step :=
  seq piRangesOver (seq evalB r8Gates)

/-- Two probes that need no part of the spine and may run alongside it.
`copar`, not `seq`: writing these in sequence would assert a dependency that
does not exist.

* the R14 audited negative — runnable against the 58-attempt archive today;
* the action-grain R10 run — tests whether `wm-outer-loop-*` reaches
  `fold-realized`'s enactment path at all, which is a one-run question. -/
def parallelProbes : BV Step :=
  copar (atom "invariant-coherence/state-snapshot-witness")
        (atom "exotic/live-sync-source-truth")

/-- The whole cascade. -/
def r8Cascade : BV Step :=
  copar parallelProbes spine

end R8
end DarkTower
