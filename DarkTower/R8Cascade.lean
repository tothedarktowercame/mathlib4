import DarkTower.BV

/-!
# A hand-built cascade as a BV structure: the R8 build sequence

Joe, 2026-08-26: *"we've also at times thought about cascades as BV diagrams …
Another strategy for us could be to hand build an example around our R8 etc
items, and develop the dependency and build sequence as a diagram, backed by
patterns — which would make it a cascade."*

This is that example, and it is the first cascade in the stack written at
**policy grade**: `π` is the whole structure, not an atomic action.

## Status: TERMS CHECKED against the real `DarkTower.BV`

Every definition below was elaborated (2026-08-26) against `DarkTower/BV.lean`
itself — its `BV`, `Cong`, `Step` and theorems, not a transcription. Exit 0.

The route matters, because `lake build` still cannot run here. This checkout is
on the fork branch `darktower`, so `lake exe cache get` finds no upstream CI
build for its commit: it attempted 8481 files from two caches and downloaded
**zero**. `Mathlib.olean` is absent and 3731 of ~8481 modules are built, so
`import Mathlib` cannot resolve, and rebuilding is what `AGENTS.md` forbids.

**But `BV.lean` does not need Mathlib.** With `import Mathlib` and the unused
`open CategoryTheory` removed it elaborates standalone in seconds, all theorems
included. That is how these terms were checked, and it suggests a one-line
improvement to `BV.lean` — not made here, since other `DarkTower` files may rely
on it re-exporting Mathlib.

What remains unchecked: `lake build DarkTower.R8Cascade` in place, which is blocked
on the substrate above rather than on anything in this file.

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
