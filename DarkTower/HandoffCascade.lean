import DarkTower.BV

/-!
# The APM cascade handoff plan as a BV structure

The second specimen in the cascade-as-BV-diagram suite
(`p4ng/empirics-futon/NOTE-cascades-as-BV-diagrams.md`), and the one where the
encoding earned its keep: it caught a gate that the prose plan had flattened.

## What the prose said, and what was wrong with it

`PLAN-apm-cascade-demo-instance.md` gave a running order —
`H0 → H1 → H4 → H2 → H5 → H3` — narrated as a chain. Two of those arrows were
not dependencies:

* **H1** (archive the rendered packet) reads nothing H0 produces. Written as a
  `seq` it asserted an order nobody had claimed; it is a `copar`.
* **H2** was a single step. Fable (claude-19, 2026-08-26) split it, and the
  split is the interesting part:

  > *H2a (not yet dispatched) — the pipeline change in `snapshot-body` … I'll
  > dispatch it only if H2b shows (d) beating (a); if it doesn't, that's a
  > result to report, not a change to make.*

  That is a measurement followed by a genuine alternative, one branch of which
  is *do not make the change*. A `seq` cannot express it. In BV it is a `par`
  under a `seq`, and — the point — **the negative branch is a named term, not
  the absence of one.**

H2b has since returned: (d) beats (a) decisively (median position 18.5 → 3,
mean 17.04 → 4.04, top-5 15 → 50). So the `par` below is eliminated in favour
of `h2aDispatch`. It is left in the term because a plan that erases its
own decision points cannot be audited afterwards.

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

What remains unchecked: `lake build DarkTower.HandoffCascade` in place, which is blocked
on the substrate above rather than on anything in this file.

-/

namespace DarkTower
namespace Handoff

open BV

/-- Atoms are shelf pattern ids, checked against `minilm_pattern_embeddings.json`. -/
abbrev Step := String

/-- H0 — dry-run the expander. Carries a stopping condition: if expansion over a
real seed set is empty, nothing downstream is worth building. -/
def h0 : BV Step := atom "aif/no-self-certification"

/-- H1 — archive the rendered packet per attempt. Depends on nothing H0
produces; it closes the technote's own boundary section. -/
def h1 : BV Step := atom "measurement/ghost-as-typed-sorry"

/-- H4 — the f42a counterfactual, and its judgement. -/
def h4 : BV Step := atom "cascades/edges-earn-permanence"

/-- H2b — the offline ordering audit: score archived used-memory positions under
the delivered/hash order (a) against the combined order (d). -/
def h2b : BV Step := atom "invariant-coherence/state-snapshot-witness"

/-- H2a — the `snapshot-body` pipeline change. -/
def h2aDispatch : BV Step := atom "exotic/live-sync-source-truth"

/-- The other branch: report the negative and change nothing. Named, because an
unnamed negative branch is how a gate silently becomes a foregone conclusion. -/
def h2aReportOnly : BV Step := atom "aif/admissibility"

/-- H2, as Fable actually reads it: measure, then choose. -/
def h2 : BV Step := seq h2b (par h2aDispatch h2aReportOnly)

/-- H5 — populate the graph before exploiting it: multi-attach memories, author
pattern→pattern edges. A habit of writing, not a schema change. -/
def h5 : BV Step := atom "cascades/on-the-fly-cascade"

/-- H3 — wire the cascade, why-hop only, last and optional. -/
def h3 : BV Step := atom "orchestration/pattern-warranted-choice-point"

/-- The plan. H1 sits beside the spine rather than inside it. -/
def handoffCascade : BV Step :=
  copar h1 (seq h0 (seq h4 (seq h2 (seq h5 h3))))

end Handoff
end DarkTower
