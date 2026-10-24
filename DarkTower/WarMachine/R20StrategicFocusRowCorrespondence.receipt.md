# Finite strategic-focus supplied-value correspondence receipt

Date: 2026-10-24 UTC  
Author: codex-9; independent reviewer: codex-11  
Branch: `wm-strategic-focus-formal`  
Worktree: `/home/joe/worktrees/mathlib4-strategic-focus-formal`

## Pins

- Base/darktower: `b05f3d561a1a325aee87ac39d92fc0f2a0d219ab`
- Code commit: `644c3fa79addbe1223d296b296db058d88a7c525`
- Module SHA-256: `5bce78ade2845468b08343c7c0d3fab5e51e9cac2116a111085e7d3bf96621a2`
- Deliberate negative source SHA-256: `442fcec2730203a76d8bec876184b49c9e6d307692f4d8a3608cd61a0b0b418b`
- `.lake` verified as symlink to `/home/joe/code/mathlib4/.lake` before build.

The accepted precursor was
`/home/joe/notes/wm-next/strategic-focus-formal/SuppliedRelation.lean`, reviewed
in `independent-review.md`. The current predicate is
`R15StrategicTarget.StrategicTickConforms` at the pinned base.

## Result

`adaptCandidates` is total and all-or-nothing. Its exact theorem is:

```text
adaptCandidates raw = some out ↔ List.Forall₂ CandidateAdapts raw out
```

`CandidateAdapts` preserves position, target, supplied relation and scored
class. Consequently absence anywhere refuses the whole list; it cannot be
filtered. A present wrong class remains in the adapted tick and is rejected by
the unchanged `StrategicTickConforms`.

`adapted_tick_conforms_iff` proves that a successfully adapted tick conforms
iff every supplied relation is present with the matching scorer class and the
unchanged supplied preference function satisfies the existing in-horizon
schedule equation. The accepted singleton theorem is recovered as an instance.
Empty candidates and horizon zero retain the existing predicate behavior.
The positive multi-candidate control includes supplied `.other 4`; this is only
a Lean value and makes no runtime unknown-to-other decoding claim.

## Positive build

Command, cwd `/home/joe/worktrees/mathlib4-strategic-focus-formal`:

```text
lake build DarkTower.WarMachine.R20StrategicFocusRowCorrespondence
```

Exit `0`:

```text
ℹ [2949/2949] Built DarkTower.WarMachine.R20StrategicFocusRowCorrespondence (1.3s)
Build completed successfully (2949 jobs).
```

The printed axioms are:

- `adaptCandidates_eq_some_iff`: `propext`, `Quot.sound`;
- the conformance, singleton, positive, wrong-class, wrong-schedule, empty-list
  conformance and zero-horizon theorems: at most `propext`,
  `Classical.choice`, `Quot.sound`;
- missing-middle and empty-list adaptation controls: no axioms.

No theorem reports `sorryAx`. Source scan:

```text
rg -n "sorry|admit|axiom" DarkTower/WarMachine/R20StrategicFocusRowCorrespondence.lean
```

Exit `0`; matches are only the eleven `#print axioms` commands.

`git diff --check` exited `0` before the code commit.

## Deliberate negative

File: `/home/joe/notes/wm-next/strategic-focus-formal/FiniteNegative.lean`.
It falsely asserts that a three-element input with an absent middle relation
adapts to the two present endpoints.

Command from the worktree:

```text
lake env lean /home/joe/notes/wm-next/strategic-focus-formal/FiniteNegative.lean
```

Exit `1`, expected. Lean reports at line 16:

```text
error: Tactic `rfl` failed: The left-hand side ... is not definitionally equal
to the right-hand side ...
```

The displayed goal retains all three supplied inputs on the left and the
illegally shortened two-element result on the right. This discriminates the
required refusal from filtering.

## Scope

This module proves finite supplied-value correspondence only. It does not
provide a runtime decoder, target identity encoding, relation provenance,
off-facet policy, full strategic runtime row, graph wiring, or `RunCertified`.
No existing predicate was changed. No nonempty-list or positive-horizon premise
was added. No Clojure, runtime, click, reload, graph, or live state was touched.
