# O2 build receipt

- HEAD before commit: `f01d392afb345e6feccb1d8cd08c7de1fe34183e`
- Worktree: `/home/joe/worktrees/mathlib4-o2`
- Environment: Lean `v4.31.0-rc1`, shared primary `.lake` symlink as requested.
- Command run once: `lake build DarkTower.WarMachine.Proof2.OuterSelectionCanonicalG`
- Result: `Built DarkTower.WarMachine.Proof2.OuterSelectionCanonicalG (2.8s)`;
  `Build completed successfully (8519 jobs).`
- The module's five `#print axioms` reports list only standard
  `propext`, `Classical.choice`, and `Quot.sound`; no theorem depends on
  `sorryAx`.

The negative control is constructive rather than a failing build: the proved
`counterexample_G_frontier` and `counterexample_outer_frontier` exhibit the
same two policies with an equal canonical-G frontier and a unique outer
objective winner, respectively. Removing `lnE` from the outer objective makes
the latter theorem fail to elaborate, which is the named bad case.

## O2b follow-up

- HEAD before follow-up commit: `17543a07774fbb743a8f1f40bbae6195e6bdcef5`
- Command run once after the revision: `lake build
  DarkTower.WarMachine.Proof2.OuterSelectionCanonicalG`
- Result: `Built DarkTower.WarMachine.Proof2.OuterSelectionCanonicalG (2.2s)`;
  `Build completed successfully (8519 jobs).`
- Negative control run once: temporarily asserted the G-frontier equality for
  `counterA`/`counterB` without the constant-lnE condition. Lean exited 1;
  `counterexample_outer_frontier` and `counterexample_G_frontier` are the
  retained constructive witness of that failed assertion. The temporary
  assertion was removed before the green build.
- The revised `#print axioms` entries report only `propext`,
  `Classical.choice`, and `Quot.sound`; no `sorryAx`.

## Review additions (claude-7)

- HEAD before review commit: `741925ac784cceb3a9852b902285754b62c72c64`
- Added `mem_assessedPairs` (refusal exclusion on any menu, not only a
  singleton), `assessedPairs_ok`, and `canonicalSelection_agrees` (the
  `compareAtHorizonN` = `.ok outerG` hypothesis, positive gamma and constant
  lnE give `canonicalSelection = outerSelection gamma`). O2b had removed the
  earlier agreement theorem without a replacement tying the canonical side in.
- Command run once: `lake build DarkTower.WarMachine.Proof2.OuterSelectionCanonicalG`
  → `Build completed successfully (8519 jobs).` No warnings in this module;
  all `#print axioms` list only `propext`, `Classical.choice`, `Quot.sound`.
- Negative control for dropping the lnE hypothesis: the existing
  `counterexample_outer_frontier` / `counterexample_G_frontier` pair is a
  menu on which the conclusion of `canonicalSelection_agrees` without `hlnE`
  is false (outer frontier `[counterB]`, G frontier `[counterA, counterB]`).
