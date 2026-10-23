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
