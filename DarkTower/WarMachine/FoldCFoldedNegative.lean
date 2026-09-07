import DarkTower.WarMachine.FoldCWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.F10RuledCarrier
open DarkTower.WarMachine.FoldCWitness

-- Must fail: folding a layer marked not folded does change the base.
theorem foldC_unfolded_layer_leaves_base :
    foldC ruledBase [addLayer] = ruledBase := by
  funext o
  rfl
