import DarkTower.WarMachine.FoldCWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.F10RuledCarrier
open DarkTower.WarMachine.FoldCWitness

-- Must fail: the two non-commuting layers make the ordered fold observable.
theorem foldC_order_insensitive :
    foldC ruledBase [addLayer, doubleLayer] =
      foldC ruledBase [doubleLayer, addLayer] := by
  funext o
  rfl
