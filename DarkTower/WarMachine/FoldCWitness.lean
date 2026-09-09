import DarkTower.WarMachine.F10RuledCarrier

namespace DarkTower.WarMachine.FoldCWitness

open Holes
open F10RuledCarrier

/-- Base preference on the ruled F10 outcome carrier. -/
def ruledBase : Outcome SeedObs → ℝ
  | ⟨.organization, .groundedChange⟩ => 3
  | _ => 0

/-- The runtime declaration currently marks no ruled-sum layer folded. -/
def runtimeFoldedLayers : List (PreferenceLayer (Outcome SeedObs)) := []

theorem foldC_runtimeFoldedLayers_eq_base :
    foldC ruledBase runtimeFoldedLayers = ruledBase := rfl

def addLayer : PreferenceLayer (Outcome SeedObs) where
  record := ⟨"add-one", .operatorDeclared, "F10 slice 5", "ordered-fold witness", false,
    "DarkTower/WarMachine/FoldCWitness.lean"⟩
  prefers := fun _ => 1
  compose := (· + ·)

def doubleLayer : PreferenceLayer (Outcome SeedObs) where
  record := ⟨"multiply-two", .operatorDeclared, "F10 slice 5", "ordered-fold witness", false,
    "DarkTower/WarMachine/FoldCWitness.lean"⟩
  prefers := fun _ => 2
  compose := (· * ·)

/-- `foldC` is an ordered left fold: add-one then multiply-by-two gives eight
at the ruled `groundedChange` outcome, while the reverse gives seven. -/
theorem foldC_order_is_observable :
    foldC ruledBase [addLayer, doubleLayer] (organisationOutcome .groundedChange) = 8 ∧
    foldC ruledBase [doubleLayer, addLayer] (organisationOutcome .groundedChange) = 7 := by
  norm_num [foldC, ruledBase, addLayer, doubleLayer, organisationOutcome]

end DarkTower.WarMachine.FoldCWitness
