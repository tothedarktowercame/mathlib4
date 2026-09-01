import DarkTower.WarMachine.Holes

open DarkTower.WarMachine.Holes

def partialMeasurement : Channel → Option ℝ := fun
  | .annotationHealth => none
  | _ => some 0

-- Must fail: typed absence cannot be silently admitted as a complete vector.
def badObservation : ObservationVector := ⟨partialMeasurement⟩
