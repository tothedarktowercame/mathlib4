import DarkTower.WarMachine.Holes

open DarkTower.WarMachine.Holes

def partialMeasurement : Channel → Option ℝ := fun
  | .annotationHealth => none
  | _ => some 0

-- Must fail: typed absence cannot be silently admitted as a complete vector.
/--
error: Application type mismatch: The argument
  partialMeasurement
has type
  Channel → Option ℝ
but is expected to have type
  Channel → ℝ
in the application
  { value := partialMeasurement }
-/
#guard_msgs in
def badObservation : ObservationVector := ⟨partialMeasurement⟩
