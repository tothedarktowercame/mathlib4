import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.PredictionErrorWitness

open Holes

def observed : ObservationVector := ⟨fun _ => 1⟩
def predicted : Channel → ℝ := fun _ => 3

structure ErrorReference where
  observation : ℝ
  prediction : ℝ
  expectedError : ℝ

def errorReference : ErrorReference :=
  { observation := 1, prediction := 3, expectedError := -2 }

theorem signedDifferenceReference (k : Channel) :
    predictionError observed predicted k = errorReference.expectedError := by
  norm_num [errorReference, predictionError, observed, predicted]

theorem differsFromObservation (k : Channel) :
    predictionError observed predicted k ≠ observed.value k := by
  norm_num [predictionError, observed, predicted]

theorem differsFromPrediction (k : Channel) :
    predictionError observed predicted k ≠ predicted k := by
  norm_num [predictionError, observed, predicted]

end DarkTower.WarMachine.PredictionErrorWitness
