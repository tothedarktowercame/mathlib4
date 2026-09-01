import DarkTower.WarMachine.PredictionErrorWitness

namespace DarkTower.WarMachine.PredictionErrorNegative

open Holes PredictionErrorWitness

-- Negative control: reversing observation and prediction must not preserve ε.
/--
error: unsolved goals
k : Channel
⊢ False
-/
#guard_msgs in
theorem reversedSignSlips (k : Channel) :
    predictionError observed predicted k = 2 := by
  norm_num [predictionError, observed, predicted]

end DarkTower.WarMachine.PredictionErrorNegative
