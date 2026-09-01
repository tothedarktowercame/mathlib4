import DarkTower.WarMachine.PrecisionWitness

namespace DarkTower.WarMachine.PrecisionNegative

open Holes

def signedError : Channel → ℝ := fun _ => -1

-- Negative control: a signed prediction-error map is not a precision map.
/--
error: Type mismatch
  signedError
has type
  Channel → ℝ
but is expected to have type
  PrecisionMap
-/
#guard_msgs in
def badPrecision : PrecisionMap := signedError

end DarkTower.WarMachine.PrecisionNegative
