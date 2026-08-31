import DarkTower.WarMachine.PrecisionWitness

namespace DarkTower.WarMachine.PrecisionNegative

open Holes

def signedError : Channel → ℝ := fun _ => -1

-- Negative control: a signed prediction-error map is not a precision map.
def badPrecision : PrecisionMap := signedError

end DarkTower.WarMachine.PrecisionNegative
