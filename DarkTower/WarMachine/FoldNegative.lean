import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.FoldNegative

open Holes

-- Intentionally rejected: the common Fold boundary requires the policy-hole
-- field even when its value would be an empty list.
/--
error: Insufficient number of fields for `⟨...⟩` constructor: Constructor `DarkTower.WarMachine.Holes.Fold.mk` has 3 explicit field, but only 2 were provided
-/
#guard_msgs in
def malformed : Fold Unit Unit := ⟨(), none⟩

end DarkTower.WarMachine.FoldNegative
