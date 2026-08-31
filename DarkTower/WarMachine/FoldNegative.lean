import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.FoldNegative

open Holes

-- Intentionally rejected: the common Fold boundary requires the policy-hole
-- field even when its value would be an empty list.
def malformed : Fold Unit Unit := ⟨(), none⟩

end DarkTower.WarMachine.FoldNegative
