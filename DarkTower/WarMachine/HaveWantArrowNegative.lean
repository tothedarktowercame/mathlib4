import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.HaveWantArrowNegative

open Holes

inductive Endpoint where | a | b | c | wrong deriving DecidableEq

def left : HaveWantArrow Endpoint := ⟨.a, .b, .constructed⟩
def malformedRight : HaveWantArrow Endpoint := ⟨.wrong, .c, .open⟩

-- This file is intentionally rejected: `.b` is not `.wrong`.
/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.6 = ?m.6
but is expected to have type
  left.target = malformedRight.source
in the application
  { endpointMatch := rfl }
-/
#guard_msgs in
def malformed : HaveWantArrowComposition left malformedRight := ⟨rfl⟩

end DarkTower.WarMachine.HaveWantArrowNegative
