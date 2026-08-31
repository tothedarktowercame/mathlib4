import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.HaveWantArrowNegative

open Holes

inductive Endpoint where | a | b | c | wrong deriving DecidableEq

def left : HaveWantArrow Endpoint := ⟨.a, .b, .constructed⟩
def malformedRight : HaveWantArrow Endpoint := ⟨.wrong, .c, .open⟩

-- This file is intentionally rejected: `.b` is not `.wrong`.
def malformed : HaveWantArrowComposition left malformedRight := ⟨rfl⟩

end DarkTower.WarMachine.HaveWantArrowNegative
