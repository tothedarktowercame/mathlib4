import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.HaveWantArrowWitness

open Holes

inductive Endpoint where
  | beliefMass
  | supportCoverage
  | witnessedCoverage
  deriving DecidableEq

def first : HaveWantArrow Endpoint :=
  ⟨.beliefMass, .supportCoverage, .constructed⟩

def second : HaveWantArrow Endpoint :=
  ⟨.supportCoverage, .witnessedCoverage, .open⟩

/-- The record-derived fixture composes because its shared endpoint is exact. -/
def recordedComposition : HaveWantArrowComposition first second :=
  ⟨rfl⟩

end DarkTower.WarMachine.HaveWantArrowWitness
