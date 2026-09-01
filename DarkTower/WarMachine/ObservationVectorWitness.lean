import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.ObservationVectorWitness

open Holes

/-- Hand-derived coordinate fixture in declaration order. The function is
total over `Channel`, so every one of the fourteen constructors has a value. -/
def observed : ObservationVector := ⟨fun
  | .loopHealth => 0 | .supportCoverage => 1 | .attackCoverage => 2
  | .missionHealth => 3 | .stackPct => 4 | .consultingPct => 5
  | .portfolioPct => 6 | .mathematicsPct => 7 | .activeRepoRatio => 8
  | .sorryCountNorm => 9 | .couplingDensity => 10 | .ticksFiringRatio => 11
  | .depositingSignal => 12 | .annotationHealth => 13⟩

theorem completeCoordinateValues :
    Channel.all.map observed.value = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := rfl

end DarkTower.WarMachine.ObservationVectorWitness
