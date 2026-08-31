import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.ChannelWitness
open Holes

/-- The C58 record's fourteen named coordinates, in declaration order. -/
theorem declaredVocabulary : Channel.all =
    [.loopHealth, .supportCoverage, .attackCoverage, .missionHealth, .stackPct,
     .consultingPct, .portfolioPct, .mathematicsPct, .activeRepoRatio,
     .sorryCountNorm, .couplingDensity, .ticksFiringRatio, .depositingSignal,
     .annotationHealth] := rfl

example : Channel.all.length = 14 := by native_decide

end DarkTower.WarMachine.ChannelWitness
