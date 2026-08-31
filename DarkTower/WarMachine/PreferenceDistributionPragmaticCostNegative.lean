import DarkTower.WarMachine.PreferenceDistributionWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.PreferenceDistributionWitness

noncomputable def pragmaticCost : Obs .people → ℝ := C .people (by decide)

-- Must fail: the vertex-local pragmatic cost is not normalized preference C.
def badPreference : PreferenceDistribution Obs := pragmaticCost
