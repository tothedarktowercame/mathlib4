import DarkTower.WarMachine.PreferenceDistributionWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.PreferenceDistributionWitness

noncomputable def pragmaticCost : Obs .people → ℝ := C .people (by decide)

-- Must fail: the vertex-local pragmatic cost is not normalized preference C.
/--
error: Type mismatch
  pragmaticCost
has type
  Obs Vertex.people → ℝ
but is expected to have type
  PreferenceDistribution Obs
-/
#guard_msgs in
def badPreference : PreferenceDistribution Obs := pragmaticCost
