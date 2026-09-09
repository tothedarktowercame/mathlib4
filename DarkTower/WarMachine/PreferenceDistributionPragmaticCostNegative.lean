import DarkTower.WarMachine.PreferenceDistributionWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.PreferenceDistributionWitness

noncomputable def pragmaticCost : Obs .nouns → ℝ := C .nouns (by decide)

-- Must fail: the vertex-local pragmatic cost is not normalized preference C.
/--
error: Type mismatch
  pragmaticCost
has type
  Obs Vertex.nouns → ℝ
but is expected to have type
  PreferenceDistribution Obs
-/
#guard_msgs in
def badPreference : PreferenceDistribution Obs := pragmaticCost
