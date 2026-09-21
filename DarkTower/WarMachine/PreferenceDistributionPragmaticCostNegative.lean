import DarkTower.WarMachine.PreferenceDistributionWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.PreferenceDistributionWitness

-- C591 closed 2026-09-21: `C` now states the ruled time-indexed family
-- (terminal member, step index, elsewhere family — values as parameters).
-- A fully applied step of that family is still a vertex-local function,
-- which is exactly what this negative control needs: local, not the
-- normalized global preference.
noncomputable def pragmaticCost : Obs .nouns → ℝ :=
  C .nouns (by decide) (fun _ => 0) 0 (fun _ _ => 0) 0

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
