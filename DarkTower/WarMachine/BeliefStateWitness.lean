import DarkTower.WarMachine.Holes

open DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.BeliefStateWitness

/-- The C31 fixture fields kept adjacent to the constructed posterior. -/
structure BeliefReference where
  priorMean : ℝ
  priorVariance : ℝ
  posteriorMean : ℝ
  posteriorVariance : ℝ

def beliefReference : BeliefReference :=
  { priorMean := 0, priorVariance := 2,
    posteriorMean := 1, posteriorVariance := 1 }

/-- The record-derived posterior uses a total channel-indexed carrier;
there is no channel for which mean or variance can be absent. -/
def reference : BeliefState :=
  { mean := fun _ => beliefReference.posteriorMean
    variance := fun _ => ⟨beliefReference.posteriorVariance, by norm_num [beliefReference]⟩ }

theorem recordedPosterior (k : Channel) :
    reference.mean k = 1 ∧ (reference.variance k).value = 1 := by
  simp [reference, beliefReference]

end DarkTower.WarMachine.BeliefStateWitness
