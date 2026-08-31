import DarkTower.WarMachine.Holes

open DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.BeliefStateWitness

/-- The record-derived reference state uses a total channel-indexed carrier;
there is no channel for which mean or variance can be absent. -/
def reference : BeliefState :=
  { mean := fun _ => 0
    variance := fun _ => ⟨0.01, by norm_num⟩ }

example (k : Channel) : reference.mean k = 0 := rfl
example (k : Channel) : 0 ≤ (reference.variance k).value :=
  (reference.variance k).nonnegative

end DarkTower.WarMachine.BeliefStateWitness
