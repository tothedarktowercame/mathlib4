import DarkTower.WarMachine.Holes

open DarkTower.WarMachine.Holes

inductive Observation where | clear
def Obs : Vertex → Type := fun _ => Observation
def oneOutcome : Outcome Obs := ⟨.evidence, .clear⟩

-- Must fail: one vertex-tagged outcome is not the fourteen-coordinate vector.
def badObservation : ObservationVector := oneOutcome
