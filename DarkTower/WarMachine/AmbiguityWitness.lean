import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.AmbiguityWitness

open Holes

inductive Policy where | inspect deriving DecidableEq
inductive State where | certain deriving DecidableEq
inductive Observation where | seen deriving DecidableEq

def predictedState : ProbabilityKernel Policy State where
  support := fun _ => [.certain]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

def observationModel : observationKernel State Observation where
  support := fun _ => [.seen]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

structure AmbiguityReference where
  predictedStateMass : ℝ
  observationMass : ℝ
  expectedAmbiguity : ℝ

def ambiguityReference : AmbiguityReference :=
  { predictedStateMass := 1, observationMass := 1, expectedAmbiguity := 0 }

/-- Independent fixture: a point-mass observation has Shannon entropy zero. -/
theorem pointMassAmbiguity :
    ambiguity predictedState observationModel .inspect =
      ambiguityReference.expectedAmbiguity := by
  norm_num [ambiguityReference, ambiguity, observationEntropy, predictedState, observationModel]

end DarkTower.WarMachine.AmbiguityWitness
