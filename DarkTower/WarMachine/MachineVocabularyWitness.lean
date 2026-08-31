import DarkTower.WarMachine.Holes

open Set
open DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.MachineVocabularyWitness

inductive Control where | observe | act | outside deriving DecidableEq

def U : ControlVocabulary Control :=
  ⟨{Control.observe, Control.act}⟩

def recordedPolicy : ControlPolicy U :=
  ⟨[.observe, .act], by simp [U]⟩

def temperature : AlivenessFactor := ⟨0.8, by norm_num⟩
def harmony : AlivenessFactor := ⟨0.6, by norm_num⟩
example : aliveness temperature harmony = 0.48 := by norm_num [aliveness, temperature, harmony]

example : actGate (some 1.2) (some (-0.8)) = .pass := by norm_num [actGate]
example : actGate none (some (-0.8)) = .abstainMissingLeg := by rfl

inductive OutcomeClass where | grounded | abstained
def recordedCohort : Cohort String Nat String OutcomeClass :=
  ⟨"wm-outer-loop-46-v1", "omni-jvm", 3, by decide,
   {OutcomeClass.grounded, OutcomeClass.abstained}, [1, 2, 3], by decide⟩

end DarkTower.WarMachine.MachineVocabularyWitness
