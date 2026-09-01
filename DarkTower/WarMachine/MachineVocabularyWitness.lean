import DarkTower.WarMachine.Holes

open Set
open DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.MachineVocabularyWitness

inductive Control where | observe | act | outside deriving DecidableEq

def U : ControlVocabulary Control :=
  ⟨{Control.observe, Control.act}⟩

def recordedPolicy : ControlPolicy U :=
  ⟨[.observe, .act], by simp [U]⟩

theorem recordedControlPolicy : recordedPolicy.controls = [Control.observe, Control.act] := rfl

def temperature : AlivenessFactor := ⟨0.8, by norm_num⟩
def harmony : AlivenessFactor := ⟨0.6, by norm_num⟩

structure AlivenessReference where
  temperature : ℝ
  harmony : ℝ
  expectedAliveness : ℝ

def alivenessReference : AlivenessReference :=
  { temperature := 0.8, harmony := 0.6, expectedAliveness := 0.48 }

theorem recordedAliveness :
    aliveness temperature harmony = alivenessReference.expectedAliveness := by
  norm_num [alivenessReference, aliveness, temperature, harmony]

structure ActGateReference where
  passingCascade : ℝ
  passingCoverageDelta : ℝ
  missingCoverageDelta : ℝ

def actGateReference : ActGateReference :=
  { passingCascade := 1.2, passingCoverageDelta := -0.8,
    missingCoverageDelta := -0.8 }

theorem recordedActGatePass :
    actGate (some actGateReference.passingCascade)
      (some actGateReference.passingCoverageDelta) = .pass := by
  norm_num [actGateReference, actGate]

theorem recordedActGateMissing :
    actGate none (some actGateReference.missingCoverageDelta) = .abstainMissingLeg := by
  rfl

inductive OutcomeClass where | grounded | abstained
def recordedCohort : Cohort String Nat String OutcomeClass :=
  ⟨"wm-outer-loop-46-v1", "omni-jvm", 3, by decide,
   {OutcomeClass.grounded, OutcomeClass.abstained}, [1, 2, 3], by decide⟩

theorem recordedCohortFields :
    recordedCohort.id = "wm-outer-loop-46-v1" ∧
    recordedCohort.semanticEpoch = "omni-jvm" ∧
    recordedCohort.stoppingTarget = 3 ∧
    recordedCohort.attempts = [1, 2, 3] := by
  decide

end DarkTower.WarMachine.MachineVocabularyWitness
