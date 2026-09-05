import DarkTower.WarMachine.MachineObservation

/-! # Reference witnesses for the structured observation construction -/

namespace DarkTower.WarMachine.MachineObservationWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineObservation

def emptyValues : Channel → ℝ := fun _ => 0
def absentVariants : Channel → MeasurementVariant := fun _ => .absent

theorem emptyObservationHasFourteenZeros :
    (machineObservation emptyValues absentVariants).1.value = emptyValues ∧
    (Channel.all.map (machineObservation emptyValues absentVariants).1.value).length = 14 := by
  norm_num [machineObservation, Channel.all, emptyValues]

theorem sorryAtCap : upperClamp 1 = 1 := by norm_num [upperClamp]
theorem sorryAboveCap : upperClamp 2 = 1 := by norm_num [upperClamp]
theorem couplingAtCap : upperClamp 1 = 1 := by norm_num [upperClamp]
theorem couplingAboveCap : upperClamp 5 = 1 := by norm_num [upperClamp]

def stackSeventy : ObservationVector := ⟨fun c => if c = .stackPct then 70 else 0⟩
def loopHealthNegativeThree : ObservationVector :=
  ⟨fun c => if c = .loopHealth then -3 else 0⟩
def activeRepoFive : ObservationVector :=
  ⟨fun c => if c = .activeRepoRatio then 5 else 0⟩

theorem stackSeventyIsUnbounded : ¬ BoundedObservation stackSeventy := by
  intro h
  have := (h .stackPct).2
  norm_num [stackSeventy] at this

theorem loopHealthNegativeThreeIsUnbounded :
    ¬ BoundedObservation loopHealthNegativeThree := by
  intro h
  have := (h .loopHealth).1
  norm_num [loopHealthNegativeThree] at this

theorem activeRepoFiveIsUnbounded : ¬ BoundedObservation activeRepoFive := by
  intro h
  have := (h .activeRepoRatio).2
  norm_num [activeRepoFive] at this

theorem observedVariantReference :
    (machineObservation emptyValues (fun _ => .observed)).2.variant .loopHealth =
      .observed := rfl

theorem absentVariantReference :
    (machineObservation emptyValues absentVariants).2.variant .loopHealth =
      .absent := rfl

theorem matchingEnvelopeVectorLength :
    let pair := machineObservation emptyValues absentVariants
    (senseToVector pair.1 pair.2 rfl).length = 14 := by
  norm_num [senseToVector, machineObservation, Channel.all]

theorem incompleteSummaryReference :
    ¬ activeRepoInputsComplete (some 3) none := by
  exact incompleteActiveRepoSummaryDoesNotEstablishPromise 3

end DarkTower.WarMachine.MachineObservationWitness
