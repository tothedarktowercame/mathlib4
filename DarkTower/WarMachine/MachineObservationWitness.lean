import DarkTower.WarMachine.MachineObservation

/-! # Reference witnesses for the structured observation construction

Every `-expected` in `futon2:holes/labs/wm-contract/f8_observation_readback.clj`
is transcribed from a theorem named here. -/

namespace DarkTower.WarMachine.MachineObservationWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineObservation

def emptyValues : Channel → ℝ := fun _ => 0
def absentVariants : Channel → MeasurementVariant := fun _ => .absent

/-- `(observe {})` returns fourteen coordinates, all zero.  The content is the
count: `machineObservation` is total over `Channel` by construction, so what is
measurable is that `Channel.all` has fourteen entries and the readback's vector
has the same length. -/
theorem emptyObservationHasFourteenZeros :
    (Channel.all.map (machineObservation emptyValues absentVariants).1.value)
      = List.replicate 14 (0 : ℝ) := by
  norm_num [machineObservation, Channel.all, emptyValues, List.replicate]

/-! ## The clamped channels — the part of the `[0,1]` claim that holds -/

theorem clampAtCap : upperClamp 1 = 1 := by norm_num [upperClamp]
theorem clampAboveCapTwo : upperClamp 2 = 1 := by norm_num [upperClamp]
theorem clampAboveCapFive : upperClamp 5 = 1 := by norm_num [upperClamp]

/-- `:sorry-count-norm` and `:coupling-density` are bounded above whatever the
raw reading is. -/
theorem sorryCountNormIsBoundedAbove (raw : Channel → ℝ) :
    (clampAtClamped raw).value .sorryCountNorm ≤ 1 :=
  clampedChannelsAreBoundedAbove raw _ (by decide)

theorem couplingDensityIsBoundedAbove (raw : Channel → ℝ) :
    (clampAtClamped raw).value .couplingDensity ≤ 1 :=
  clampedChannelsAreBoundedAbove raw _ (by decide)

/-- …and `:stack-pct` is not: the same construction passes it straight through,
because it is not in `clampedChannels`. -/
theorem stackPctIsNotClamped (raw : Channel → ℝ) :
    (clampAtClamped raw).value .stackPct = raw .stackPct := by
  simp only [clampAtClamped]
  rw [if_neg (by decide)]

/-! ## The three measured counterexamples to `BoundedObservation` -/

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

/-! ## The coercion promise, and the one-character asymmetry -/

/-- A `:summary` present without `:total-repos` yields no reading at
`:active-repo-ratio` — `observe` raises at `observation.clj:129`. -/
theorem incompleteActiveRepoSummaryHasNoReading (active : ℝ) :
    activeRepoReading (some active) none = none := rfl

/-- The same missing key at `:coupling-density` yields the promised `0`,
because `observation.clj:134` supplies a default. -/
theorem incompleteCouplingSummaryReadsZero (edges : ℝ) :
    couplingDensityReading (some edges) none = some 0 := by
  norm_num [couplingDensityReading]

/-- The promise the envelope carries at that channel is not kept. -/
theorem readbackCoercionPromiseIsBroken
    (envelope : ObservationEnvelope) (reading : Channel → Option ℝ)
    (hAbsent : envelope.variant .activeRepoRatio = .absent)
    (hCoercedTo : envelope.value .activeRepoRatio = 0)
    (hNoReading : reading .activeRepoRatio = none) :
    EnvelopePromises envelope .activeRepoRatio ∧
      ¬ PromiseKept reading envelope .activeRepoRatio :=
  incompleteActiveRepoSummaryBreaksTheCoercionPromise envelope reading
    hAbsent hCoercedTo hNoReading

/-! ## The envelope variants and the vector boundary -/

theorem observedVariantReference :
    (machineObservation emptyValues (fun _ => .observed)).2.variant .loopHealth =
      .observed := rfl

theorem absentVariantReference :
    (machineObservation emptyValues absentVariants).2.variant .loopHealth =
      .absent := rfl

def emptyEnvelope : ObservationEnvelope := envelopeOf emptyValues absentVariants

/-- The envelope of `(observe {:loop-health {:overall 0.0}})`: `.loopHealth`
observed, the other thirteen absent, and EVERY coordinate still `0`. -/
def loopHealthObservedEnvelope : ObservationEnvelope :=
  envelopeOf emptyValues (fun c => if c = .loopHealth then .observed else .absent)

/-- The pair the readback refuses agrees at every numeric coordinate. -/
theorem readbackRefusalPairAgreesNumerically :
    emptyEnvelope.value = loopHealthObservedEnvelope.value := rfl

/-- …and is refused anyway, on the variant.  This is why `EnvelopeMatches`
compares the whole tagged map: a value-only test would accept exactly this pair,
and `sense->vector` throws on it (`runs/F8-observe/clojure-readback.txt`). -/
theorem readbackRefusalPairIsRefused :
    ¬ EnvelopeMatches emptyEnvelope loopHealthObservedEnvelope := by
  rintro ⟨hv, -⟩
  have h : emptyEnvelope.variant .loopHealth
      = loopHealthObservedEnvelope.variant .loopHealth := by rw [hv]
  simp only [emptyEnvelope, loopHealthObservedEnvelope, envelopeOf, absentVariants] at h
  exact absurd h (by decide)

theorem matchingEnvelopeVectorLength :
    (senseToVector ⟨emptyValues⟩ emptyEnvelope emptyEnvelope ⟨rfl, rfl⟩).length = 14 := by
  norm_num [senseToVector, Channel.all]

end DarkTower.WarMachine.MachineObservationWitness
