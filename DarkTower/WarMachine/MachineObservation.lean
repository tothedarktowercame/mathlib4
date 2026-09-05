import DarkTower.WarMachine.Holes

/-!
# The machine structured observation o

This states the fourteen-channel construction in `observe`
(`futon2:src/futon2/aif/observation.clj:103-146`), its provenance envelope
(`futon2:src/futon2/aif/observation.clj:42-101`), and the guarded vector
boundary (`futon2:src/futon2/aif/observation.clj:148-158`). It deliberately
does NOT refine `Holes.ObservationVector.value` to `[0,1]`: only
`sorry-count-norm` and `coupling-density` have upper clamps, and no channel has
a constructed lower clamp (`futon2:src/futon2/aif/observation.clj:120-145`).
-/

namespace DarkTower.WarMachine.MachineObservation

open DarkTower.WarMachine.Holes

inductive MeasurementVariant | observed | absent deriving DecidableEq, Repr

structure ObservationEnvelope where
  variant : Channel → MeasurementVariant
  value : Channel → ℝ

/-- The composite carrier: a total `ObservationVector` paired with the tagged
absence envelope which records the same numeric coordinate. -/
def machineObservation (values : Channel → ℝ)
    (variants : Channel → MeasurementVariant) :
    ObservationVector × ObservationEnvelope :=
  (⟨values⟩, ⟨variants, values⟩)

def BoundedObservation (o : ObservationVector) : Prop :=
  ∀ channel, 0 ≤ o.value channel ∧ o.value channel ≤ 1

def upperClamp (x : ℝ) : ℝ := min 1 x

theorem upperClamp_le_one (x : ℝ) : upperClamp x ≤ 1 := by
  simp [upperClamp]

def CoercionPromise (o : ObservationVector) (envelope : ObservationEnvelope)
    (channel : Channel) : Prop :=
  envelope.variant channel = .absent →
    envelope.value channel = 0 ∧ o.value channel = 0

def activeRepoInputsComplete (activeRepos totalRepos : Option ℝ) : Prop :=
  activeRepos.isSome ∧ totalRepos.isSome

theorem incompleteActiveRepoSummaryDoesNotEstablishPromise (active : ℝ) :
    ¬ activeRepoInputsComplete (some active) none := by
  simp [activeRepoInputsComplete]

def EnvelopeMatches (o : ObservationVector) (envelope : ObservationEnvelope) : Prop :=
  envelope.value = o.value

def senseToVector (o : ObservationVector) (envelope : ObservationEnvelope)
    (_matching : EnvelopeMatches o envelope) : List ℝ :=
  Channel.all.map o.value

theorem senseToVectorRequiresMatchingEnvelope (o : ObservationVector)
    (envelope : ObservationEnvelope) (h : EnvelopeMatches o envelope) :
    envelope.value = o.value := h

end DarkTower.WarMachine.MachineObservation
