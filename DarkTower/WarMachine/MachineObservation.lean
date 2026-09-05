import DarkTower.WarMachine.Holes

/-!
# The machine structured observation o

This states the fourteen-channel construction in `observe`
(`futon2:src/futon2/aif/observation.clj:103-146`), its provenance envelope
(`futon2:src/futon2/aif/observation.clj:42-101`), and the guarded vector
boundary (`futon2:src/futon2/aif/observation.clj:148-158`).

The registry row `:observe` is `:class :stack-defined` and its `:formal` line
is a boundary statement, not a formula, so there is no equation to transcribe.
What is stated instead is the construction and the three claims it makes about
itself — totality over `Channel`, the `[0,1]` bound, and the envelope's
`:coerced-to 0.0` — with the two that the implementation does not keep exhibited
rather than assumed away.

`Holes.ObservationVector.value` is DELIBERATELY NOT refined to `[0,1]`. Only
`sorry-count-norm` (`observation.clj:133`) and `coupling-density`
(`observation.clj:136-137`) are clamped, both from above only, and no channel is
clamped from below (`observation.clj:120-145`) — while the `[0,1]` range is
asserted at the namespace level (`:5-7`), on all fourteen channel lines
(`:18-32`) and in `observe`'s own docstring (`:105-106`). A bounded carrier here
would have stated a guarantee the machine does not make.

Two things are stated by a SIGNATURE rather than by a theorem, and the reason is
that a theorem would have had no content:
* `senseToVector` takes the matching proof as an argument, so the vector is
  unconstructible without it. A theorem `EnvelopeMatches o e → e.value = o.value`
  would unfold to `P → P` with the hypothesis as its own proof — the shape the
  slice-4 review deleted at mathlib4 `d7a45a358a`.
* `machineObservation` builds the envelope's coordinates from the same function
  as the vector's, so a pair it produces matches by construction. The refusal is
  about pairs a CALLER assembles, which is why the counterexample in the witness
  module builds its envelope by hand.
-/

namespace DarkTower.WarMachine.MachineObservation

open DarkTower.WarMachine.Holes

inductive MeasurementVariant | observed | absent deriving DecidableEq, Repr

structure ObservationEnvelope where
  variant : Channel → MeasurementVariant
  value : Channel → ℝ

/-- The tagged envelope `observation-envelope` builds from an observation
(`observation.clj:85-101`): the same numeric coordinate at every channel, paired
with that channel's variant. -/
def envelopeOf (values : Channel → ℝ) (variants : Channel → MeasurementVariant) :
    ObservationEnvelope := ⟨variants, values⟩

/-- The composite carrier: a total `ObservationVector` paired with the tagged
absence envelope which records the same numeric coordinate.  Totality over
`Channel` is not a hypothesis here — `observe` returns a literal fourteen-key
map (`observation.clj:120-145`), so every channel has a value on every input. -/
def machineObservation (values : Channel → ℝ)
    (variants : Channel → MeasurementVariant) :
    ObservationVector × ObservationEnvelope :=
  (⟨values⟩, envelopeOf values variants)

/-! ## The `[0,1]` bound: a predicate, and which channels establish it -/

def BoundedObservation (o : ObservationVector) : Prop :=
  ∀ channel, 0 ≤ o.value channel ∧ o.value channel ≤ 1

/-- `(min 1.0 …)`, the only clamp the implementation applies. -/
def upperClamp (x : ℝ) : ℝ := min 1 x

theorem upperClamp_le_one (x : ℝ) : upperClamp x ≤ 1 := min_le_left 1 x

/-- The two channels `observe` clamps: `:sorry-count-norm`
(`observation.clj:133`) and `:coupling-density` (`observation.clj:136-137`).
The other twelve are unclamped pass-throughs or unclamped quotients. -/
def clampedChannels : List Channel := [.sorryCountNorm, .couplingDensity]

/-- `observe`'s shape: clamp at the two clamped channels, pass the rest
through. -/
def clampAtClamped (raw : Channel → ℝ) : ObservationVector :=
  ⟨fun c => if c ∈ clampedChannels then upperClamp (raw c) else raw c⟩

/-- The upper bound holds at the clamped channels FOR EVERY raw reading — this
is the part of the `[0,1]` claim the construction does establish. -/
theorem clampedChannelsAreBoundedAbove (raw : Channel → ℝ) (c : Channel)
    (hc : c ∈ clampedChannels) : (clampAtClamped raw).value c ≤ 1 := by
  simp only [clampAtClamped, hc, if_pos]
  exact upperClamp_le_one _

/-! ## The envelope's coercion promise, and the one channel that cannot keep it

`channel-statuses` writes `{:variant :absent … :coerced-to 0.0}` at every absent
channel unconditionally (`observation.clj:69-73`).  Whether that promise is KEPT
is a claim about the coordinate `observe` returns, so a channel at which `observe`
returns nothing cannot keep it.  A reading is modelled as `Option ℝ`, with `none`
where the implementation raises instead of returning. -/

/-- What the envelope asserts at an absent channel. -/
def EnvelopePromises (envelope : ObservationEnvelope) (channel : Channel) : Prop :=
  envelope.variant channel = .absent → envelope.value channel = 0

/-- What keeping that assertion would require of the numeric path. -/
def PromiseKept (reading : Channel → Option ℝ) (envelope : ObservationEnvelope)
    (channel : Channel) : Prop :=
  envelope.variant channel = .absent → reading channel = some 0

/-- `:active-repo-ratio` (`observation.clj:129-132`).  `(:total-repos summary)`
is read WITH NO DEFAULT, so `(pos? nil)` raises: no reading exists. -/
noncomputable def activeRepoReading (activeRepos totalRepos : Option ℝ) : Option ℝ :=
  match totalRepos with
  | none => none
  | some t => if 0 < t then some ((activeRepos.getD 0) / t) else some 0

/-- `:coupling-density` (`observation.clj:134-138`) reads THE SAME KEY as
`(:total-repos summary 0)` — with a default.  The one-character difference is
the whole of the defect. -/
noncomputable def couplingDensityReading (couplingEdges totalRepos : Option ℝ) : Option ℝ :=
  let n := totalRepos.getD 0
  let maxEdges := n * (n - 1) / 2
  if 0 < maxEdges then some (upperClamp ((couplingEdges.getD 0) / maxEdges))
  else some 0

/-- The envelope's promise stands as written and is not kept.  The two are
separated deliberately: the defect is not that the envelope lies, it is that the
numeric path never reaches the coordinate the envelope describes. -/
theorem incompleteActiveRepoSummaryBreaksTheCoercionPromise
    (envelope : ObservationEnvelope) (reading : Channel → Option ℝ)
    (hAbsent : envelope.variant .activeRepoRatio = .absent)
    (hCoercedTo : envelope.value .activeRepoRatio = 0)
    (hNoReading : reading .activeRepoRatio = none) :
    EnvelopePromises envelope .activeRepoRatio ∧
      ¬ PromiseKept reading envelope .activeRepoRatio := by
  refine ⟨fun _ => hCoercedTo, fun hKept => ?_⟩
  have h := hKept hAbsent
  rw [hNoReading] at h
  exact absurd h.symm (by simp)

/-! ## The vector boundary -/

/-- `sense->vector` recomputes the envelope from the observation and compares
the WHOLE tagged map — variant and value together (`observation.clj:152-156`).
Matching on the numeric coordinates alone would be a weaker test, and the witness
module exhibits a pair on which the two tests disagree. -/
def EnvelopeMatches (expected provided : ObservationEnvelope) : Prop :=
  expected.variant = provided.variant ∧ expected.value = provided.value

/-- The ordered numeric vector, in `Channel.all` order
(`observation.clj:158`).  The matching proof is an ARGUMENT: without it there is
no vector, which is the refusal at `observation.clj:152-156` stated as a
signature. -/
def senseToVector (o : ObservationVector) (expected provided : ObservationEnvelope)
    (_matching : EnvelopeMatches expected provided) : List ℝ :=
  Channel.all.map o.value

end DarkTower.WarMachine.MachineObservation
