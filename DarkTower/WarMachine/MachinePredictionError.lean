import DarkTower.WarMachine.MachinePrecision

/-!
# The machine's prediction error ε, stated

`futon2:holes/labs/wm-contract/worklist.edn` `:F8`, leg 1 (Lean completion),
slice 2. The quantity is `:prediction-error` (ε, node R8) of
`futon2:holes/labs/wm-contract/aif-equations.edn:77-80`, whose row carried
`:lean nil :lean-status :missing` before this module.

WHAT WAS IN LEAN BEFORE. `Holes.predictionError` (`Holes.lean:6815-6817`) is
the registry's `:formal` line and nothing more: `ε_k := o_k − μ_k`, a total
function `ObservationVector → (Channel → ℝ) → Channel → ℝ`.
`PredictionErrorWitness` witnesses that it is the signed difference and equals
neither operand; `PredictionErrorNegative` refuses the reversed sign. So the
SPEC form was in Lean and the map the implementation runs was not.

WHAT THIS MODULE STATES. `compute-prediction-error`
(`futon2:src/futon2/aif/free_energy.clj:203-278`) is not a function into ℝ. It
is a function into a THREE-VALUED typed record — present, absent, refused —
and which one it emits is the decision (AC1, Joe's 2026-09-02 ruling on C130
§2, quoted in the docstring at `:207-212`). Three reductions the `:formal`
line does not carry are visible in it, and each is stated below:

1. THE SUBTRACTED TERM IS NOT μ. It is `:predicted-mean`, one member of a
   likelihood-model output `{:mean :variance}` produced by
   `belief/predict-observation` (`belief.clj:1199-1238`) from the belief
   state. The implementation's belief is an entity-indexed CATEGORICAL map,
   not the per-channel `Channel → ℝ` mean `Holes.BeliefState` and the registry
   line both assume; the per-channel mean is a READOUT of it
   (`belief.clj:640-737`). `registryFormOfPresent` states exactly where the
   registry line holds: on a channel whose predicted mean IS the belief mean.
   Whether that hypothesis holds of the running stack is a question about
   `predict-observation`, not about this row, and no claim is made here.
2. THE OUTPUT CARRIES A PRECISION THAT IS NOT R7's Π. The `:precision` the
   producer stamps is `1 / max(predicted-variance, minVariance)`, derived from
   the LIKELIHOOD's variance for this one call. R7's Π
   (`MachinePrecision.machinePrecision`, slice 1) is derived from the
   channel's ERROR HISTORY. They are different numbers, they occupy the same
   `:precision` key at different points in the tick, and
   `precision/weighted-error` (`precision.clj:213-233`) overwrites the first
   with the second, preserving it as `:per-call-precision`. This module
   therefore calls the field `perCallPrecision`: naming it `precision` would
   reproduce in Lean exactly the bare-symbol collision `:F8` leg 2's
   concordance checker exists to refuse.
3. A REFUSAL OF ONE CHANNEL REFUSES THE WHOLE UPDATE. At the vector level
   (`war_machine.clj:6110-6127`) an ABSENT channel is omitted and the rest are
   scored, but a single REFUSED channel empties the error map for every
   channel — `scoredErrors` below, and `oneRefusalEmptiesTheUpdate`.

WHAT THIS MODULE FINDS. A NEGATIVE PREDICTED VARIANCE IS SCORED, NOT REFUSED.
`prediction-member` (`free_energy.clj:191-201`) classifies a model member as
missing, not-finite, or present, and `-4.0` is present: finiteness is checked
and sign is not. The `max` at `:270` then floors it to `minVariance`, so a
variance that cannot exist yields the LARGEST per-call precision the floor
allows — `1/minVariance` = 100 under the declared default — and the record is
indistinguishable from one built on a variance of exactly zero except by
reading `:predicted-variance` back out.
(`negativeVarianceIsNotRefused`, `subMinVarianceIsFloored`, and
`MachinePredictionErrorWitness.zeroAndNegativeVarianceAgree`.) NOT A RULING:
nothing is written to `:choices`, and no claim is made about whether the
producer should refuse a negative variance.

WHAT THIS MODULE DOES NOT DO. It says nothing about generalised coordinates
(the reduction the registry's `:eq` already names), nothing about the
belief-aggregation driver that consumes the errors at R3, and nothing about
`:policy-free-energy`, which is a different row on the same node.
-/

namespace DarkTower.WarMachine.MachinePredictionError

open DarkTower.WarMachine.Holes

/-- One field of the producer's input AS IT ARRIVES, with the three cases
`free_energy.clj:182-201` distinguishes: the key is missing or `nil`
(`.missing`); the key holds something that is not a finite number — a string,
a keyword, a NaN, an infinity (`.notFinite`); or it holds a finite number
(`.value`). ℝ has no NaN, so the malformed case has to be a constructor
rather than a real number: this type is the producer's input space, not a
subset of ℝ. -/
inductive Field where
  | missing
  | notFinite
  | value (x : ℝ)

/-- The likelihood-model output for one channel, `{:mean :variance}` as
`belief/predict-observation` emits it (`belief.clj:1199-1238`). -/
structure Prediction where
  mean : Field
  variance : Field

/-- The three members the refusal record can name (`free_energy.clj:246-249`). -/
inductive Member where
  | mean | variance | observed
  deriving DecidableEq, Repr

/-- One entry of `:offending`. Missing and not-finite are kept apart because
the refusal record has to say which one happened (`free_energy.clj:192-194`). -/
inductive Offence where
  | missing (m : Member)
  | notFinite (m : Member)
  deriving DecidableEq, Repr

/-- A MODEL member offends when it is anything but a finite number: a
likelihood that produced no mean is a producer defect. -/
def memberOffence (m : Member) : Field → List Offence
  | .missing => [Offence.missing m]
  | .notFinite => [Offence.notFinite m]
  | .value _ => []

/-- The OBSERVATION offends only when it is malformed. An observation nobody
made is absent, not offending — `observed-malformed?` at
`free_energy.clj:245` guards on `(some? observed)`, which is the whole of the
difference between omitting a channel and refusing the update. -/
def observedOffence : Field → List Offence
  | .notFinite => [Offence.notFinite Member.observed]
  | _ => []

/-- `:offending`, in the order `free_energy.clj:246-249` builds it: the two
model members first, in `[mean variance]` order, then the observation
appended by `conj` onto the vector. -/
def offences (o : Field) (p : Prediction) : List Offence :=
  memberOffence Member.mean p.mean ++ memberOffence Member.variance p.variance
    ++ observedOffence o

/-- The `:present` record, field for field as `free_energy.clj:271-278` emits
it. `perCallPrecision` is the key the runtime spells `:precision`; see §2 of
the module docstring for why it is not spelled that way here. -/
structure PresentRecord where
  observed : ℝ
  predictedMean : ℝ
  predictedVariance : ℝ
  error : ℝ
  perCallPrecision : ℝ
  weightedError : ℝ

/-- The producer's output: one of three typed records, and which one it emits
is the decision. -/
inductive Outcome where
  | present (r : PresentRecord)
  | absent (m : Member)
  | refused (offending : List Offence)

/-- `free_energy.clj:266-278`: ε := o − mean, per-call Π := 1 / max(variance,
minVariance), weighted := ε · Π. -/
noncomputable def presentRecord (minVariance observed predictedMean predictedVariance : ℝ) :
    PresentRecord :=
  { observed := observed
    predictedMean := predictedMean
    predictedVariance := predictedVariance
    error := observed - predictedMean
    perCallPrecision := 1 / max predictedVariance minVariance
    weightedError := (observed - predictedMean) * (1 / max predictedVariance minVariance) }

/-- THE PRODUCER, `free_energy.clj:250-278`. The `cond` has three arms and
their ORDER is load-bearing, so the match below reproduces it rather than
paraphrasing it: offences are tested first, absence second, scoring last.
Written by matching on the three fields because that is provably the same
function (`refused_iff` below) and far easier to compute with. -/
noncomputable def machineChannelPredictionError (minVariance : ℝ)
    (o : Field) (p : Prediction) : Outcome :=
  match p.mean, p.variance, o with
  | .value m, .value v, .value ob => .present (presentRecord minVariance ob m v)
  | .value _, .value _, .missing => .absent Member.observed
  | _, _, _ => .refused (offences o p)

/-! ### The three arms, and the order they are tried in -/

/-- The match above IS the `cond`: the producer refuses exactly when
`:offending` is nonempty, which is the first arm's guard. -/
theorem refused_iff (minVariance : ℝ) (o : Field) (p : Prediction) :
    (∃ l, machineChannelPredictionError minVariance o p = Outcome.refused l)
      ↔ offences o p ≠ [] := by
  obtain ⟨mean, var⟩ := p
  cases mean <;> cases var <;> cases o <;>
    simp [machineChannelPredictionError, offences, memberOffence, observedOffence]

/-- REFUSAL DOMINATES ABSENCE. A channel this tick did not observe, whose
likelihood ALSO failed to produce a mean, is REFUSED and not omitted — the
`cond`'s first arm is reached before the `(nil? observed)` arm. So the count
of omissions in a tick is not the count of unobserved channels. -/
theorem refusalDominatesAbsence (minVariance : ℝ) (v : Field) :
    machineChannelPredictionError minVariance Field.missing ⟨Field.missing, v⟩
      = Outcome.refused (offences Field.missing ⟨Field.missing, v⟩) := by
  cases v <;> rfl

/-- ABSENCE REQUIRES A WELL-FORMED MODEL. The converse of the above: the
producer omits a channel only when both model members are finite numbers and
the observation alone is missing. -/
theorem absence_requires_wellFormedModel (minVariance : ℝ) (o : Field) (p : Prediction)
    (h : machineChannelPredictionError minVariance o p = Outcome.absent Member.observed) :
    o = Field.missing ∧ (∃ m, p.mean = Field.value m) ∧ (∃ v, p.variance = Field.value v) := by
  obtain ⟨mean, var⟩ := p
  cases mean <;> cases var <;> cases o <;>
    simp_all [machineChannelPredictionError]

/-- An unobserved channel under a well-formed model is OMITTED, and the record
carries no numbers at all: an observation nobody made is not an observation of
zero. -/
theorem missingObservationIsAbsent (minVariance m v : ℝ) :
    machineChannelPredictionError minVariance Field.missing
        ⟨Field.value m, Field.value v⟩ = Outcome.absent Member.observed := rfl

/-- A MALFORMED observation is refused, not omitted: `free_energy.clj:245`
distinguishes `nil` from a value that is not a finite number. -/
theorem malformedObservationIsRefused (minVariance m v : ℝ) :
    machineChannelPredictionError minVariance Field.notFinite
        ⟨Field.value m, Field.value v⟩
      = Outcome.refused [Offence.notFinite Member.observed] := rfl

/-! ### The scored arm -/

theorem present_eq (minVariance ob m v : ℝ) :
    machineChannelPredictionError minVariance (Field.value ob)
        ⟨Field.value m, Field.value v⟩
      = Outcome.present (presentRecord minVariance ob m v) := rfl

/-- THE REGISTRY LINE, EXACTLY WHERE IT HOLDS. `aif-equations.edn:79` writes
`eps_k := o_k - mu_k`; the scored arm's `:error` is that difference precisely
when the likelihood's predicted mean for the channel IS the belief mean the
registry line names. `Holes.predictionError` is the registry line, so this is
the seam between the spec form already in Lean and the map the machine runs. -/
theorem registryFormOfPresent (minVariance : ℝ) (obs : ObservationVector)
    (beliefMean : Channel → ℝ) (variance : Channel → ℝ) (k : Channel) :
    machineChannelPredictionError minVariance (Field.value (obs.value k))
        ⟨Field.value (beliefMean k), Field.value (variance k)⟩
      = Outcome.present
          { observed := obs.value k
            predictedMean := beliefMean k
            predictedVariance := variance k
            error := predictionError obs beliefMean k
            perCallPrecision := 1 / max (variance k) minVariance
            weightedError :=
              predictionError obs beliefMean k * (1 / max (variance k) minVariance) } := rfl

theorem perCallPrecision_pos (minVariance : ℝ) (hmv : 0 < minVariance) (ob m v : ℝ) :
    0 < (presentRecord minVariance ob m v).perCallPrecision := by
  have h : 0 < max v minVariance := lt_of_lt_of_le hmv (le_max_right _ _)
  simpa [presentRecord] using one_div_pos.mpr h

theorem weightedError_eq (minVariance ob m v : ℝ) :
    (presentRecord minVariance ob m v).weightedError
      = (presentRecord minVariance ob m v).error
        * (presentRecord minVariance ob m v).perCallPrecision := rfl

/-! ### The finding: a negative predicted variance is scored, not refused -/

/-- No hypothesis on `v`. A variance of `-4` reaches the scored arm exactly as
a variance of `1/4` does, because `prediction-member` checks FINITENESS and
not sign (`free_energy.clj:191-201`). -/
theorem negativeVarianceIsNotRefused (minVariance ob m v : ℝ) :
    machineChannelPredictionError minVariance (Field.value ob)
        ⟨Field.value m, Field.value v⟩
      = Outcome.present (presentRecord minVariance ob m v) := rfl

/-- And then the floor collapses it: every variance at or below `minVariance`
— zero, and every negative number — yields the same per-call precision
`1/minVariance`, the largest the floor allows. -/
theorem subMinVarianceIsFloored (minVariance ob m v : ℝ) (hv : v ≤ minVariance) :
    (presentRecord minVariance ob m v).perCallPrecision = 1 / minVariance := by
  simp [presentRecord, max_eq_right hv]

/-- `free_energy.clj:240`, the `:or {min-variance 0.01}` default of this
producer. It is a SEPARATE declaration from `precision.clj:43`'s
`default-min-variance`, which holds the same value and floors a different
quantity (the error-history variance, not the likelihood's). -/
noncomputable def defaultMinVariance : ℝ := 1 / 100

/-! ### The vector level: which channels are scored at all -/

/-- `belief.clj:933-934`, `channels-with-likelihood`: the EIGHT channels for
which an R3a likelihood model exists. The tick computes ε on these and does
not attempt the other six at all — they produce no record, not an absent one
(`war_machine.clj:6110-6113`). -/
def channelsWithLikelihood : List Channel :=
  [.annotationHealth, .sorryCountNorm, .missionHealth, .activeRepoRatio,
   .supportCoverage, .attackCoverage, .couplingDensity, .ticksFiringRatio]

theorem channelsWithLikelihood_length : channelsWithLikelihood.length = 8 := rfl

/-- The six declared channels ε is never computed on. -/
def channelsWithoutLikelihood : List Channel :=
  Channel.all.filter (fun k => !channelsWithLikelihood.contains k)

theorem channelsWithoutLikelihood_eq :
    channelsWithoutLikelihood =
      [.loopHealth, .stackPct, .consultingPct, .portfolioPct, .mathematicsPct,
       .depositingSignal] := rfl

theorem channelsWithoutLikelihood_length : channelsWithoutLikelihood.length = 6 := rfl

def isPresent : Outcome → Bool
  | .present _ => true
  | _ => false

def isRefused : Outcome → Bool
  | .refused _ => true
  | _ => false

/-- `war_machine.clj:6110-6113`, `triples`: one producer call per channel that
has a likelihood model. -/
noncomputable def channelOutcomes (minVariance : ℝ) (o : Channel → Field)
    (p : Channel → Prediction) : List (Channel × Outcome) :=
  channelsWithLikelihood.map (fun k => (k, machineChannelPredictionError minVariance (o k) (p k)))

/-- `war_machine.clj:6123-6127`, `raw-errors`: the map that actually reaches
R7 and R3. Absent channels are dropped and the rest are kept; but if ANY
channel refused, the whole map is empty. -/
noncomputable def scoredErrors (minVariance : ℝ) (o : Channel → Field)
    (p : Channel → Prediction) : List (Channel × Outcome) :=
  if (channelOutcomes minVariance o p).any (fun x => isRefused x.2) then []
  else (channelOutcomes minVariance o p).filter (fun x => isPresent x.2)

/-- ONE REFUSAL EMPTIES THE UPDATE. A single channel whose likelihood failed
takes every other channel's error with it, however well those were measured.
This is the all-or-nothing rule the registry's `:formal` line has no room to
carry. -/
theorem oneRefusalEmptiesTheUpdate (minVariance : ℝ) (o : Channel → Field)
    (p : Channel → Prediction) (k : Channel) (hk : k ∈ channelsWithLikelihood)
    (h : isRefused (machineChannelPredictionError minVariance (o k) (p k)) = true) :
    scoredErrors minVariance o p = [] := by
  have : (channelOutcomes minVariance o p).any (fun x => isRefused x.2) = true := by
    rw [List.any_eq_true]
    exact ⟨(k, machineChannelPredictionError minVariance (o k) (p k)),
      List.mem_map_of_mem hk, h⟩
  simp [scoredErrors, this]

/-- What survives is present and nothing else: an absent channel is OMITTED
from the update, never entered at zero. -/
theorem scoredErrors_present (minVariance : ℝ) (o : Channel → Field)
    (p : Channel → Prediction) (x : Channel × Outcome)
    (hx : x ∈ scoredErrors minVariance o p) : isPresent x.2 = true := by
  unfold scoredErrors at hx
  split at hx
  · simp at hx
  · exact (List.mem_filter.mp hx).2

end DarkTower.WarMachine.MachinePredictionError
