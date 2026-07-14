import Mathlib
import DarkTower.BV
import DarkTower.Fill
import DarkTower.TypedHole

/-!
# Evaluator comb as a DarkTower object

This file instantiates the feed-forward evaluator side of the common
generator/evaluator basis derived in `EVALUATOR-SPEC.md`.  One evaluator maps a
spacetime behaviour to a scalar score through the process spine

`readSpacetime ◁ selectSources ◁ estimate ◁ aggregate`.

AIS, nearest-neighbor transfer entropy, and distance/lagged transfer entropy
are occupants of the same two variation holes.  They differ in source
selection while sharing the corrected conditional-mutual-information estimator
and aggregation vocabulary.  Recurrence is external, so the deferred open
diagram layer in `Comb.lean` is not needed.
-/

namespace DarkTower

namespace EvaluatorExample

/-! ## Feed-forward process skeleton -/

/-- Observable stages of one behaviour-to-score evaluator pass. -/
inductive Stage where
  | readSpacetime
  | selectSources
  | estimate
  | aggregate
  deriving DecidableEq, Repr

/-- The evaluator-comb skeleton specified by the approved DERIVE. -/
def evaluatorComb : BV Stage :=
  BV.seq (BV.atom Stage.readSpacetime)
    (BV.seq (BV.atom Stage.selectSources)
      (BV.seq (BV.atom Stage.estimate) (BV.atom Stage.aggregate)))

/-- The evaluator tail with its first association exposed. -/
def evaluatorTailLeft : BV Stage :=
  BV.seq (BV.seq (BV.atom Stage.selectSources) (BV.atom Stage.estimate))
    (BV.atom Stage.aggregate)

/-- The evaluator tail as it occurs in `evaluatorComb`. -/
def evaluatorTailRight : BV Stage :=
  BV.seq (BV.atom Stage.selectSources)
    (BV.seq (BV.atom Stage.estimate) (BV.atom Stage.aggregate))

/-- Existing BV associativity composes the feed-forward evaluator tail. -/
example : BV.Cong evaluatorTailLeft evaluatorTailRight :=
  BV.Cong.seq_assoc (BV.atom Stage.selectSources) (BV.atom Stage.estimate)
    (BV.atom Stage.aggregate)

/-! ## Source-selection variation slot -/

/-- The source-selection policy is the single position of `sourceHole`. -/
inductive SourcePort where
  | policy
  deriving DecidableEq, Repr

/--
Ways to choose the observations conditioning destination-next prediction.
`offset d τ` selects the cell `d` sites away and `τ` steps back.
-/
inductive SourceSelectionFill where
  | selfPast
  | nearestNeighbor
  | offset (d : Int) (τ : Nat)
  deriving DecidableEq, Repr

/-- The source port accepts exactly a source-selection policy. -/
def SourceDirection : SourcePort -> Type
  | SourcePort.policy => SourceSelectionFill

/-- The source-selection interface is fed for every evaluator occupant. -/
def sourceHole : TypedHole where
  poly :=
    { A := SourcePort
      B := SourceDirection }
  satiety := fun _ => SatietyGrade.canon

/-- The source-selection port has the intended dependent fill type. -/
example : sourceHole.holeType SourcePort.policy = SourceSelectionFill :=
  rfl

/-- Every source-selection position is fed. -/
example (port : SourcePort) : sourceHole.satiety port = SatietyGrade.canon :=
  rfl

/-! ## Estimator-parameter variation slot -/

/-- Parameters spanning source selection, estimation, and score reduction. -/
inductive ParamPort where
  | destPast
  | sourcePast
  | offset
  | alphabet
  | correction
  | aggregate
  deriving DecidableEq, Repr

/-- Destination-history length `k`. -/
inductive DestPastFill where
  | historyLength (k : Nat)
  deriving DecidableEq, Repr

/-- Source-history length `l`. -/
inductive SourcePastFill where
  | historyLength (l : Nat)
  deriving DecidableEq, Repr

/-- Spatial distance `d` and temporal lag `τ`. -/
inductive OffsetFill where
  | distanceLag (d : Int) (τ : Nat)
  deriving DecidableEq, Repr

/-- Observation alphabets whose rotation sensitivity is tested at runtime. -/
inductive AlphabetFill where
  | bitplane
  | coarse
  | fullCell
  deriving DecidableEq, Repr

/-- Bias correction for the conditional-mutual-information estimate. -/
inductive CorrectionFill where
  | millerMadow
  deriving DecidableEq, Repr

/-- Reduction from per-cell/per-plane estimates to one scalar score. -/
inductive AggregateFill where
  | meanPerCellPlane
  deriving DecidableEq, Repr

/-- Each parameter position accepts only values of its parameter family. -/
def ParamDirection : ParamPort -> Type
  | ParamPort.destPast => DestPastFill
  | ParamPort.sourcePast => SourcePastFill
  | ParamPort.offset => OffsetFill
  | ParamPort.alphabet => AlphabetFill
  | ParamPort.correction => CorrectionFill
  | ParamPort.aggregate => AggregateFill

/-- The estimator-parameter interface is fully fed by every occupant. -/
def paramHole : TypedHole where
  poly :=
    { A := ParamPort
      B := ParamDirection }
  satiety := fun _ => SatietyGrade.canon

/-- Destination history has its intended fill type. -/
example : paramHole.holeType ParamPort.destPast = DestPastFill :=
  rfl

/-- Source history has its intended fill type. -/
example : paramHole.holeType ParamPort.sourcePast = SourcePastFill :=
  rfl

/-- Distance and lag share one dependent parameter fill. -/
example : paramHole.holeType ParamPort.offset = OffsetFill :=
  rfl

/-- Alphabet selection has its intended fill type. -/
example : paramHole.holeType ParamPort.alphabet = AlphabetFill :=
  rfl

/-- Bias correction has its intended fill type. -/
example : paramHole.holeType ParamPort.correction = CorrectionFill :=
  rfl

/-- Aggregation has its intended fill type. -/
example : paramHole.holeType ParamPort.aggregate = AggregateFill :=
  rfl

/-- Every estimator-parameter position is fed. -/
example (port : ParamPort) : paramHole.satiety port = SatietyGrade.canon :=
  rfl

/-! ## Occupant fills -/

/-- AIS conditions destination-next on the destination cell's own past. -/
def aisSourceFill :
    (port : sourceHole.poly.A) -> sourceHole.holeType port
  | SourcePort.policy => SourceSelectionFill.selfPast

/-- Nearest-neighbor TE conditions on an adjacent cell's past. -/
def nnTeSourceFill :
    (port : sourceHole.poly.A) -> sourceHole.holeType port
  | SourcePort.policy => SourceSelectionFill.nearestNeighbor

/-- Distance TE selects observations at the candidate spatial/temporal offset. -/
def distanceTeSourceFill (d : Int) (τ : Nat) :
    (port : sourceHole.poly.A) -> sourceHole.holeType port
  | SourcePort.policy => SourceSelectionFill.offset d τ

/-- AIS parameterization: one-step histories over a bitplane. -/
def aisParamFill :
    (port : paramHole.poly.A) -> paramHole.holeType port
  | ParamPort.destPast => DestPastFill.historyLength 1
  | ParamPort.sourcePast => SourcePastFill.historyLength 1
  | ParamPort.offset => OffsetFill.distanceLag 0 1
  | ParamPort.alphabet => AlphabetFill.bitplane
  | ParamPort.correction => CorrectionFill.millerMadow
  | ParamPort.aggregate => AggregateFill.meanPerCellPlane

/-- Nearest-neighbor TE parameterization with unit spatial and temporal lag. -/
def nnTeParamFill :
    (port : paramHole.poly.A) -> paramHole.holeType port
  | ParamPort.destPast => DestPastFill.historyLength 1
  | ParamPort.sourcePast => SourcePastFill.historyLength 1
  | ParamPort.offset => OffsetFill.distanceLag 1 1
  | ParamPort.alphabet => AlphabetFill.bitplane
  | ParamPort.correction => CorrectionFill.millerMadow
  | ParamPort.aggregate => AggregateFill.meanPerCellPlane

/--
Distance-TE leaves `(d, τ)` and the alphabet exposed for VERIFY.  This is
load-bearing: comparing bitplane, coarse, and full-cell occupants tests whether
the observed gliders rotate their values as they propagate.
-/
def distanceTeParamFill (d : Int) (τ : Nat) (alphabet : AlphabetFill) :
    (port : paramHole.poly.A) -> paramHole.holeType port
  | ParamPort.destPast => DestPastFill.historyLength 1
  | ParamPort.sourcePast => SourcePastFill.historyLength 1
  | ParamPort.offset => OffsetFill.distanceLag d τ
  | ParamPort.alphabet => alphabet
  | ParamPort.correction => CorrectionFill.millerMadow
  | ParamPort.aggregate => AggregateFill.meanPerCellPlane

/-- AIS occupies the source slot with self-history. -/
example : aisSourceFill SourcePort.policy = SourceSelectionFill.selfPast :=
  rfl

/-- nn-TE occupies the source slot with the adjacent-cell policy. -/
example : nnTeSourceFill SourcePort.policy = SourceSelectionFill.nearestNeighbor :=
  rfl

/-- Distance-TE carries its concrete distance and lag in the source fill. -/
example (d : Int) (τ : Nat) : distanceTeSourceFill d τ SourcePort.policy =
    SourceSelectionFill.offset d τ :=
  rfl

/-! ## Three occupants of one evaluator comb -/

/-- The evaluator twin of `MetaCAExample.DynamicOccupant`. -/
structure EvaluatorOccupant where
  /-- The evaluator's fill at every source-selection port. -/
  sourceFill : (port : sourceHole.poly.A) -> sourceHole.holeType port
  /-- The evaluator's fill at every estimator-parameter port. -/
  paramFill : (port : paramHole.poly.A) -> paramHole.holeType port

/-- Active information storage on the common evaluator skeleton. -/
def aisOccupant : EvaluatorOccupant where
  sourceFill := aisSourceFill
  paramFill := aisParamFill

/-- Nearest-neighbor transfer entropy on the common evaluator skeleton. -/
def nnTeOccupant : EvaluatorOccupant where
  sourceFill := nnTeSourceFill
  paramFill := nnTeParamFill

/--
Distance/lagged transfer entropy is an occupant family awaiting empirical
selection of `(d, τ, alphabet)` in the Clojure VERIFY half.
-/
def distanceTeOccupant (d : Int) (τ : Nat)
    (alphabet : AlphabetFill) : EvaluatorOccupant where
  sourceFill := distanceTeSourceFill d τ
  paramFill := distanceTeParamFill d τ alphabet

/-- AIS has the required source fill type and selects self-history. -/
example : aisOccupant.sourceFill SourcePort.policy =
    SourceSelectionFill.selfPast :=
  rfl

/-- AIS uses the approved Miller-Madow correction. -/
example : aisOccupant.paramFill ParamPort.correction =
    CorrectionFill.millerMadow :=
  rfl

/-- nn-TE has the required source fill type and selects the nearest neighbor. -/
example : nnTeOccupant.sourceFill SourcePort.policy =
    SourceSelectionFill.nearestNeighbor :=
  rfl

/-- nn-TE records unit spatial/temporal offset in the parameter hole. -/
example : nnTeOccupant.paramFill ParamPort.offset =
    OffsetFill.distanceLag 1 1 :=
  rfl

/-- A distance-TE occupant uses the same `(d, τ)` at both variation holes. -/
example (d : Int) (τ : Nat) (alphabet : AlphabetFill) :
    (distanceTeOccupant d τ alphabet).sourceFill SourcePort.policy =
      SourceSelectionFill.offset d τ :=
  rfl

/-- The distance-TE alphabet remains an explicit occupant parameter. -/
example (d : Int) (τ : Nat) (alphabet : AlphabetFill) :
    (distanceTeOccupant d τ alphabet).paramFill ParamPort.alphabet = alphabet :=
  rfl

/-- Nested polynomial substitution records the two evaluator variation slots. -/
def twoSlotInterface := Fill.fill paramHole.poly sourceHole.poly

/-! ## R9 validation property -/

/--
A runtime-produced 95% validation record for one evaluator occupant.  The Lean
object states the bounds and their ownership; producing an honest record is the
responsibility of the independent runtime measurement and artifact bridge.
-/
structure ValidationRecord where
  occupant : EvaluatorOccupant
  complexLower : ℝ
  frozenUpper : ℝ
  chaoticUpper : ℝ
  artifactRef : String

/--
R9 separation: a runtime record for `occ` has a nonempty artifact reference and
its complex-class 95% lower bound is strictly above both frozen and chaotic 95%
upper bounds.
-/
def SeparatesEoC (occ : EvaluatorOccupant) : Prop :=
  ∃ record : ValidationRecord,
    record.occupant = occ ∧
      record.artifactRef ≠ "" ∧
      record.complexLower > record.frozenUpper ∧
      record.complexLower > record.chaoticUpper

/-!
The runtime evidence reports that AIS satisfies `SeparatesEoC`.  No theorem is
asserted here because the confidence bounds are external measurements.

Nearest-neighbor TE does not satisfy the intended ordering: its chaotic score
is `0.208`, above its complex score `0.072`.  Distance-TE is the candidate to be
VERIFIED by the Clojure half across offsets and all three alphabets, and must
also reproduce the eye-calibration ordering before acceptance.
-/

end EvaluatorExample

end DarkTower
