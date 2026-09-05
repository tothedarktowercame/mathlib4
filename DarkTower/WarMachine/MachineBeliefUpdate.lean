import DarkTower.WarMachine.MachinePredictionError

/-!
# The machine belief update μ-next

This states the map executed by `futon2.aif.belief/r3d-aggregate-driver`
(`futon2:src/futon2/aif/belief.clj:1122-1197`) and the War Machine R3 inner
step (`futon2:scripts/futon2/report/war_machine.clj:6147-6187`). The resulting
per-entity event is consumed by the categorical filter
(`futon2:src/futon2/aif/belief.clj:297-346`), not by an additive update on a
real-valued vector.
-/

namespace DarkTower.WarMachine.MachineBeliefUpdate

open scoped BigOperators

structure ChannelContribution where
  sign : ℝ
  precision : ℝ
  predictionError : ℝ

def signedWeightedError (c : ChannelContribution) : ℝ :=
  c.sign * c.precision * c.predictionError

noncomputable def multichannelDriver (cs : List ChannelContribution) : Option ℝ :=
  let totalPrecision := (cs.map (·.precision)).sum
  if 0 < totalPrecision then
    some ((cs.map signedWeightedError).sum / totalPrecision)
  else none

def singleChannelDriver (c : ChannelContribution) : ℝ :=
  c.precision * c.predictionError

noncomputable def annealFactor (step maxSteps : ℝ) : ℝ :=
  max 0 (1 - step / maxSteps)

def baseWeight (driver : ℝ) : ℝ := min 1 |driver|

noncomputable def eventWeight (driver step maxSteps : ℝ) : ℝ :=
  baseWeight driver * annealFactor step maxSteps * (1 / 10)

inductive BeliefEventType
  | strengthened
  | foreclosed
  deriving DecidableEq, Repr

noncomputable def eventType (driver : ℝ) : BeliefEventType :=
  if 0 < driver then .strengthened else .foreclosed

def inconsistency (kind : BeliefEventType) (health : ℝ) : ℝ :=
  match kind with
  | .strengthened => 1 - health
  | .foreclosed => health

noncomputable def attributionNorm (eventWeight entityCount totalInconsistency : ℝ) : ℝ :=
  if 0 < totalInconsistency then
    eventWeight * entityCount / totalInconsistency
  else 0

noncomputable def attributedWeight (eventWeight entityCount totalInconsistency health : ℝ)
    (kind : BeliefEventType) : ℝ :=
  inconsistency kind health *
    attributionNorm eventWeight entityCount totalInconsistency

noncomputable def normalise {n : Nat} [NeZero n] (q : Fin n → ℝ) : Fin n → ℝ :=
  let total := ∑ i, q i
  if total = 0 then fun _ => 1 / n else fun i => q i / total

/-- `Math/pow likelihood (log2 (1+w))`, with the zero exponent made explicit.
All production likelihoods are positive, so this branch is extensionally the
same and exposes the exact no-op boundary without floating-point reasoning. -/
noncomputable def temperedLikelihood (kappa likelihood : ℝ) : ℝ :=
  if kappa = 0 then 1 else likelihood ^ kappa

noncomputable def categoricalUpdate {n : Nat} [NeZero n]
    (kappa : ℝ) (likelihood prior : Fin n → ℝ) : Fin n → ℝ :=
  normalise fun i => temperedLikelihood kappa (likelihood i) * prior i

noncomputable def kappa (weight : ℝ) : ℝ :=
  Real.log (1 + weight) / Real.log 2

theorem kappa_zero : kappa 0 = 0 := by
  simp [kappa]

theorem kappaZeroIsNoOp {n : Nat} [NeZero n] (likelihood prior : Fin n → ℝ)
    (hprior : (∑ i, prior i) = 1) :
    categoricalUpdate 0 likelihood prior = prior := by
  funext i
  simp [categoricalUpdate, temperedLikelihood, normalise, hprior]

theorem zeroTotalInconsistencyMovesNothing
    (eventWeight entityCount health : ℝ) (kind : BeliefEventType) :
    attributedWeight eventWeight entityCount 0 health kind = 0 := by
  simp [attributedWeight, attributionNorm]

theorem driverMagnitudeSaturates :
    eventWeight 1 0 3 = eventWeight 50 0 3 := by
  norm_num [eventWeight, baseWeight, annealFactor, abs_of_nonneg]

theorem annealTerminates : annealFactor 3 3 = 0 := by
  norm_num [annealFactor]

theorem productionStepsDoNotReachAnnealTermination (step : Nat)
    (h : step < 3) : step ≠ 3 := by
  omega

theorem unknownDriverAppliesNoEvent (step maxSteps : ℝ) :
    eventWeight ((none : Option ℝ).getD 0) step maxSteps = 0 := by
  simp [eventWeight, baseWeight]

theorem precisionDividesOutInMultichannel
    (cs : List ChannelContribution) (scale : ℝ)
    (hscale : 0 < scale)
    (hprecision : 0 < (cs.map (·.precision)).sum) :
    multichannelDriver
        (cs.map fun c => { c with precision := scale * c.precision }) =
      multichannelDriver cs := by
  simp only [multichannelDriver, List.map_map]
  have hden :
      (cs.map fun c => scale * c.precision).sum =
        scale * (cs.map (·.precision)).sum := by
    exact List.sum_map_mul_left cs (·.precision) scale
  have hnum :
      (cs.map fun c => signedWeightedError
        { c with precision := scale * c.precision }).sum =
        scale * (cs.map signedWeightedError).sum := by
    rw [← List.sum_map_mul_left cs signedWeightedError scale]
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    simp [signedWeightedError]
    ring
  have hscaled : 0 < (cs.map fun c => scale * c.precision).sum := by
    rw [hden]
    positivity
  change
    (if 0 < (cs.map fun c => scale * c.precision).sum then
      some ((cs.map fun c => signedWeightedError
        { c with precision := scale * c.precision }).sum /
        (cs.map fun c => scale * c.precision).sum)
     else none) =
    (if 0 < (cs.map (·.precision)).sum then
      some ((cs.map signedWeightedError).sum /
        (cs.map (·.precision)).sum)
     else none)
  rw [hden, hnum]
  rw [if_pos (mul_pos hscale hprecision), if_pos hprecision]
  congr 1
  field_simp

theorem precisionScalesSingleChannel (c : ChannelContribution) (scale : ℝ) :
    singleChannelDriver { c with precision := scale * c.precision } =
      scale * singleChannelDriver c := by
  simp [singleChannelDriver]
  ring

/-- The registry's additive expression is not the machine map in general.
This two-state counterexample uses κ=0: Bayes leaves the prior fixed while a
nonzero additive `alpha * Pi * eps` moves it. -/
theorem registryAdditiveFormIsNotGeneral :
    let prior : Fin 2 → ℝ := fun _ => 1 / 2
    let likelihood : Fin 2 → ℝ := fun _ => 1
    categoricalUpdate 0 likelihood prior 0 ≠ prior 0 + (1/10) * 2 * 1 := by
  norm_num [categoricalUpdate, temperedLikelihood, normalise]

end DarkTower.WarMachine.MachineBeliefUpdate
