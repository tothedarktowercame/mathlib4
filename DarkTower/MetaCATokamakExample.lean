import Mathlib
import DarkTower.TypedHole
import DarkTower.BV

/-!
# The MetaCA tokamak as a DarkTower object

This file mirrors `WMPipelineExample.lean`: one tokamak tick is a `BV` process
expression over a `Stage` enum. The EFE decomposition (epistemic ΔF and
pragmatic ΔG) is held simultaneous by `BV.copar` (⅋) — non-signalling,
never sequenced — exactly as the War Machine's `gateF ⅋ gateG`.

The 9-stage enum and tick spine instantiate the Slice 0 design
(`futon5/holes/labs/M-aif-tokamak/darktower-map.md`). The stages mirror the AIF
*target* controller's actual per-tick flow:
`step ◁ perceive ◁ predict ◁ (evaluateF ⅋ evaluateG) ◁ gate ◁ select ◁ enact ◁ trace`

Feed-forward per tick: recurrence is the outer `run-controller` loop (tick N's
`enact` writes exotype params that tick N+1's `step` reads), precisely like
`WMPipelineExample`'s `learn → next wake` loop is external iteration.

Stage occupants are stubs this slice — the `g-efe`/`TypedHole`/theorem content
is Slice 2+.

Grounding:
* `futon5/holes/labs/M-aif-tokamak/darktower-map.md` (the compliance mapping);
* `futon5/holes/missions/M-aif-tokamak.md` (the mission spec, Slice 1 block);
* `futon5/src/futon5/aif/forward.clj` (the Clojure forward model this mirrors);
* `futon5/scripts/cyber_mmca_compare.clj:195` (the `run-controller` loop whose
  tick stages the `Stage` enum mirrors).
-/

namespace DarkTower

namespace MetaCATokamakExample

/-- Stages of one tokamak tick (the AIF target controller's per-tick flow). -/
inductive Stage where
  | step        -- run the CA forward (runtime/run-mmca): produces the observation
  | perceive    -- predictive-coding update of belief μ from the observation (R1/R3)
  | predict     -- forward-predict next macro-features under each candidate action (R4)
  | evaluateF   -- the epistemic leg: ΔF (ambiguity) over predicted outcomes
  | evaluateG   -- the pragmatic leg: ΔG (KL-risk to C) over predicted outcomes
  | gate        -- the ∧: combine epistemic + pragmatic into G_efe per action
  | select      -- softmax over -G/τ; abstain if below threshold (R6/R14/R9)
  | enact       -- apply the selected action via adjust-params; write exotype params
  | trace       -- emit per-tick F, G, τ, action, regime (R8)
  deriving DecidableEq, Repr

/--
One tokamak tick as a BV process expression: a `seq` spine, with the two EFE
evaluation legs held simultaneous by `copar` — ΔF (ambiguity) and ΔG (KL-risk to
C) are independent readings of the same `predict` cascade, neither may signal
the other (the `gate` stage demands both, separately). This mirrors
`WMPipelineExample.flight` exactly in structure.
-/
def tick : BV Stage :=
  BV.seq (BV.atom Stage.step)
    (BV.seq (BV.atom Stage.perceive)
      (BV.seq (BV.atom Stage.predict)
        (BV.seq (BV.copar (BV.atom Stage.evaluateF) (BV.atom Stage.evaluateG))
          (BV.seq (BV.atom Stage.gate)
            (BV.seq (BV.atom Stage.select)
              (BV.seq (BV.atom Stage.enact)
                (BV.atom Stage.trace)))))))

/-- A three-stage prefix, left-associated. -/
def stepPerceivePredictLeft : BV Stage :=
  BV.seq (BV.seq (BV.atom Stage.step) (BV.atom Stage.perceive)) (BV.atom Stage.predict)

/-- The reassociated form. -/
def stepPerceivePredictRight : BV Stage :=
  BV.seq (BV.atom Stage.step) (BV.seq (BV.atom Stage.perceive) (BV.atom Stage.predict))

/-- The tick prefix reassociates by BV structural congruence. -/
example : BV.Cong stepPerceivePredictLeft stepPerceivePredictRight :=
  BV.Cong.seq_assoc (BV.atom Stage.step) (BV.atom Stage.perceive) (BV.atom Stage.predict)

/-! ## Observation feed (R2 macro-feature channels)

The 5 macro-feature observation channels produced by `windowed-macro-features`
(`futon5/src/futon5/mmca/metrics.clj:596`). Each port is a position on the
observation typed-hole; its satiety records whether the CA step fed it.

Stub: the full satiety-graded `TypedHole` and the starvation theorem are
Slice 3. Here we declare the port enum and the interface type so the Lean
object compiles and mirrors the Clojure ABI.
-/

/-- The 5 macro-feature observation channels (R2 ABI). -/
inductive ObsPort where
  | pressure     -- normalized avg-change (metrics.clj:626)
  | selectivity  -- normalized 1-avg-unique (metrics.clj:628)
  | structure    -- normalized temporal-autocorr (metrics.clj:629)
  | activity     -- normalized avg-change (metrics.clj:630)
  | regime       -- classify-regime keyword: freeze | magma | static | chaos | eoc
  deriving DecidableEq, Repr

/-- Regime labels from classify-regime (metrics.clj:643). -/
inductive RegimeLabel where
  | freeze
  | magma
  | static
  | chaos
  | eoc
  deriving DecidableEq, Repr

/-- What fills each observation port. -/
inductive ObsFeed where
  | reading (v : Float)       -- a normalized [0,1] macro-feature value
  | regimeLabel (r : RegimeLabel)
  deriving Repr

/-- The direction family: every observation port accepts an `ObsFeed`. -/
def ObsDirection : ObsPort → Type
  | _ => ObsFeed

/--
The observation interface as a typed-hole. In the fed (live) apparatus, all
ports grade `canon` — the CA step produces them every tick. The satiety grading
and the starvation theorem (`IsHungry` for a severed feed) are Slice 3.
-/
def obsHole : TypedHole where
  poly :=
    { A := ObsPort
      B := ObsDirection }
  satiety := fun _ => SatietyGrade.canon

/-- A port is hungry when its satiety is the payoff grade (FirstFlights idiom). -/
def IsHungry (T : TypedHole) (a : T.poly.A) : Prop :=
  T.satiety a = SatietyGrade.payoff

/-- In the live apparatus, the pressure port is fed (not hungry). -/
example : ¬ IsHungry obsHole ObsPort.pressure := by
  simp [IsHungry, obsHole]

/-- In the live apparatus, the regime port is fed (not hungry). -/
example : ¬ IsHungry obsHole ObsPort.regime := by
  simp [IsHungry, obsHole]

/-- Every observation port accepts `ObsFeed` (the interface types check). -/
example : obsHole.holeType ObsPort.pressure = ObsFeed :=
  rfl

/-! ## EoC preference C (R19) and EFE occupants (R5)

The EFE decomposition is structurally copar (⅋), not seq — non-signalling.
This is visible in the `tick` definition above: `BV.copar (evaluateF) (evaluateG)`.

The occupants below give the evaluateF/evaluateG/gate stages concrete Lean
types. The math (Gaussian KL + Gaussian entropy) mirrors the Clojure
`futon5.aif.efe` kernel, which in turn mirrors `ants.aif.efe` byte-for-byte.
-/

/-- The EoC confinement preference C: target means per channel. -/
def eocTargetMeans : ObsPort → Float
  | ObsPort.pressure => 0.5
  | ObsPort.selectivity => 0.4
  | ObsPort.structure => 0.4
  | ObsPort.activity => 0.5
  | ObsPort.regime => 0.0  -- regime is categorical, not a numeric target

/-- The EoC confinement preference C: target variances (σ²) per channel. -/
def eocTargetVariances : ObsPort → Float
  | ObsPort.pressure => 0.0225  -- 0.15²
  | ObsPort.selectivity => 0.0225
  | ObsPort.structure => 0.0225
  | ObsPort.activity => 0.0225
  | ObsPort.regime => 1.0  -- no constraint on regime via Gaussian

/-- The constant 2πe used in Gaussian entropy. -/
def twoPiE : Float := 2.0 * 3.141592653589793 * 2.718281828459045

/-- Gaussian differential entropy: 1/2 * ln(2*pi*e*sigma^2), floored at 1e-9. -/
def gaussianEntropy (sigmaSq : Float) : Float :=
  0.5 * Float.log (twoPiE * max sigmaSq 1e-9)

/-- Gaussian KL divergence: 1/2[ln(s2_sq/s1_sq) + (s1_sq + (mu1-mu2)^2)/s2_sq - 1]. -/
def gaussianKL (mu1 sigmaSq1 mu2 sigmaSq2 : Float) : Float :=
  let s1 := max sigmaSq1 1e-9
  let s2 := max sigmaSq2 1e-9
  let d := mu1 - mu2
  0.5 * (Float.log (s2 / s1) + (s1 + d * d) / s2 - 1.0)

/-- evaluateF — the epistemic leg: ambiguity = Σ ½·ln(2πe·σ²) per channel.

This is the predicted observation entropy — "what would I learn?" Higher
predicted variance → higher ambiguity → higher EFE contribution.
Mirrors `futon5.aif.efe/gaussian-entropy` + `ambiguity`. -/
def evaluateF (variances : ObsPort → Float) : Float :=
  (gaussianEntropy (variances ObsPort.pressure)
    + gaussianEntropy (variances ObsPort.selectivity)
    + gaussianEntropy (variances ObsPort.structure)
    + gaussianEntropy (variances ObsPort.activity))

/-- evaluateG — the pragmatic leg: KL-risk = Σ KL(N(μ,σ²)‖N(C_μ,C_σ²)) per channel.

This is the divergence from the EoC preference C — "how far from confinement?"
Mirrors `futon5.aif.efe/gaussian-kl` + `risk`. -/
def evaluateG (means variances : ObsPort → Float) : Float :=
  (gaussianKL (means ObsPort.pressure) (variances ObsPort.pressure)
     (eocTargetMeans ObsPort.pressure) (eocTargetVariances ObsPort.pressure)
  + gaussianKL (means ObsPort.selectivity) (variances ObsPort.selectivity)
     (eocTargetMeans ObsPort.selectivity) (eocTargetVariances ObsPort.selectivity)
  + gaussianKL (means ObsPort.structure) (variances ObsPort.structure)
     (eocTargetMeans ObsPort.structure) (eocTargetVariances ObsPort.structure)
  + gaussianKL (means ObsPort.activity) (variances ObsPort.activity)
     (eocTargetMeans ObsPort.activity) (eocTargetVariances ObsPort.activity))

/-- gate — combine the copar legs into G_efe = risk + ambiguity.

The gate stage takes the simultaneous copar readings (evaluateF ⅋ evaluateG)
and combines them into the scalar G_efe per candidate action. Neither leg
signals the other; they are independent readings held by BV.copar. -/
def gate (means variances : ObsPort → Float) : Float :=
  evaluateF variances + evaluateG means variances

/-- The tick's evaluateF/evaluateG are the 4th seq-argument (copar position). -/
example : ∃ rest : BV Stage,
  tick = BV.seq (BV.atom Stage.step)
    (BV.seq (BV.atom Stage.perceive)
      (BV.seq (BV.atom Stage.predict)
        (BV.seq (BV.copar (BV.atom Stage.evaluateF) (BV.atom Stage.evaluateG))
          rest))) :=
  ⟨BV.seq (BV.atom Stage.gate)
    (BV.seq (BV.atom Stage.select)
      (BV.seq (BV.atom Stage.enact) (BV.atom Stage.trace))), rfl⟩

/-- evaluateF + evaluateG = gate (the gate combines the copar legs). -/
example (means variances : ObsPort → Float) :
    gate means variances = evaluateF variances + evaluateG means variances := by
  rfl

end MetaCATokamakExample

end DarkTower
