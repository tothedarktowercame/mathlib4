import Mathlib
import DarkTower.WarMachine.CommitmentTemperature

/-!
# Machine selection temperature τ

This module states the numeric quantity supplied to policy scoring. It is
distinct from `CommitmentTemperature`, which asks whether that quantity can
change the selected action; its `live_selector_does_not_govern` theorem is the
downstream channel result. Exact `ℝ` arithmetic is used so the three laws and
their reductions are proved without floating approximation. Non-finite machine
inputs are represented explicitly rather than pretending `ℝ` contains NaN.
-/
namespace DarkTower.WarMachine.MachineTemperature

/-- The three dispatch arms of `effective-temperature`
(`futon2:src/futon2/aif/policy.clj:128-143`). -/
inductive TauMode | spread | selectionGainOnly | variationalBetaGamma
  deriving DecidableEq, Repr

/-- The finite/non-finite distinction checked by `finite-pos?`
(`futon2:src/futon2/aif/policy.clj:47-55`). -/
inductive MachineNumber
  | finite (value : ℝ)
  | nonfinite

/-- Inputs to the three temperature laws (`futon2:src/futon2/aif/policy.clj:124-143`). -/
structure TemperatureOpts where
  mode : TauMode
  tauMin : ℝ
  spreadTemperature : ℝ
  selectionGain : ℝ
  variationalBeta : Option MachineNumber := none

/-- The variational arm refuses missing, non-finite, zero, and negative β rather
than falling back to `1/g` (`futon2:src/futon2/aif/policy.clj:135-141`). -/
inductive TemperatureError | invalidVariationalBeta deriving DecidableEq, Repr

/-- The machine's three-law, partially defined selection temperature. The gain
floor belongs only to the two engineering modes; β is validated but not floored
(`futon2:src/futon2/aif/policy.clj:118-141`). -/
noncomputable def machineTemperature (opts : TemperatureOpts) : Except TemperatureError ℝ :=
  let g := max opts.tauMin opts.selectionGain
  match opts.mode with
  | .spread => .ok (opts.spreadTemperature / g)
  | .selectionGainOnly => .ok (1 / g)
  | .variationalBetaGamma =>
      match opts.variationalBeta with
      | some (.finite beta) => if 0 < beta then .ok beta else .error .invalidVariationalBeta
      | _ => .error .invalidVariationalBeta

/-- At gain one, the spread arm is exactly τ_spread and the gain-only arm is
exactly one (`futon2:src/futon2/aif/policy.clj:113-117`). -/
theorem gainOneReductions (spread tauMin : ℝ) (hmin : tauMin ≤ 1) :
    machineTemperature ⟨.spread, tauMin, spread, 1, none⟩ = .ok spread ∧
    machineTemperature ⟨.selectionGainOnly, tauMin, spread, 1, none⟩ = .ok 1 := by
  simp [machineTemperature, max_eq_right hmin]

/-- Positive β is returned exactly, even below `tauMin`; the floor is not
shared with the variational law (`futon2:src/futon2/aif/policy.clj:118-123,135-141`). -/
theorem betaIsNotFloored (beta tauMin spread gain : ℝ) (hbeta : 0 < beta) :
    machineTemperature ⟨.variationalBetaGamma, tauMin, spread, gain,
      some (.finite beta)⟩ = .ok beta := by
  simp [machineTemperature, hbeta]

/-- Missing β rejects and never becomes the selection-gain result
(`futon2:src/futon2/aif/policy.clj:135-141`). -/
theorem missingBetaNeverFallsBack (tauMin spread gain : ℝ) :
    machineTemperature ⟨.variationalBetaGamma, tauMin, spread, gain, none⟩ =
      .error .invalidVariationalBeta := rfl

/-- `effective-temperature` defaults to spread
(`futon2:src/futon2/aif/policy.clj:128-129`). -/
def policyFunctionDefault : TauMode := .spread

/-- The unset arena environment selects gain-only
(`futon2:scripts/futon2/report/war_machine.clj:865-869`). -/
def liveArenaDefault : TauMode := .selectionGainOnly

/-- The function and live-arena defaults name different laws
(`policy.clj:128-129`; `war_machine.clj:865-869`). -/
theorem temperatureDefaultsDisagree : policyFunctionDefault ≠ liveArenaDefault := by decide

/-- Carry provenance attached to variational β
(`futon2:src/futon2/aif/policy_precision.clj:497-560`). -/
inductive BetaSource | convergedPosterior | heldUnsolved | heldAbsent | initial
  deriving DecidableEq, Repr

/-- Only this source says the β was solved on the current tick
(`futon2:src/futon2/aif/policy_precision.clj:551-560`). -/
def solvedThisTick : BetaSource → Bool | .convergedPosterior => true | _ => false

/-- Mode names the law; source independently records whether its β was solved
(`futon2:src/futon2/aif/policy.clj:57-75`). -/
theorem variationalModeCanCarryHeldBeta :
    solvedThisTick .heldUnsolved = false ∧ solvedThisTick .heldAbsent = false ∧
      solvedThisTick .initial = false := by decide

/-- The score consumes τ as `-G/τ`
(`futon2:src/futon2/aif/policy.clj:157-214`). -/
noncomputable def temperatureScore (g tau : ℝ) : ℝ := -g / tau

/-- The default head selector does not read τ, while full-score selection does;
this is the numeric seam behind
`CommitmentTemperature.live_selector_does_not_govern`
(`futon2:src/futon2/aif/policy.clj:567-594`). -/
inductive SelectionLaw | controllerHead | fullScorePosterior deriving DecidableEq, Repr

/-- Whether the chosen-action branch consults the τ-scaled full scores
(`futon2:src/futon2/aif/policy.clj:567-594`). -/
def temperatureReachesChoice : SelectionLaw → Bool
  | .controllerHead => false | .fullScorePosterior => true

/-- The τ-to-action channel is severed under the head law and live under the
full-score law (`futon2:src/futon2/aif/policy.clj:567-594`). -/
theorem selectionLawControlsTemperatureChannel :
    temperatureReachesChoice .controllerHead = false ∧
      temperatureReachesChoice .fullScorePosterior = true := by decide


/-! ## Repairs by the reviewing seat

The delivered module dispatched over three laws without ever stating that they
are three, left the registry's own `gamma = 1/beta` unmentioned, took the spread
law's value as an opaque input rather than computing it, and asserted the
tau-to-choice channel instead of deriving it.  What follows closes those four
gaps. -/

/-! ### The spread law is computed, not assumed -/

/-- `(apply max g-totals) - (apply min g-totals)`, the spread
`adaptive-temperature` divides (`futon2:src/futon2/aif/policy.clj:41`). -/
noncomputable def gRange : List ℝ → ℝ
  | [] => 0
  | x :: xs => (xs.foldl max x) - (xs.foldl min x)

/-- `adaptive-temperature` itself (`futon2:src/futon2/aif/policy.clj:33-45`):
`max tauMin (range G / k)`, production defaults `tauMin = 1/100`, `k = 5`.  The
delivered module took this value as the opaque field `spreadTemperature`; it is
a named production function with a floor of its own, and the floor is the
reason a degenerate candidate set cannot divide tau to zero. -/
noncomputable def adaptiveTemperature (tauMin k : ℝ) : List ℝ → ℝ
  | [] => tauMin
  | gs => max tauMin (gRange gs / k)

/-- Measured at HEAD (`runs/F8-temperature/review-independent-probe.txt`, line
`tau-spread g-totals`): the four-candidate field `[1, 2, 7/2, 1/2]` has range 3
and gives `tau_spread = 3/5`. -/
theorem adaptiveTemperatureReference :
    adaptiveTemperature (1/100) 5 [1, 2, 7/2, 1/2] = 3/5 := by
  norm_num [adaptiveTemperature, gRange]

/-- An empty candidate list returns the floor rather than dividing
(`futon2:src/futon2/aif/policy.clj:43`).  Measured: `0.01`. -/
theorem emptySpreadIsTheFloor (tauMin k : ℝ) :
    adaptiveTemperature tauMin k [] = tauMin := rfl

/-- The floor's stated purpose: identical EFE inputs give range 0, and the
result is `tauMin`, not `0` (`futon2:src/futon2/aif/policy.clj:36-38`).
Measured on `[2, 2, 2]`: `0.01`. -/
theorem degenerateSpreadIsTheFloor :
    adaptiveTemperature (1/100) 5 [2, 2, 2] = 1/100 := by
  norm_num [adaptiveTemperature, gRange]

/-! ### There is no single tau: the three laws disagree on one input -/

/-- One input, read by all three laws.  `tauMin = 1/100` and `k = 5` are
production's defaults; the field is `adaptiveTemperatureReference`'s, the gain
is 2, and a valid `beta = 1/4` is present so that no law is refused for want of
an input.  This is the probe's configuration
(`runs/F8-temperature/review-independent-probe.txt`). -/
noncomputable def probeOpts (mode : TauMode) : TemperatureOpts :=
  ⟨mode, 1/100, 3/5, 2, some (.finite (1/4))⟩

/-- **The finding the row exists for.**  The registry line names one quantity,
`tau`.  On a single input at which every law is defined, the three laws return
three different numbers, so `tau` does not denote until a mode is named.
Measured at HEAD: `0.3`, `0.5`, `0.25`
(`runs/F8-temperature/review-independent-probe.txt`, the three `law :` lines). -/
theorem threeLawsDisagree :
    machineTemperature (probeOpts .spread) = .ok (3/10) ∧
    machineTemperature (probeOpts .selectionGainOnly) = .ok (1/2) ∧
    machineTemperature (probeOpts .variationalBetaGamma) = .ok (1/4) ∧
    (3/10 : ℝ) ≠ 1/2 ∧ (3/10 : ℝ) ≠ 1/4 ∧ (1/2 : ℝ) ≠ 1/4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [machineTemperature, probeOpts]

/-! ### The registry's own equation, and the two laws it is false of -/

/-- The registry `:eq` line is `friston2017 eq. 2.1 (gamma = 1/beta)`
(`futon2:holes/labs/wm-contract/aif-equations.edn`, `:id :temperature`).  The
score divides by tau (`futon2:src/futon2/aif/policy.clj:209`), so the precision
the machine actually applies is `1/tau`. -/
noncomputable def machineGamma (tau : ℝ) : ℝ := 1 / tau

/-- Under the variational law, and only there, the registry equation holds
exactly: `tau = beta`, hence `gamma = 1/beta`
(`futon2:src/futon2/aif/policy.clj:135-141`). -/
theorem variationalGammaIsInverseBeta (beta tauMin spread gain : ℝ) (hbeta : 0 < beta) :
    (machineTemperature ⟨.variationalBetaGamma, tauMin, spread, gain,
      some (.finite beta)⟩).map machineGamma = .ok (1 / beta) := by
  rw [betaIsNotFloored beta tauMin spread gain hbeta]
  rfl

/-- And it is false of the other two.  On `probeOpts`, where `beta = 1/4` is
present and `1/beta = 4`, the two engineering laws yield `gamma = 10/3` and
`gamma = 2`.  Neither is `1/beta`, so the registry's `:eq` describes one of the
three arms rather than the quantity the row names. -/
theorem engineeringGammaIsNotInverseBeta :
    (machineTemperature (probeOpts .spread)).map machineGamma = .ok (10/3) ∧
    (machineTemperature (probeOpts .selectionGainOnly)).map machineGamma = .ok 2 ∧
    (10/3 : ℝ) ≠ 4 ∧ (2 : ℝ) ≠ 4 := by
  obtain ⟨hspread, hgain, -, -, -, -⟩ := threeLawsDisagree
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · rw [hspread]; simp only [Except.map, machineGamma, Except.ok.injEq]; norm_num
  · rw [hgain]; simp only [Except.map, machineGamma, Except.ok.injEq]; norm_num

/-! ### The gain floor bites, and beta's does not exist -/

/-- The other half of `betaIsNotFloored`.  In the two engineering modes a
degenerate gain is floored to `tauMin` before the division
(`futon2:src/futon2/aif/policy.clj:132`), so `g = 0` gives `1/tauMin` rather
than a division by zero.  Without this the "not floored" claim about beta has
nothing to contrast with. -/
theorem gainFloorPreventsDivisionByZero (tauMin spread : ℝ) (h : 0 ≤ tauMin) :
    machineTemperature ⟨.selectionGainOnly, tauMin, spread, 0, none⟩ = .ok (1 / tauMin) := by
  simp [machineTemperature, max_eq_left h]

/-! ### What tau does to the scores, and when it can reach the choice -/

/-- `selection-scores`: the habit prior enters UNSCALED and `G` is divided
(`futon2:src/futon2/aif/policy.clj:207-209`; the semantic commitment is stated
at `:225-229` -- "controller temperature modulates G, never the habit prior"). -/
noncomputable def selectionScore (lnE g tau : ℝ) : ℝ := lnE + temperatureScore g tau

/-- Raising tau contracts the gap between two candidates' scores.  This is what
the word "temperature" names here, and the delivered module defined
`temperatureScore` without ever saying it.  Measured at HEAD on `G = [1, 0]`:
gap `1.0` at `tau = 1`, gap `0.1` at `tau = 10`
(`runs/F8-temperature/review-independent-probe.txt`, the two
`selection-scores` lines). -/
theorem largerTemperatureFlattensScores (g₁ g₂ τ₁ τ₂ : ℝ)
    (hg : g₁ < g₂) (hτ₁ : 0 < τ₁) (hτ : τ₁ < τ₂) :
    temperatureScore g₁ τ₂ - temperatureScore g₂ τ₂ <
      temperatureScore g₁ τ₁ - temperatureScore g₂ τ₁ := by
  have hgap : ∀ τ : ℝ, temperatureScore g₁ τ - temperatureScore g₂ τ = (g₂ - g₁) / τ := by
    intro τ; simp only [temperatureScore]; ring
  rw [hgap, hgap]
  exact div_lt_div_of_pos_left (sub_pos.mpr hg) hτ₁ hτ

/-- **Why the head law's tau-blindness is structural rather than an accident.**
For any positive tau, `g ↦ -g/tau` is strictly antitone, so every positive tau
induces the SAME order on the candidates.  With a zero habit prior -- the
production default -- no argmax over the tau-scaled scores can move with tau at
any temperature.  The delivered module asserted the severed channel; this is
the reason for it. -/
theorem zeroPriorOrderIsTemperatureInvariant (g₁ g₂ τ₁ τ₂ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) :
    (selectionScore 0 g₁ τ₁ < selectionScore 0 g₂ τ₁) ↔
      (selectionScore 0 g₁ τ₂ < selectionScore 0 g₂ τ₂) := by
  have key : ∀ τ : ℝ, 0 < τ →
      ((selectionScore 0 g₁ τ < selectionScore 0 g₂ τ) ↔ g₂ < g₁) := by
    intro τ hτ
    simp only [selectionScore, temperatureScore, zero_add, neg_div]
    rw [neg_lt_neg_iff, div_lt_div_iff_of_pos_right hτ]
  rw [key τ₁ hτ₁, key τ₂ hτ₂]

/-- And the converse: tau reaches the choice only through the unscaled habit
prior.  The measured production case
(`runs/F8-temperature/review-independent-probe.txt`, the three `habit branch`
lines): cautious `⟨lnE 0, G 0⟩` against habitual `⟨lnE 1, G 2⟩`.  At `tau = 1/2`
cautious scores higher; at `tau = 8` habitual does.  Production selected
`:cautious` and `:habitual` respectively at exactly these temperatures. -/
theorem habitPriorMakesOrderTemperatureDependent :
    selectionScore 1 2 (1/2) < selectionScore 0 0 (1/2) ∧
    selectionScore 0 0 8 < selectionScore 1 2 8 := by
  constructor <;> norm_num [selectionScore, temperatureScore]

#print axioms gRange
#print axioms adaptiveTemperature
#print axioms adaptiveTemperatureReference
#print axioms emptySpreadIsTheFloor
#print axioms degenerateSpreadIsTheFloor
#print axioms probeOpts
#print axioms threeLawsDisagree
#print axioms machineGamma
#print axioms variationalGammaIsInverseBeta
#print axioms engineeringGammaIsNotInverseBeta
#print axioms gainFloorPreventsDivisionByZero
#print axioms selectionScore
#print axioms largerTemperatureFlattensScores
#print axioms zeroPriorOrderIsTemperatureInvariant
#print axioms habitPriorMakesOrderTemperatureDependent
#print axioms TauMode
#print axioms MachineNumber
#print axioms TemperatureOpts
#print axioms TemperatureError
#print axioms machineTemperature
#print axioms gainOneReductions
#print axioms betaIsNotFloored
#print axioms missingBetaNeverFallsBack
#print axioms policyFunctionDefault
#print axioms liveArenaDefault
#print axioms temperatureDefaultsDisagree
#print axioms BetaSource
#print axioms solvedThisTick
#print axioms variationalModeCanCarryHeldBeta
#print axioms temperatureScore
#print axioms SelectionLaw
#print axioms temperatureReachesChoice
#print axioms selectionLawControlsTemperatureChannel

end DarkTower.WarMachine.MachineTemperature
