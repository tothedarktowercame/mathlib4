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
