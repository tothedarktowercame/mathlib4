import DarkTower.WarMachine.MachineBeliefUpdate

/-!
# The machine policy free energy F_pi

This module states the map run by `f-pi-for-candidate`
(`futon2:src/futon2/aif/policy_free_energy.clj:41-144`) and the score seam run
by `selection-scores` (`futon2:src/futon2/aif/policy.clj:157-211`). Logarithms
remain symbolic in Lean: the witness proves the algebraic terms exactly, while
the production readback reports whole-term floating deltas at tolerance 1e-12.
-/

namespace DarkTower.WarMachine.MachinePolicyFreeEnergy

inductive VarianceStatus | present | absent deriving DecidableEq, Repr
inductive AbsentVarianceMode | reject | floor deriving DecidableEq, Repr
inductive PolicyFreeEnergyError | invalidVariance | deterministicMismatch
  deriving DecidableEq, Repr

structure ChannelDatum where
  residual : ℝ
  variance : ℝ
  varianceStatus : VarianceStatus := .present

noncomputable def channelPolicyFreeEnergy
    (datum : ChannelDatum) (tolerance floor : ℝ)
    (mode : AbsentVarianceMode) : Except PolicyFreeEnergyError ℝ :=
  let effectiveVariance :=
    if datum.variance = 0 ∧ datum.varianceStatus = .absent ∧ mode = .floor
    then floor else datum.variance
  if effectiveVariance < 0 then .error .invalidVariance
  else if effectiveVariance = 0 then
    if |datum.residual| ≤ tolerance then .ok 0
    else .error .deterministicMismatch
  else .ok ((Real.log (2 * Real.pi * effectiveVariance) +
    datum.residual ^ 2 / effectiveVariance) / 2)

/-- The single composite carrier for the registry's `F_pi` row. -/
noncomputable def machinePolicyFreeEnergy
    (channels : List ChannelDatum) (tolerance floor : ℝ)
    (mode : AbsentVarianceMode) : Except PolicyFreeEnergyError ℝ :=
  channels.foldlM (fun total datum =>
    return total + (← channelPolicyFreeEnergy datum tolerance floor mode)) 0

/-- Exact branch table: negative rejects; positive scores; a bare zero is
deterministic; only an absent zero under floor mode is replaced by the floor. -/
theorem varianceTrichotomy (r tolerance floor : ℝ) (hfloor : 0 < floor) :
    channelPolicyFreeEnergy ⟨r, -1, .present⟩ tolerance floor .reject =
        .error .invalidVariance ∧
    channelPolicyFreeEnergy ⟨r, 1, .present⟩ tolerance floor .reject =
        .ok ((Real.log (2 * Real.pi) + r ^ 2) / 2) ∧
    (channelPolicyFreeEnergy ⟨r, 0, .present⟩ tolerance floor .floor =
       if |r| ≤ tolerance then .ok 0 else .error .deterministicMismatch) ∧
    channelPolicyFreeEnergy ⟨r, 0, .absent⟩ tolerance floor .floor =
        .ok ((Real.log (2 * Real.pi * floor) + r ^ 2 / floor) / 2) := by
  have hfloorNonnegative : 0 ≤ floor := le_of_lt hfloor
  simp [channelPolicyFreeEnergy, hfloorNonnegative, ne_of_gt hfloor]

/-- A successful production result is a real-valued total. `ℝ` has neither
NaN nor infinities; failure remains in the `Except` branch. -/
theorem successfulTotalIsFinite (channels : List ChannelDatum)
    (tolerance floor total : ℝ) (mode : AbsentVarianceMode)
    (h : machinePolicyFreeEnergy channels tolerance floor mode = .ok total) :
    ∃ finiteTotal : ℝ, machinePolicyFreeEnergy channels tolerance floor mode =
      .ok finiteTotal := ⟨total, h⟩

inductive FPiScaling | unscaled | byTau deriving DecidableEq, Repr

noncomputable def selectionScore (logPrior g fPi tau : ℝ)
    (scaling : FPiScaling) : ℝ :=
  logPrior - g / tau - match scaling with
    | .unscaled => fPi
    | .byTau => fPi / tau

/-- Under the default arm, changing tau changes only the G contribution;
under `byTau`, the F_pi contribution changes with tau as well. -/
theorem policyFreeEnergyEntersUnscaled (lp g f t₁ t₂ : ℝ) :
    selectionScore lp g f t₁ .unscaled - selectionScore lp g 0 t₁ .unscaled = -f ∧
    selectionScore lp g f t₂ .unscaled - selectionScore lp g 0 t₂ .unscaled = -f ∧
    selectionScore lp g f t₁ .byTau - selectionScore lp g 0 t₁ .byTau = -f / t₁ := by
  simp [selectionScore]
  ring

end DarkTower.WarMachine.MachinePolicyFreeEnergy
