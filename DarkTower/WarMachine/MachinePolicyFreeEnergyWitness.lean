import DarkTower.WarMachine.MachinePolicyFreeEnergy

/-!
# Reference witnesses for machine policy free energy

Logarithms are kept symbolic. Algebraic residual and temperature terms are
proved exactly; the companion Clojure readback measures the complete floating
terms and prints every delta against a 1e-12 tolerance.
-/

namespace DarkTower.WarMachine.MachinePolicyFreeEnergyWitness

open DarkTower.WarMachine.MachinePolicyFreeEnergy

theorem present_ne_absent : VarianceStatus.present ≠ .absent := by decide
theorem reject_ne_floor : AbsentVarianceMode.reject ≠ .floor := by decide

theorem positiveVarianceContribution :
    channelPolicyFreeEnergy ⟨1/2, 1/4, .present⟩ 0 (1/100) .reject =
      .ok ((Real.log (2 * Real.pi * (1/4)) + 1) / 2) := by
  norm_num [channelPolicyFreeEnergy, present_ne_absent, reject_ne_floor]

theorem toleratedDeterministicZero :
    channelPolicyFreeEnergy ⟨1/1000, 0, .present⟩ (1/1000) (1/100) .reject =
      .ok 0 := by
  norm_num [channelPolicyFreeEnergy, present_ne_absent, reject_ne_floor]

theorem rejectedDeterministicZero :
    channelPolicyFreeEnergy ⟨1/100, 0, .present⟩ (1/1000) (1/100) .reject =
      .error .deterministicMismatch := by
  norm_num [channelPolicyFreeEnergy, present_ne_absent, reject_ne_floor]

theorem absentZeroFloored :
    channelPolicyFreeEnergy ⟨1/10, 0, .absent⟩ 0 (1/100) .floor =
      .ok ((Real.log (2 * Real.pi * (1/100)) + 1) / 2) := by
  norm_num [channelPolicyFreeEnergy]

theorem bareZeroStillRejectsUnderFloor :
    channelPolicyFreeEnergy ⟨1/10, 0, .present⟩ 0 (1/100) .floor =
      .error .deterministicMismatch := by
  norm_num [channelPolicyFreeEnergy, present_ne_absent]

theorem negativeVarianceRejects :
    channelPolicyFreeEnergy ⟨0, -1, .present⟩ 0 (1/100) .reject =
      .error .invalidVariance := by
  norm_num [channelPolicyFreeEnergy]

/-- The registry's declared carrier, evaluated. The two channels are exactly the
`positive` candidate the Clojure readback scores (`prediction-mean {:a 0.5 :b
-0.25}`, `prediction-variance {:a 0.25 :b 1.0}`, `observation {:a 1.0 :b 0.25}`),
so the readback's two-channel total and its `f-pi-vector[0]` are measured against
THIS statement rather than against a second Clojure expression of the same
formula. Without it the composite is the one declaration in this slice with no
Lean-side value, which is the declaration the registry row names. -/
theorem machineTwoChannelTotal :
    machinePolicyFreeEnergy [⟨1/2, 1/4, .present⟩, ⟨1/2, 1, .present⟩]
        0 (1/100) .reject =
      .ok ((Real.log (2 * Real.pi * (1/4)) + 1) / 2 +
           (Real.log (2 * Real.pi * 1) + 1/4) / 2) := by
  norm_num [machinePolicyFreeEnergy, channelPolicyFreeEnergy,
    present_ne_absent, reject_ne_floor, List.foldlM, Except.bind, Except.pure,
    bind, pure, Except.ok.injEq]

theorem unscaledTauPair :
    selectionScore 0 4 3 2 .unscaled = -5 ∧
    selectionScore 0 4 3 4 .unscaled = -4 := by
  norm_num [selectionScore]

theorem scaledTauPair :
    selectionScore 0 4 3 2 .byTau = -7/2 ∧
    selectionScore 0 4 3 4 .byTau = -7/4 := by
  norm_num [selectionScore]

end DarkTower.WarMachine.MachinePolicyFreeEnergyWitness
