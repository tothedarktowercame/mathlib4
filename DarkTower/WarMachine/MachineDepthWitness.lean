import DarkTower.WarMachine.MachineDepth

/-!
# Concrete witnesses for the machine depth T

Every hypothesis in `MachineDepth` is discharged here for a concrete step,
effects function and epistemic functional, so that no theorem there is met by
nothing in the development.  The numbers named here are the ones the production
readback compares against.
-/
namespace DarkTower.WarMachine.MachineDepthWitness
open DarkTower.WarMachine.MachineDepth

def incrementStep (state : Nat) (_action : Unit) : Nat := state + 1

theorem depthThreeTrajectory :
    predictMultiHorizon incrementStep 0 () 3 = ([1, 2, 3], 3) := by decide

/-- Depth changes the mean: the state after three steps is not the state after
one.  Without this the depth-K/depth-1 distinction would be a distinction
between two names for the same thing. -/
theorem depthThreeDiffersFromFirst :
    (predictMultiHorizon incrementStep 0 () 3).2 ≠
      (predictMultiHorizon incrementStep 0 () 3).1.head! := by decide

theorem depthThreeMinusFirst :
    (predictMultiHorizon incrementStep 0 () 3).2 -
      (predictMultiHorizon incrementStep 0 () 3).1.head! = 2 := by decide

theorem efeDepthThreeReference : efeDepths (some liveTickHorizon) = ⟨3, 3, 1, 1⟩ := by decide
theorem nilDepthReference : effectiveDepth none = 1 := rfl
theorem oneDepthReference : effectiveDepth (some 1) = 1 := rfl

/-- The two independent defaults, as the named machine constants rather than as
numerals: `(2 : Nat) = 2` would have been a fact of arithmetic. -/
theorem forwardDefaultReference : forwardModelDefaultHorizon = 3 := rfl
theorem rolloutDefaultReference : rolloutDefaultHorizon = 2 := rfl
theorem cascadeLaneReference : cascadeLaneHorizon = 5 := rfl

/-! ## The state-blind variance, made concrete

`obsVariance` and the theorems above it hold for an arbitrary `effects`; here is
one that behaves like `predict-effects`' `:address-sorry` arm
(`futon2:src/futon2/aif/forward_model.clj:129-140`, `:obs-variance
{:sorry-count-norm 0.01 :mission-health 0.005}`), scaled to `Nat` so the
witnesses are decidable: the variance depends on the action and not on the
state, even though the state argument is offered. -/
def addressSorryEffects : Option Nat → Unit → Nat
  | _, _ => 1

/-- Every step of the depth-three trajectory carries variance 1, the same value
the first step carries — the discarded depth-K variance equals the retained
depth-one one. -/
theorem trajectoryVarianceIsOne :
    ∀ s ∈ trajectory incrementStep 0 () 3,
      obsVariance addressSorryEffects s () = 1 := by decide

/-- `epistemicTermsAreHorizonBlind` discharged for a concrete epistemic
functional (doubling stands in for `ambiguity-by-channel` /
`predictability-bonus`, both functions of the variance alone): its value at
depth three equals its value at depth one, and the difference is exactly 0. -/
theorem epistemicAtThreeEqualsAtOne :
    (fun v => 2 * v) (obsVariance addressSorryEffects (finalState incrementStep 0 () 3) ()) =
      (fun v => 2 * v) (obsVariance addressSorryEffects (finalState incrementStep 0 () 1) ()) :=
  epistemicTermsAreHorizonBlind addressSorryEffects (fun v => 2 * v) incrementStep 0 () 3 1

/-- `klRiskIsNotAnySingleDepthDensity` discharged at the live tick's depth. -/
theorem mixedDensityAtLiveDepth : ∀ depth : Nat, mixedKlDensity liveTickHorizon ≠ ⟨depth, depth⟩ :=
  klRiskIsNotAnySingleDepthDensity liveTickHorizon (by decide)

/-- The τ-varying plan and the two constant-action trajectories, as numbers:
`false`-then-`true` reaches 3, constant `false` reaches 2, constant `true`
reaches 4. -/
theorem varyingPlanReachesThree :
    actionSensitiveStep (actionSensitiveStep 0 false) true = 3 ∧
    finalState actionSensitiveStep 0 false 2 = 2 ∧
    finalState actionSensitiveStep 0 true 2 = 4 := by decide

theorem liveDepthWitness : liveDepth false true = 1 ∧ liveDepth true true = 3 := by decide

end DarkTower.WarMachine.MachineDepthWitness
