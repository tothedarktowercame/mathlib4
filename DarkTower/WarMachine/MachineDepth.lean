import Mathlib

/-!
# Machine temporal policy depth T

`predictMultiHorizon` mirrors the constant-action chaining at
`futon2:src/futon2/aif/forward_model.clj:280-310`. EFE enables it only for
depths at least two and mixes the depth-K mean with depth-one variance
(`futon2:src/futon2/aif/efe.clj:629-706`). Rollout separately defaults to two
(`futon2:src/futon2/aif/rollout.clj:474-479`). There is therefore no single
machine depth matching the registry's one range for all sums.
-/
namespace DarkTower.WarMachine.MachineDepth

def trajectory {State Action : Type} (step : State → Action → State)
    (state : State) (action : Action) : Nat → List State
  | 0 => []
  | k + 1 => let next := step state action
             next :: trajectory step next action k

def finalState {State Action : Type} (step : State → Action → State)
    (state : State) (action : Action) : Nat → State
  | 0 => state
  | k + 1 => finalState step (step state action) action k

def predictMultiHorizon {State Action : Type} (step : State → Action → State)
    (state : State) (action : Action) (k : Nat) : List State × State :=
  (trajectory step state action k, finalState step state action k)

theorem predictMultiHorizon_length {State Action : Type}
    (step : State → Action → State) (state : State) (action : Action) (k : Nat) :
    (predictMultiHorizon step state action k).1.length = k := by
  induction k generalizing state with
  | zero => rfl
  | succ k ih =>
    have h := ih (step state action)
    change (trajectory step (step state action) action k).length = k at h
    simp [predictMultiHorizon, trajectory, h]

theorem predictMultiHorizon_final {State Action : Type}
    (step : State → Action → State) (state : State) (action : Action) (k : Nat) :
    (predictMultiHorizon step state action k).2 =
      finalState step state action k := rfl

def effectiveDepth : Option Nat → Nat
  | some k => if 2 ≤ k then k else 1
  | none => 1

structure EfeDepths where
  risk : Nat
  homeostatic : Nat
  ambiguity : Nat
  information : Nat
  deriving DecidableEq, Repr

def efeDepths (requested : Option Nat) : EfeDepths :=
  let k := effectiveDepth requested
  ⟨k, k, 1, 1⟩

theorem gTermsDisagreeOnDepth (k : Nat) (hk : 2 ≤ k) :
    efeDepths (some k) = ⟨k, k, 1, 1⟩ ∧ k ≠ 1 := by
  simp [efeDepths, effectiveDepth, hk]
  omega

structure GaussianAtDepth where
  mean : Nat
  variance : Nat
  deriving DecidableEq, Repr

def mixedKlDensity (k : Nat) : GaussianAtDepth := ⟨k, 1⟩

theorem klRiskIsNotAnySingleDepthDensity :
    ∀ depth : Nat, mixedKlDensity 3 ≠ ⟨depth, depth⟩ := by
  intro depth
  simp [mixedKlDensity]
  omega

theorem someOneEqualsNone : effectiveDepth (some 1) = effectiveDepth none := by rfl

def actionSensitiveStep (state : Nat) (action : Bool) : Nat :=
  state + if action then 2 else 1

theorem varyingPolicyNotConstantAction :
    ∀ action : Bool, finalState actionSensitiveStep 0 action 2 ≠
      actionSensitiveStep (actionSensitiveStep 0 false) true := by
  intro action
  cases action <;> decide

theorem declaredDepthDefaultsDisagree : (3 : Nat) ≠ 2 ∧ (3 : Nat) = 3 := by decide

def liveDepth (eventsLoaded : Bool) (eventsNonempty : Bool) : Nat :=
  if eventsLoaded && eventsNonempty then 3 else 1

theorem noLoadedEventsMeansDepthOne : liveDepth false true = 1 := rfl

theorem machineHasNoSingleDepth :
    (efeDepths (some 3)).risk = 3 ∧
    (efeDepths (some 3)).ambiguity = 1 ∧
    mixedKlDensity 3 ≠ ⟨3, 3⟩ ∧
    effectiveDepth (some 1) = effectiveDepth none ∧
    (3 : Nat) ≠ 2 ∧ liveDepth false true = 1 := by
  decide

end DarkTower.WarMachine.MachineDepth
