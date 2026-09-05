import Mathlib

/-!
# Machine temporal policy depth T

The registry line this module is about
(`futon2:holes/labs/wm-contract/aif-equations.edn`, `:id :depth`, node R13) is

    T := temporal policy depth (the range of the sums in Q(o|pi) and G)

citing da Costa 2020 eq. 42's sum over τ.  **The machine has no single T.**
`predictMultiHorizon` mirrors the constant-action chaining at
`futon2:src/futon2/aif/forward_model.clj:294-310`; EFE takes that path only for
a requested depth of at least two (`futon2:src/futon2/aif/efe.clj:629-631`) and
then evaluates risk and homeostatic pressure at depth K while ambiguity and the
predictability bonus stay at depth one (`:633-636`, `:641`, `:701`, `:705`,
`:706`).  Four call sites declare four depths.  And because the variance model
is state-blind (`:334`), the epistemic half of G cannot vary with the horizon at
all.

`Holes.lean` declares no depth or horizon quantity, so unlike slices 1–4 there
is no glossary carrier to compare against; nothing here is claimed about one.
-/
namespace DarkTower.WarMachine.MachineDepth

/-! ## The trajectory: K steps of ONE action -/

/-- The states `predict-multi-horizon` visits: `K` iterations, each feeding the
previous step's predicted state forward, **with the same `action` every step**
(`futon2:src/futon2/aif/forward_model.clj:296-310`). -/
def trajectory {State Action : Type} (step : State → Action → State)
    (state : State) (action : Action) : Nat → List State
  | 0 => []
  | k + 1 => let next := step state action
             next :: trajectory step next action k

/-- The `:final-state` the loop returns: the `K`-fold iterate under the constant
action (`futon2:src/futon2/aif/forward_model.clj:300-310`). -/
def finalState {State Action : Type} (step : State → Action → State)
    (state : State) (action : Action) : Nat → State
  | 0 => state
  | k + 1 => finalState step (step state action) action k

/-- `{:trajectory … :final-state … :horizon-steps K}`, less the echoed `K`
(`futon2:src/futon2/aif/forward_model.clj:300-303`). -/
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

/-! ## Four declared depths

Each of these is a literal in the running code, named here so that the
disagreement below is a statement about the machine's constants rather than
about numerals.  A theorem whose statement is `(3 : Nat) ≠ 2` is a fact of
arithmetic and says nothing about the machine. -/

/-- `futon2:src/futon2/aif/forward_model.clj:278` — `default-horizon-steps`,
read only by the 2-arity of `predict-multi-horizon` (`:294`). -/
def forwardModelDefaultHorizon : Nat := 3

/-- `futon2:src/futon2/aif/rollout.clj:474-479` — `rollout-horizon`'s default,
a depth belonging to the rollout apparatus, not to EFE scoring. -/
def rolloutDefaultHorizon : Nat := 2

/-- `futon2:scripts/futon2/report/war_machine.clj:6283-6285` — the live tick's
`wm-horizon-steps`, set to 3 only when the anticipation snapshot is loaded with
non-empty events, and passed into the EFE options at `:6327`. -/
def liveTickHorizon : Nat := 3

/-- `futon2:scripts/futon2/report/cascade_lane.clj:381` — `best-rollout … :depth
5` on the cascade report lane, reaching `rollout-horizon` at
`futon2:src/futon2/aif/rollout.clj:694`. -/
def cascadeLaneHorizon : Nat := 5

/-- Three of the four declared depths differ from one another.  This does NOT
say the four are pairwise distinct — `forwardModelDefaultHorizon` and
`liveTickHorizon` agree, and that agreement is stated separately below. -/
theorem declaredDepthsDisagree :
    rolloutDefaultHorizon ≠ liveTickHorizon ∧
    cascadeLaneHorizon ≠ liveTickHorizon ∧
    cascadeLaneHorizon ≠ rolloutDefaultHorizon := by decide

/-- The one agreement among the four, stated so that
`declaredDepthsDisagree` is not read as a claim of four distinct depths. -/
theorem forwardDefaultAgreesWithLiveTick :
    forwardModelDefaultHorizon = liveTickHorizon := by decide

/-! ## The EFE guard, and the depth each term of G is evaluated at -/

/-- `futon2:src/futon2/aif/efe.clj:629-631` — the multi-horizon path is taken
only when `:horizon-steps` is present and at least 2; anything else scores the
immediate next state, i.e. at depth one. -/
def effectiveDepth : Option Nat → Nat
  | some k => if 2 ≤ k then k else 1
  | none => 1

/-- The depth at which each of the four G terms is evaluated in one call. -/
structure EfeDepths where
  risk : Nat
  homeostatic : Nat
  ambiguity : Nat
  information : Nat
  deriving DecidableEq, Repr

/-- Risk (`futon2:src/futon2/aif/efe.clj:641`, through `fe-on-predicted` on
`next-mean`) and homeostatic pressure (`:706`) read the depth-K final-state
mean; ambiguity (`:701`) and the predictability bonus (`:705`) read `next-var`,
which `:636` fixes to the FIRST step's variance whatever K is. -/
def efeDepths (requested : Option Nat) : EfeDepths :=
  let k := effectiveDepth requested
  ⟨k, k, 1, 1⟩

/-- **The machine's T.**  Not a number: the registry line asks for one range
for the sums in `Q(o|pi)` and `G`, and what the machine has is a map from the
requested `:horizon-steps` to the four depths its four G terms are evaluated at
(`futon2:src/futon2/aif/efe.clj:633-636`, `:641`, `:701`, `:705`, `:706`).
`efeDepths` is the machine's inhabitant of this type. -/
abbrev machineDepth := Option Nat → EfeDepths

theorem efeDepthsIsMachineDepth : (efeDepths : machineDepth) = efeDepths := rfl

/-- For any requested depth of at least two, one evaluation of G evaluates its
terms at two different depths.  This is what makes the registry's "the range of
the sums in Q(o|pi) and G" false as written: there is no one range. -/
theorem gTermsDisagreeOnDepth (k : Nat) (hk : 2 ≤ k) :
    efeDepths (some k) = ⟨k, k, 1, 1⟩ ∧ k ≠ 1 := by
  simp [efeDepths, effectiveDepth, hk]
  omega

/-- `futon2:src/futon2/aif/efe.clj:629` — a requested depth of one is below the
guard, so it selects exactly the path that no requested depth selects. -/
theorem someOneEqualsNone : effectiveDepth (some 1) = effectiveDepth none := by rfl

/-! ## The variance model is state-blind, so the epistemic terms are
horizon-blind

`predict` computes its variance as `(predict-effects nil action)` —
`futon2:src/futon2/aif/forward_model.clj:334` passes `nil` where the state
would go — and every `:obs-variance` arm is a literal keyed by action type
alone (`:138`, `:148`, `:165`, `:172`, `:184`, `:193`, `:202`).  The state
argument is therefore discarded, which is modelled here by an `effects`
function whose state argument is `Option State` and is always applied to
`none`. -/

/-- The variance `predict` attaches to its prediction: the effects function
applied to `none` and the action, never to the state it was given. -/
def obsVariance {State Action Var : Type} (effects : Option State → Action → Var)
    (_state : State) (action : Action) : Var := effects none action

theorem obsVarianceIgnoresState {State Action Var : Type}
    (effects : Option State → Action → Var) (s s' : State) (action : Action) :
    obsVariance effects s action = obsVariance effects s' action := rfl

/-- Every step of a constant-action trajectory carries the same variance as the
first, so the depth-K variance that `futon2:src/futon2/aif/efe.clj:636`
discards is EQUAL to the depth-one variance it keeps. -/
theorem trajectoryVarianceIsConstant {State Action Var : Type}
    (effects : Option State → Action → Var) (step : State → Action → State)
    (state : State) (action : Action) (k : Nat) :
    ∀ s ∈ trajectory step state action k,
      obsVariance effects s action = obsVariance effects state action := by
  intro s _
  rfl

/-- **The sharp consequence.** Ambiguity and the predictability bonus are
functions of the variance alone, and the variance is a function of the action
alone, so those two terms of G take the same value at every horizon.  The
epistemic half of G has no τ-sum at any K — not because of the `≥ 2` guard, but
by construction.  This does NOT say the terms are constant: they vary with the
action.  It says they cannot vary with the depth. -/
theorem epistemicTermsAreHorizonBlind {State Action Var Score : Type}
    (effects : Option State → Action → Var) (epistemic : Var → Score)
    (step : State → Action → State) (state : State) (action : Action) (j k : Nat) :
    epistemic (obsVariance effects (finalState step state action j) action) =
      epistemic (obsVariance effects (finalState step state action k) action) := rfl

/-! ## The `:kl` risk density mixes two depth indices -/

/-- A Gaussian labelled by the depth its mean and its variance were taken from. -/
structure GaussianAtDepth where
  mean : Nat
  variance : Nat
  deriving DecidableEq, Repr

/-- `futon2:src/futon2/aif/efe.clj:684-685` — under the live-arena default
`:risk-mode :kl` (`:611-612`) the per-channel Gaussian takes `mu` from
`next-mean` (depth K) and `s2` from `next-var` (depth 1). -/
def mixedKlDensity (k : Nat) : GaussianAtDepth := ⟨k, 1⟩

/-- The scored density carries no single depth index, for any requested depth of
at least two.  This is a statement about the INDICES only.  It does NOT say the
two numbers differ: by `trajectoryVarianceIsConstant` the depth-one variance IS
the depth-K variance in this machine, so the mixed density's VALUES coincide
with the depth-K density's — see `mixedDensityValuesCollapse`. -/
theorem klRiskIsNotAnySingleDepthDensity (k : Nat) (hk : 2 ≤ k) :
    ∀ depth : Nat, mixedKlDensity k ≠ ⟨depth, depth⟩ := by
  intro depth h
  simp [mixedKlDensity, GaussianAtDepth.mk.injEq] at h
  omega

/-- The mixing has no numerical consequence here: with a state-blind variance
the pair (depth-K mean, depth-1 variance) that EFE scores is equal to the pair
(depth-K mean, depth-K variance) it did not compute.  The mixing rule is real;
its effect on the number is nil, and a reader who took
`klRiskIsNotAnySingleDepthDensity` for a numerical claim would have it wrong. -/
theorem mixedDensityValuesCollapse {State Action Var M : Type}
    (effects : Option State → Action → Var) (step : State → Action → State)
    (meanAt : Nat → M) (state : State) (action : Action) (k : Nat) :
    (meanAt k, obsVariance effects (finalState step state action 1) action) =
      (meanAt k, obsVariance effects (finalState step state action k) action) := rfl

/-! ## A τ-varying policy is not representable -/

/-- A step whose result depends on the action, so the statement below is not
vacuously true of a step that ignores its action. -/
def actionSensitiveStep (state : Nat) (action : Bool) : Nat :=
  state + if action then 2 else 1

/-- da Costa eq. 42 sums over τ with a policy naming an action per τ.
`predict-multi-horizon` repeats ONE action, so the two-step plan
`false` then `true` is reached by neither constant-action trajectory.  This does
NOT say the machine cannot represent plans anywhere — `rollout.clj` scores
ordered policies — only that the depth-K object EFE scores is a repetition. -/
theorem varyingPolicyNotConstantAction :
    ∀ action : Bool, finalState actionSensitiveStep 0 action 2 ≠
      actionSensitiveStep (actionSensitiveStep 0 false) true := by
  intro action
  cases action <;> decide

/-! ## Depth is conditional on data, not a parameter of the model -/

/-- `futon2:scripts/futon2/report/war_machine.clj:6283-6285`. -/
def liveDepth (eventsLoaded : Bool) (eventsNonempty : Bool) : Nat :=
  if eventsLoaded && eventsNonempty then liveTickHorizon else 1

theorem noLoadedEventsMeansDepthOne : liveDepth false true = 1 := rfl
theorem loadedEventsMeansLiveTickHorizon : liveDepth true true = liveTickHorizon := rfl

/-! ## The conjunction

The claim this module exists to make, in one proposition.  The three previous
slice reviews each found a slice whose finding existed only as separate
theorems, so a reader could check every piece and never find the claim. -/

/-- There is no single machine depth: within one evaluation of G two terms sit
at depth K and two at depth 1; the epistemic pair cannot move with K at all;
the scored `:kl` density carries no single depth index; a requested depth of one
is not a depth; three of the four declared depths differ; and whether any depth
above one is used at all is decided by whether anticipation data loaded. -/
theorem machineHasNoSingleDepth :
    (efeDepths (some liveTickHorizon)).risk = liveTickHorizon ∧
    (efeDepths (some liveTickHorizon)).ambiguity = 1 ∧
    (∀ depth : Nat, mixedKlDensity liveTickHorizon ≠ ⟨depth, depth⟩) ∧
    effectiveDepth (some 1) = effectiveDepth none ∧
    rolloutDefaultHorizon ≠ liveTickHorizon ∧
    cascadeLaneHorizon ≠ liveTickHorizon ∧
    liveDepth false true = 1 := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide⟩
  exact klRiskIsNotAnySingleDepthDensity liveTickHorizon (by decide)

end DarkTower.WarMachine.MachineDepth
