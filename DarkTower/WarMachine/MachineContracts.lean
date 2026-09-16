import DarkTower.WarMachine.MachineObservation
import DarkTower.WarMachine.MachineBeliefState
import DarkTower.WarMachine.MachineBeliefUpdate
import DarkTower.WarMachine.MachinePrecision
import DarkTower.WarMachine.MachineDepth
import DarkTower.WarMachine.MachineTemperature
import DarkTower.WarMachine.MachineAction
import DarkTower.WarMachine.MachinePredictionError
import DarkTower.WarMachine.TokenState
import DarkTower.WarMachine.CascadeTransition
import DarkTower.WarMachine.PolicyRollout
import DarkTower.WarMachine.TokenObservation
import DarkTower.WarMachine.TokenPreference
import DarkTower.WarMachine.PolicyHorizon
import DarkTower.WarMachine.ExactBeliefTrajectory

/-!
Leaf registry for the War Machine's Lean→Clojure contracts. Checked name quotations
bind each reference to an elaborated declaration. Each entry's `holder` states its
claim: `model-transcription-only` entries (2026-09-12) assert no runtime
correspondence; `runtime-correspondence-not-live-path` entries assert that the named
Clojure function computes the Lean declaration, checked by the named behavioural
fixture test, and that the function is not yet called on the live War Machine path
(`p4ng/wm-walkthroughs/build-loop/closure/ALIGNMENT.md` item 4).

Scope of the `wm-cascade-transition` and `wm-policy-rollout` claims: they cover
add-only pattern effects. When effects retract established tokens, enactment
(`receipt_construction` acting order) and prediction are known to differ; the test
`enactment-prediction-divergence-with-retraction` asserts that difference, and
proposal P10 (with Joe) decides it. No correspondence is claimed there.
Registration date is the date of this registry, not a historical closure date.
Holes imports none of these registries. The companion script pins emitted bytes
and checks each owning source against its committed tree before and after emission.
-/
namespace DarkTower.WarMachine.MachineContracts
open Lean DarkTower.Contract.Emit

private def entry (decl : Name) (owner locus fixture evidence falsifier : String) : DarkTower.Contract.Emit.Declaration :=
  { name := decl.toString, kind := .closed
    signature := "checked-reference:" ++ decl.toString
    owner := owner, holder := "model-transcription-only", decided := "2026-09-12"
    clojureLocus := some locus, fixture := some fixture
    evidence := some evidence, falsifier := some falsifier }

/-- An aligned entry: a runtime function that computes the Lean declaration. -/
private def runtimeEntry (decl : Name) (holder decided owner locus fixture evidence falsifier : String) :
    DarkTower.Contract.Emit.Declaration :=
  { name := decl.toString, kind := .closed
    signature := "checked-reference:" ++ decl.toString
    owner := owner, holder := holder, decided := decided
    clojureLocus := some locus, fixture := some fixture
    evidence := some evidence, falsifier := some falsifier }

private def notLivePath : String := "runtime-correspondence-not-live-path"

/-- The runtime function is called on the live War Machine path, but its result is only
recorded; it does not select or change enacted output. The owner string names the live
call site as `live-call-site=path:line`, which the verifier resolves to a call. -/
private def liveShadow : String := "runtime-correspondence-live-shadow"

/-- The named Clojure function computes the Lean declaration except on a known,
named input class, recorded first in the falsifier: the Lean moved ahead (an approved
design change) and the runtime has not caught up. -/
private def lagging : String := "runtime-correspondence-lagging"

def registries : List Registry := [
  { schemaVersion := 1, contractId := "wm-machine-observe",
    moduleName := "DarkTower.WarMachine.MachineObservation",
    declarations := [entry ``DarkTower.WarMachine.MachineObservation.machineObservation
      "R2: machine-model transcription; no runtime correspondence claim"
      "futon2/src/futon2/aif/observation.clj:103"
      "futon2/holes/labs/wm-contract/runs/F8-observe/clojure-readback.txt:1"
      "mathlib4/DarkTower/WarMachine/MachineObservationWitness.lean:1"
      "Envelope variant/value mismatch is accepted, or declared coordinate reference differs."] },
  { schemaVersion := 1, contractId := "wm-machine-belief-state",
    moduleName := "DarkTower.WarMachine.MachineBeliefState",
    declarations := [entry ``DarkTower.WarMachine.MachineBeliefState.machineBeliefState
      "R1: machine-model transcription; no runtime correspondence claim"
      "futon2/src/futon2/aif/belief.clj:510"
      "futon2/holes/labs/wm-contract/runs/F8-belief-state/clojure-readback.txt:1"
      "mathlib4/DarkTower/WarMachine/MachineBeliefStateWitness.lean:1"
      "Carry loses a surviving posterior, loses a new prior, or retains an absent entity."] },
  { schemaVersion := 1, contractId := "wm-machine-belief-update",
    moduleName := "DarkTower.WarMachine.MachineBeliefUpdate",
    declarations := [entry ``DarkTower.WarMachine.MachineBeliefUpdate.machineBeliefUpdate
      "R3: machine-model transcription; no runtime correspondence claim"
      "futon2/src/futon2/aif/belief.clj:297"
      "futon2/holes/labs/wm-contract/runs/F8-belief-update/clojure-readback.txt:1"
      "mathlib4/DarkTower/WarMachine/MachineBeliefUpdateWitness.lean:1"
      "Zero inconsistency moves a normalized prior, or declared categorical tempering differs."] },
  { schemaVersion := 1, contractId := "wm-machine-precision",
    moduleName := "DarkTower.WarMachine.MachinePrecision",
    declarations := [entry ``DarkTower.WarMachine.MachinePrecision.machinePrecision
      "R7: machine-model transcription; no runtime correspondence claim"
      "futon2/src/futon2/aif/precision.clj:116"
      "futon2/holes/labs/wm-contract/runs/F8-precision/clojure-readback.txt:1"
      "mathlib4/DarkTower/WarMachine/MachinePrecisionWitness.lean:1"
      "Window variance, separate-mode salience, floor or cap disagrees with declared parameters."] },
  { schemaVersion := 1, contractId := "wm-machine-depth",
    moduleName := "DarkTower.WarMachine.MachineDepth",
    declarations := [entry ``DarkTower.WarMachine.MachineDepth.machineDepth
      "R13: machine-model transcription; no runtime correspondence claim"
      "futon2/src/futon2/aif/efe.clj:633"
      "futon2/holes/labs/wm-contract/runs/F8-depth/clojure-readback.txt:1"
      "mathlib4/DarkTower/WarMachine/MachineDepthWitness.lean:1"
      "Four-term depth tuple differs; a single-depth claim hides unequal component depths."] },
  { schemaVersion := 1, contractId := "wm-machine-temperature",
    moduleName := "DarkTower.WarMachine.MachineTemperature",
    declarations := [entry ``DarkTower.WarMachine.MachineTemperature.machineTemperature
      "R14: machine-model transcription; no runtime correspondence claim"
      "futon2/src/futon2/aif/policy.clj:77"
      "futon2/holes/labs/wm-contract/runs/F8-temperature/clojure-readback.txt:1"
      "mathlib4/DarkTower/WarMachine/MachineTemperatureWitness.lean:1"
      "Wrong mode temperature, floored valid beta, or accepted invalid variational beta."] },
  { schemaVersion := 1, contractId := "wm-machine-action",
    moduleName := "DarkTower.WarMachine.MachineAction",
    declarations := [entry ``DarkTower.WarMachine.MachineAction.machineAction
      "R16: machine-model transcription; no runtime correspondence claim"
      "futon2/src/futon2/aif/policy.clj:672"
      "futon2/holes/labs/wm-contract/runs/F8-action/clojure-readback.txt:1"
      "mathlib4/DarkTower/WarMachine/MachineActionWitness.lean:1"
      "Declared boundary/law choice, tie rule, fallback or no-op exclusion differs."] },
  { schemaVersion := 1, contractId := "wm-machine-prediction-error",
    moduleName := "DarkTower.WarMachine.MachinePredictionError",
    declarations := [entry ``DarkTower.WarMachine.MachinePredictionError.machineChannelPredictionError
      "R3a-host-proposed: machine-model transcription; no runtime correspondence claim"
      "futon2/src/futon2/aif/free_energy.clj:203"
      "futon2/holes/labs/wm-contract/runs/F8-prediction-error/clojure-readback.txt:1"
      "mathlib4/DarkTower/WarMachine/MachinePredictionErrorWitness.lean:1"
      "Prediction triple refusal/absence/present precedence or observed-minus-mean differs."] },
  { schemaVersion := 1, contractId := "wm-token-state",
    moduleName := "DarkTower.WarMachine.TokenState",
    declarations := [
      runtimeEntry ``DarkTower.WarMachine.TokenState.observedBelief notLivePath "2026-09-16"
        "WM-02 (P2/P4): point-mass q0 on the observed token set"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:114"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:59"
        "mathlib4/DarkTower/WarMachine/TokenState.lean:45"
        "The runtime row is not a point mass summing to 1 on the observed token set.",
      runtimeEntry ``DarkTower.WarMachine.TokenState.independentBelief notLivePath "2026-09-16"
        "WM-02 (P2/P4): independent-token q0 over the token powerset"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:124"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:72"
        "mathlib4/DarkTower/WarMachine/TokenState.lean:136"
        "(independent-belief {\"t0\" 3/2 \"t1\" 1/2} #{\"t0\" \"t1\"}) does not refuse with :invalid-token-probability; or all-0/1 probabilities do not reduce to observed-belief (independentBelief_eq_observedBelief, TokenState.lean:153).",
      runtimeEntry ``DarkTower.WarMachine.TokenState.coverage notLivePath "2026-09-16"
        "WM-02 (P2): want-signature coverage |want ∩ s| / |want|"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:145"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:72"
        "mathlib4/DarkTower/WarMachine/TokenState.lean:56"
        "(coverage #{} state) does not refuse with :empty-want-signature; or coverage leaves [0,1], is 1 without want ⊆ s, or decreases as s grows (coverage_le_one :60, coverage_eq_one_iff :65, coverage_mono :83)."] },
  { schemaVersion := 1, contractId := "wm-cascade-transition",
    moduleName := "DarkTower.WarMachine.CascadeTransition",
    declarations := [
      runtimeEntry ``DarkTower.WarMachine.CascadeTransition.patternKernel notLivePath "2026-09-16"
        "WM-03 (P3): interpreted pattern kernel, success probability theta; add-only effects"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:242"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:120"
        "mathlib4/DarkTower/WarMachine/CascadeTransition.lean:57"
        "(pattern-kernel p s) with theta = 3/2 does not refuse with :invalid-pattern-interpretation; or a row does not sum to 1 (patternKernel_rowsum :50), or an achieved pattern moves the state (patternKernel_of_achieved :57).",
      runtimeEntry ``DarkTower.WarMachine.CascadeTransition.firstEnabled lagging "2026-09-16"
        "WM-03 (P3): first enabled pattern in precedence; guard consumes ⊆ s ∧ Disjoint forbids s"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:262"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:141"
        "mathlib4/DarkTower/WarMachine/CascadeTransition.lean:82"
        "LAGGING (P10, mathlib4 95127698bd): the Lean guard adds ¬(produces ⊆ s); Clojure guard-holds? (cascade_model_manifest.clj:105) does not yet, so runtime and Lean disagree whenever an achieved pattern is first in precedence. Other falsifiers: A pattern whose forbids set meets s is selected (firstEnabled_skips_forbidden :82).",
      runtimeEntry ``DarkTower.WarMachine.CascadeTransition.cascadeKernel lagging "2026-09-16"
        "WM-03 (P3): first-enabled cascade kernel; identity when no pattern is enabled; add-only effects"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:277"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:141"
        "mathlib4/DarkTower/WarMachine/CascadeTransition.lean:116"
        "LAGGING (P10, mathlib4 95127698bd): the Lean guard adds ¬(produces ⊆ s); Clojure guard-holds? (cascade_model_manifest.clj:105) does not yet, so runtime and Lean disagree whenever an achieved pattern is first in precedence. Other falsifiers: A cascade row does not sum to 1 (cascadeKernel_rowsum :116), or a blocked state is not held fixed (cascadeKernel_of_noEnabled :126; fixture_p3_identity_when_blocked :241).",
      runtimeEntry ``DarkTower.WarMachine.CascadeTransition.interpret notLivePath "2026-09-16"
        "WM-03 (P3): a precedence with an uninterpreted pattern is a typed hole"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:269"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:159"
        "mathlib4/DarkTower/WarMachine/CascadeTransition.lean:156"
        "A precedence containing an uninterpreted pattern does not yield :missing-pattern-interpretation (interpret_eq_none_iff :156)."] },
  { schemaVersion := 1, contractId := "wm-policy-rollout",
    moduleName := "DarkTower.WarMachine.PolicyRollout",
    declarations := [
      runtimeEntry ``DarkTower.WarMachine.PolicyRollout.rolloutState lagging "2026-09-16"
        "WM-03/WM-05 (P3): Q(s_tau|pi) rolled forward by the cascade kernel; add-only effects"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:298"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:120"
        "mathlib4/DarkTower/WarMachine/CascadeTransition.lean:286"
        "LAGGING (P10, mathlib4 95127698bd): the Lean guard adds ¬(produces ⊆ s); Clojure guard-holds? (cascade_model_manifest.clj:105) does not yet, so runtime and Lean disagree whenever an achieved pattern is first in precedence. Other falsifiers: The two-step rollout does not reach the full state with probability theta1*theta2 (fixture_rollout_two :286), or reversing the one-step order changes nothing where it should (fixture_one_step_reversed :514).",
      runtimeEntry ``DarkTower.WarMachine.PolicyRollout.predictedOutcome notLivePath "2026-09-16"
        "WM-04 (P5): Q(o|pi) = sum_s A(s,o) q(s) with A = TokenObservation.tokenLikelihood"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:217"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:198"
        "mathlib4/DarkTower/WarMachine/TokenObservation.lean:157"
        "With zero rates the predicted observation distribution differs from the state distribution q (predictedOutcome_eq_rolloutState :157); or a rate refusal does not propagate."] },
  { schemaVersion := 1, contractId := "wm-token-observation",
    moduleName := "DarkTower.WarMachine.TokenObservation",
    declarations := [
      runtimeEntry ``DarkTower.WarMachine.TokenObservation.tokenLikelihood notLivePath "2026-09-16"
        "WM-04 (P5): per-token adjudication likelihood A(o|s)"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:174"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:180"
        "mathlib4/DarkTower/WarMachine/TokenObservation.lean:109"
        "(token-likelihood rates s o) with false-neg 3/2 does not refuse with :invalid-adjudication-rate; or a state token with no rate entry does not refuse; or zero rates do not give the identity kernel (tokenLikelihood_checkable :109)."
      ,
      runtimeEntry ``DarkTower.WarMachine.TokenObservation.observationKernelOK notLivePath "2026-09-16"
        "WM-04 (P5): the observation row over every subset is a distribution (the ForwardModel A obligations)"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:200"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:198"
        "mathlib4/DarkTower/WarMachine/TokenObservation.lean:84"
        "An observation row has a negative entry or does not sum to exactly 1 (tokenLikelihood_nonneg :43, tokenLikelihood_colsum :84)."] },
  { schemaVersion := 1, contractId := "wm-token-preference",
    moduleName := "DarkTower.WarMachine.TokenPreference",
    declarations := [
      runtimeEntry ``DarkTower.WarMachine.TokenPreference.PreferenceSpec notLivePath "2026-09-16"
        "WM-06 (P6): preference specification (want, evidence, lam > 0, mu >= 0, zeroed proper)"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:359"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:329"
        "mathlib4/DarkTower/WarMachine/TokenPreference.lean:59"
        "lam = 0 or an empty want does not refuse with :invalid-preference-spec (the Lean structure requires lam_pos and want_nonempty; Z_pos :59 depends on them).",
      runtimeEntry ``DarkTower.WarMachine.TokenPreference.PreferenceSpec.utility notLivePath "2026-09-16"
        "WM-06 (P6): utility = lam * coverage + mu * evidence count; exact rationals in the runtime"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:388"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:286"
        "mathlib4/DarkTower/WarMachine/TokenPreference.lean:122"
        "Utility is not strictly increasing in want coverage at equal evidence count (preference_lt_of_want_lt :122), or depends on token content beyond membership (preference_congr).",
      runtimeEntry ``DarkTower.WarMachine.TokenPreference.PreferenceSpec.preference notLivePath "2026-09-16"
        "WM-06 (P6): exp(utility)/Z off zeroed, 0 on zeroed. Runtime uses Math/exp on doubles; correspondence is checked to 1e-12, not exactly"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:399"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:306"
        "mathlib4/DarkTower/WarMachine/TokenPreference.lean:76"
        "The distribution does not sum to 1 within 1e-12 (preference_sum :76), is nonzero on a zeroed outcome, or zero off it (preference_eq_zero_iff :105, preference_pos_iff :98).",
      runtimeEntry ``DarkTower.WarMachine.TokenPreference.PreferenceSpec.preference notLivePath "2026-09-16"
        "WM-10 (P11 1b-i): the same distribution in closed form at mission scale (Z without powerset enumeration, over an explicit common :universe); equal to preference-distribution on small universes"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:536"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:427"
        "mathlib4/DarkTower/WarMachine/TokenPreference.lean:76"
        "Any 2-4 token case where preference-fn differs from preference-distribution; a universe that disagrees with the enumerating one (preference-fn-universe-matches-enumerating :528).",
      runtimeEntry ``DarkTower.WarMachine.TokenPreference.PreferenceSpec.preference notLivePath "2026-09-16"
        "WM-10 (P11 1b-i): log-space closed form (log Z, overflow-safe near 1000 tokens; zeroed check safe past 62 tokens)"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:497"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:543"
        "mathlib4/DarkTower/WarMachine/TokenPreference.lean:105"
        "A zeroed outcome gets finite log-preference, or a non-zeroed one gets -inf (preference_eq_zero_iff :105); overflow or wrap at scale."] },
  { schemaVersion := 1, contractId := "wm-policy-horizon",
    moduleName := "DarkTower.WarMachine.PolicyHorizon",
    declarations := [
      runtimeEntry ``DarkTower.WarMachine.PolicyHorizon.stepRisk notLivePath "2026-09-16"
        "WM-10 (P7/P11 1a): per-step risk KL[Q(o_tau|pi) || C_tau] in EReal; the runtime is also tested against OutcomeRiskKL.outcomeRisk's top condition (the Lean equality of the two carriers is not proved)"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:418"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:402"
        "mathlib4/DarkTower/WarMachine/PolicyHorizon.lean:80"
        "A smoothed risk returns a finite value where some outcome has positive predicted mass and zero preference (the :infinite assertion); or risk is negative for a distribution C (stepRisk_nonneg :80).",
      runtimeEntry ``DarkTower.WarMachine.PolicyHorizon.stepAmbiguity notLivePath "2026-09-16"
        "WM-10 (P7): per-step ambiguity E_Q(s_tau) H[A(.|s)] read at the same rollout step as risk"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:430"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:365"
        "mathlib4/DarkTower/WarMachine/PolicyHorizon.lean:75"
        "Ambiguity is negative, or is read at a different step from risk.",
      runtimeEntry ``DarkTower.WarMachine.PolicyHorizon.horizonEFE notLivePath "2026-09-16"
        "WM-10 (P7/P11 1a): G(pi) = sum over tau=1..T of risk + ambiguity with step-indexed C_tau; runtime enumerates token powersets (small universes only)"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:450"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:385"
        "mathlib4/DarkTower/WarMachine/PolicyHorizon.lean:167"
        "A constant-C runtime fails the ranking reversal (fixture_stepIndexed_preference :300); G is finite although some step has infinite risk (horizonEFE_eq_top_iff :167); extending the horizon does not add exactly the new step (horizonEFE_succ :114).",
      runtimeEntry ``DarkTower.WarMachine.PolicyHorizon.horizonEFE notLivePath "2026-09-16"
        "WM-10 (P11 1b-i): exact sparse G at mission scale, with closed-form C_tau and identity A at zero adjudication rates (TokenObservation.tokenLikelihood_checkable). Declared limitation: non-zero judgement rates are refused at scale"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:566"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:440"
        "mathlib4/DarkTower/WarMachine/PolicyHorizon.lean:167"
        "Any 2-4 token case where sparse and enumerating G differ (sparse-g-equals-enumerating-g :440); a universe offset other than T*k*ln 2 (horizon-g-sparse-universe-offset :559); a non-zero judgement rate accepted at scale.",
      runtimeEntry ``DarkTower.WarMachine.PolicyHorizon.horizonEFE liveShadow "2026-09-16"
        "WM-05/WM-10 (P11 step 1): live shadow G. shadow-cascade-g delegates to horizon-g-sparse (whose Lean value replay is sparse-g-equals-enumerating-g and horizon-g-lean-fixture-correspondence); called on the live path in receipt_construction/construct and recorded only as :score-before/:score-after, never selecting or changing enacted output. live-call-site=futon2/src/futon2/aif/receipt_construction.clj:566 (the score closure reading these results feeds organise at :578). Declared reductions: zero adjudication rates; lam = mu = 1; empty evidence and zeroed sets; horizon 3 (AUTH-horizon-semantics proposes T = 2, awaiting Joe); documented-default theta"
        "futon2/src/futon2/aif/shadow_cascade_g.clj:135"
        "futon2/test/futon2/aif/shadow_cascade_g_test.clj:58"
        "mathlib4/DarkTower/WarMachine/PolicyHorizon.lean:167"
        "A construction whose arms are scored over per-arm universes rather than one common universe (G shifts by T*k*ln 2); a shown order that differs between the shadow scorer and the constant scorer (shadow-does-not-change-shown :119); a refusal not surfaced (shadow-g-refusals :89)."] },
  { schemaVersion := 1, contractId := "wm-exact-belief",
    moduleName := "DarkTower.WarMachine.ExactBeliefTrajectory",
    declarations := [
      runtimeEntry ``DarkTower.WarMachine.ExactBeliefTrajectory.exactUpdate notLivePath "2026-09-16"
        "WM-02 (P12, R3): exact categorical update s(x) = A(o|x)(B s_prev)(x)/P(o); unique B.2 free-energy minimiser; typed refusal exactly at P(o) = 0"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:620"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:584"
        "mathlib4/DarkTower/WarMachine/ExactBeliefTrajectory.lean:128"
        "A mean-field-style update refuses the fixture input that exact-update accepts at 9/10 (fixture_exact_accepts :263; exact-belief-falsifiers :637); a P(o) = 0 observation does not give :zero-predictive-probability, or a P(o) > 0 one does (exactUpdate_eq_none_iff :90).",
      runtimeEntry ``DarkTower.WarMachine.ExactBeliefTrajectory.tokenBeliefAt lagging "2026-09-16"
        "WM-02 (P12, R1): stored belief over token states (q0 = observed token set, B = cascade kernel, A = token likelihood); filtering only, refusal carried forward"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:648"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:592"
        "mathlib4/DarkTower/WarMachine/ExactBeliefTrajectory.lean:238"
        "LAGGING (P10, mathlib4 95127698bd): the Lean guard adds ¬(produces ⊆ s); Clojure guard-holds? (cascade_model_manifest.clj:105) does not yet, so runtime and Lean disagree whenever an achieved pattern is first in precedence. Other falsifiers: A stored belief is not a distribution (tokenBeliefAt_dist :238); a refusal is not carried forward; the first stored belief differs from the mean-field update from the observed token set (tokenBeliefAt_one_eq_meanField)."] }
  ]

def main : IO Unit := do
  let contracts ← registries.mapM fun r => do
    let commit ← sourceGitSha r.moduleName
    pure (r.toJson commit)
  IO.println (Json.mkObj [
    ("schema", Json.str "wm-machine-contract-bundle-v1"),
    ("scope", Json.str "per-entry-holder"),
    ("contracts", Json.arr contracts.toArray)]).compress
end DarkTower.WarMachine.MachineContracts
