import DarkTower.WarMachine.MachineObservation
import DarkTower.WarMachine.MachineBeliefState
import DarkTower.WarMachine.MachineBeliefUpdate
import DarkTower.WarMachine.MachinePrecision
import DarkTower.WarMachine.MachineDepth
import DarkTower.WarMachine.MachineTemperature
import DarkTower.WarMachine.MachineAction
import DarkTower.WarMachine.MachinePredictionError
import DarkTower.WarMachine.TokenState

/-!
Leaf registry for the War Machine's Lean→Clojure contracts. Checked name quotations
bind each reference to an elaborated declaration. Each entry's `holder` states its
claim: `model-transcription-only` entries (2026-09-12) assert no runtime
correspondence; `runtime-correspondence-not-live-path` entries assert that the named
Clojure function computes the Lean declaration, checked by the named behavioural
fixture test, and that the function is not yet called on the live War Machine path
(`p4ng/wm-walkthroughs/build-loop/closure/ALIGNMENT.md` item 4).
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
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:58"
        "mathlib4/DarkTower/WarMachine/TokenState.lean:45"
        "The runtime row is not a point mass summing to 1 on the observed token set.",
      runtimeEntry ``DarkTower.WarMachine.TokenState.independentBelief notLivePath "2026-09-16"
        "WM-02 (P2/P4): independent-token q0 over the token powerset"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:124"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:71"
        "mathlib4/DarkTower/WarMachine/TokenState.lean:136"
        "(independent-belief {\"t0\" 3/2 \"t1\" 1/2} #{\"t0\" \"t1\"}) does not refuse with :invalid-token-probability; or all-0/1 probabilities do not reduce to observed-belief (independentBelief_eq_observedBelief, TokenState.lean:153).",
      runtimeEntry ``DarkTower.WarMachine.TokenState.coverage notLivePath "2026-09-16"
        "WM-02 (P2): want-signature coverage |want ∩ s| / |want|"
        "futon2/src/futon2/aif/cascade_model_manifest.clj:145"
        "futon2/test/futon2/aif/cascade_model_manifest_test.clj:71"
        "mathlib4/DarkTower/WarMachine/TokenState.lean:56"
        "(coverage #{} state) does not refuse with :empty-want-signature; or coverage leaves [0,1], is 1 without want ⊆ s, or decreases as s grows (coverage_le_one :60, coverage_eq_one_iff :65, coverage_mono :83)."] }
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
