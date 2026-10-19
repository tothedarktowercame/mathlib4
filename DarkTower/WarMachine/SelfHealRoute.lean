import Mathlib.Data.List.Basic

/-!
# Self-heal route, level 1

`CLOSED-BY-RECORD`: this is the finite control-flow table transcribed from
`futon2/holes/labs/wm-contract/logic-model/phases.md`, "Injury vs ordinary,
level 1", under Joe's 2026-10-19 ruling. It certifies the routing law, not
that an admission or enactment has succeeded in a serving run.
-/

namespace DarkTower.WarMachine.SelfHealRoute

/-- The absence vocabulary carried by a readiness refusal. It is a finite
inductive rather than text so the record table remains kernel-decidable. -/
inductive AbsentTerm where
  | transactionPath | repairPorts | diagnosisPort | diagnosisEvidence | acceptanceProposalPort
  | acceptanceReviewPort | acceptanceRunPort | acceptanceTest
  deriving DecidableEq, Repr

/-- The level-1 states named by the self-heal route model. Refusal terms are
retained on readiness refusals rather than being represented by a success-like
default. -/
inductive RouteState where
  | noActiveInjury
  | activeInjury
  | diagnosisPrepared
  | diagnosisRefused
  | admissionRun
  | admissionRefused
  | reviewAccepted
  | reviewRefused
  | readinessReady
  | readinessRefused (absentTerms : List AbsentTerm)
  | routeEnacted
  | routeRefused
  | enacted
  | ordinarySelection
  | terminalRecord
  deriving DecidableEq, Repr

open RouteState

/-- Finite level-1 transition table. It follows the runtime order: prepare
diagnosis, run/admit the acceptance test, readiness, route, then enact. A
refused review remains visible to readiness; typed refusal dispositions then
end at `terminalRecord`, never at ordinary selection. -/
def transitions : List (RouteState × RouteState) :=
  [ -- `phases.md`, "Injury vs ordinary, level 1": ordinary is only no-active-injury.
    (noActiveInjury, ordinarySelection),
    (ordinarySelection, terminalRecord),
    -- `full_loop_runtime.clj:475-491`: prepare diagnosis, then acceptance/admission.
    (activeInjury, diagnosisPrepared),
    (activeInjury, diagnosisRefused),
    (diagnosisPrepared, admissionRun),
    (admissionRun, reviewAccepted),
    (admissionRun, admissionRefused),
    (admissionRun, reviewRefused),
    -- `full_loop_runtime.clj:492-505`: review result is retained through readiness.
    (reviewAccepted, readinessReady),
    (reviewRefused, readinessReady),
    (reviewRefused, readinessRefused [AbsentTerm.acceptanceTest]),
    -- `full_loop_runtime.clj:502-505`: ready input enters dedicated `route!`.
    (readinessReady, routeEnacted),
    (readinessReady, routeRefused),
    (routeEnacted, enacted),
    -- `phases.md`, ruling: typed refusals terminate and do not fall back.
    (diagnosisRefused, terminalRecord),
    (admissionRefused, terminalRecord),
    (readinessRefused [AbsentTerm.acceptanceTest], terminalRecord),
    (routeRefused, terminalRecord),
    (enacted, terminalRecord) ]

/-- The finite inventory of state *mentions* in `transitions`. `RouteState`
itself is infinite because `readinessRefused` carries a list; the decidable
claim below is only over this transcribed finite edge table. -/
def mentionedStates : List RouteState :=
  [ noActiveInjury, activeInjury, diagnosisPrepared, diagnosisRefused,
    admissionRun, admissionRefused, reviewAccepted, reviewRefused,
    readinessReady, readinessRefused [AbsentTerm.acceptanceTest], routeEnacted,
    routeRefused, enacted, ordinarySelection, terminalRecord ]

/-- Boolean equality for the finite route-state vocabulary. -/
def stateEq (left right : RouteState) : Bool := decide (left = right)

/-- Whether a table edge is present, using direct Boolean recursion so the
certificate reduces without a string equality oracle. -/
def edge (source destination : RouteState) : Bool :=
  transitions.any fun pair => stateEq source pair.1 && stateEq destination pair.2

/-- Bounded table reachability. The bound is the number of transcribed state
mentions, not a claim that the `RouteState` type is finite. -/
def reachesWithin : Nat → RouteState → RouteState → Bool
  | 0, source, destination => stateEq source destination
  | fuel + 1, source, destination =>
      stateEq source destination || transitions.any (fun pair =>
        if stateEq pair.1 source then reachesWithin fuel pair.2 destination else false)

/-- Reachability in the level-1 finite table. -/
def reaches (source destination : RouteState) : Bool :=
  reachesWithin mentionedStates.length source destination

/-- A concrete record path conforms exactly when all adjacent pairs are table
edges. -/
def conforms : List RouteState → Bool
  | [] => true
  | [_] => true
  | source :: destination :: rest => edge source destination && conforms (destination :: rest)

/-- No finite-table path from an active injury can enter ordinary selection.
This is decided over the transcribed transition table. -/
theorem noFallback : reaches activeInjury ordinarySelection = false := by decide

/-- OBSERVED-NOT-RECORDED click 1 witness. Its durable binding
`futon3c/data/wm-click-run-bindings/click-run-binding-wm-click-576d3263-6d44-4299-ae58-609eeabd53c2.edn`
sha256 `89f0c25b061eb4a5ac132d2f7696a9cac3ca10ce35bd3c91d7e2490ff7f180dc`
records only `:binding-status :absent`, `:run-record-absence`, and
`[:run-id-observation :status] :absent`; no durable record carries this path.
The serving API last-result fields `:diagnosis :status :available`,
`[:acceptance :status] :refused`, `[:route] :dedicated-meta-self-heal`, and
`:ordinary-selection-called? false` were transcribed in PACKETS finding F2c,
commit `fba86a35b`. F7 is the pending durable-disposition repair. -/
def click1ObservedPath : List RouteState :=
  [ activeInjury, diagnosisPrepared, admissionRun, reviewRefused, readinessReady,
    routeRefused, terminalRecord ]

/-- The observed click-1 path conforms to the post-ruling table; this theorem
does not promote the serving observation into a durable record witness. -/
theorem click1_observedConforms : conforms click1ObservedPath = true := by decide

/-- Click 2 durable witness. The terminal publication
`data/wm-runs/terminal-publication-2026-10-19-08771834-5add-4b3e-9459-abeaab21477c.edn`
sha256 `fd9b8ca9b5f9a9fa46ba3a37429992d2815a84cbbe9446a341370dae4db0daf0`
has `:run-record` pin `923239...a4a0`; that tick record's
`:meta-self-heal/readiness` has `:status :absent`,
`:absent-terms [:acceptance-test]`, and
`[:acceptance-observation :status] :refused`, establishing the active-injury,
prepared-diagnosis/admission, refused-review, and readiness portion. Its
`:failure {:kind :abstained :stage :selection-world}` establishes the reverted
ordinary-selection terminal observation. There is no additional tick record:
this is the pinned tick record named by the terminal publication. -/
def click2RevertedPath : List RouteState :=
  [ activeInjury, diagnosisPrepared, admissionRun, reviewRefused, readinessReady,
    ordinarySelection, terminalRecord ]

/-- Click 2 is a certified violation of the post-ruling table, not an intended
behaviour: its `readinessReady → ordinarySelection` pair is absent. -/
theorem click2_isViolation : conforms click2RevertedPath = false := by decide

end DarkTower.WarMachine.SelfHealRoute
