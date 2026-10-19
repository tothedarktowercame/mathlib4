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
  | transactionPath | repairPorts | diagnosisPort | acceptanceProposalPort
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
  [ (noActiveInjury, ordinarySelection),
    (ordinarySelection, terminalRecord),
    (activeInjury, diagnosisPrepared),
    (activeInjury, diagnosisRefused),
    (diagnosisPrepared, admissionRun),
    (admissionRun, reviewAccepted),
    (admissionRun, admissionRefused),
    (admissionRun, reviewRefused),
    (reviewAccepted, readinessReady),
    (reviewAccepted, readinessRefused [AbsentTerm.acceptanceTest]),
    (reviewRefused, readinessReady),
    (reviewRefused, readinessRefused [AbsentTerm.acceptanceTest]),
    (readinessReady, routeEnacted),
    (readinessReady, routeRefused),
    (routeEnacted, enacted),
    (diagnosisRefused, terminalRecord),
    (admissionRefused, terminalRecord),
    (readinessRefused [AbsentTerm.acceptanceTest], terminalRecord),
    (routeRefused, terminalRecord),
    (enacted, terminalRecord) ]

/-- The finite state inventory used as a sufficient simple-path bound. -/
def states : List RouteState :=
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

/-- Bounded graph reachability. A path in this finite table can be shortened
to a simple path, so `states.length` bounds every reachable endpoint. -/
def reachesWithin : Nat → RouteState → RouteState → Bool
  | 0, source, destination => stateEq source destination
  | fuel + 1, source, destination =>
      stateEq source destination || transitions.any (fun pair =>
        if stateEq pair.1 source then reachesWithin fuel pair.2 destination else false)

/-- Reachability in the level-1 finite table. -/
def reaches (source destination : RouteState) : Bool :=
  reachesWithin states.length source destination

/-- A concrete record path conforms exactly when all adjacent pairs are table
edges. -/
def conforms : List RouteState → Bool
  | [] => true
  | [_] => true
  | source :: destination :: rest => edge source destination && conforms (destination :: rest)

/-- No finite-table path from an active injury can enter ordinary selection.
This is decided over the transcribed transition table. -/
theorem noFallback : reaches activeInjury ordinarySelection = false := by decide

/-- Click 1 record witness. Source:
`futon3c/data/wm-click-run-bindings/click-run-binding-wm-click-576d3263-6d44-4299-ae58-609eeabd53c2.edn`
sha256 `89f0c25b061eb4a5ac132d2f7696a9cac3ca10ce35bd3c91d7e2490ff7f180dc`.
Its dedicated-route disposition is recorded in futon2 PACKETS F2c. -/
def click1Path : List RouteState :=
  [ activeInjury, diagnosisPrepared, admissionRun, reviewRefused, readinessReady,
    routeRefused, terminalRecord ]

/-- Click 1 conforms to the post-ruling route table. -/
theorem click1_conforms : conforms click1Path = true := by decide

/-- Click 2 record witness. Source:
`futon2/data/wm-runs/terminal-publication-2026-10-19-08771834-5add-4b3e-9459-abeaab21477c.edn`
sha256 `fd9b8ca9b5f9a9fa46ba3a37429992d2815a84cbbe9446a341370dae4db0daf0`.
It ran under the reverted F2c fallback and entered ordinary selection after a
review refusal. -/
def click2RevertedPath : List RouteState :=
  [ activeInjury, diagnosisPrepared, admissionRun, reviewRefused, readinessReady,
    ordinarySelection, terminalRecord ]

/-- Click 2 is a certified violation of the post-ruling table, not an intended
behaviour: its `readinessReady → ordinarySelection` pair is absent. -/
theorem click2_isViolation : conforms click2RevertedPath = false := by decide

end DarkTower.WarMachine.SelfHealRoute
