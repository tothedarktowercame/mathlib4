import Mathlib.Data.List.Basic

/-!
# Self-heal route, level 1

`CLOSED-BY-RECORD`: this is the finite control-flow table transcribed from
`futon2/holes/labs/wm-contract/logic-model/phases.md`, "Injury vs ordinary,
level 1", under Joe's 2026-10-19 ruling.  It certifies the routing law, not
that an admission or enactment has succeeded in a serving run.
-/

namespace DarkTower.WarMachine.SelfHealRoute

/-- The level-1 states named by the self-heal route model.  Refusal terms are
retained on readiness refusals rather than being represented by a success-like
default. -/
inductive RouteState where
  | noActiveInjury
  | activeInjury
  | readinessReady
  | readinessRefused (absentTerms : List String)
  | admissionRun
  | admissionRefused
  | reviewAccepted
  | reviewRefused
  | routeRefused
  | enacted
  | ordinarySelection
  | terminalRecord
  deriving DecidableEq, Repr

open RouteState

/-- Finite level-1 transition table.  `reviewRefused` is first routed to the
typed `routeRefused` terminal disposition; the other refusal constructors have
only their terminal-record edge.  This is the record-compatible rendering of
the ruling's "no ordinary fallback" law. -/
def transitions : List (RouteState × RouteState) :=
  [ (noActiveInjury, ordinarySelection),
    (ordinarySelection, terminalRecord),
    (activeInjury, readinessReady),
    (activeInjury, readinessRefused ["missing-readiness-term"]),
    (readinessReady, admissionRun),
    (readinessReady, reviewRefused),
    (admissionRun, reviewAccepted),
    (admissionRun, admissionRefused),
    (reviewAccepted, enacted),
    (reviewRefused, routeRefused),
    (readinessRefused ["missing-readiness-term"], terminalRecord),
    (admissionRefused, terminalRecord),
    (routeRefused, terminalRecord),
    (enacted, terminalRecord) ]

/-- The finite state inventory used as a sufficient simple-path bound. -/
def states : List RouteState :=
  [ noActiveInjury, activeInjury, readinessReady,
    readinessRefused ["missing-readiness-term"], admissionRun, admissionRefused,
    reviewAccepted, reviewRefused, routeRefused, enacted, ordinarySelection,
    terminalRecord ]

/-- Whether a table edge is present. -/
def edge (from to : RouteState) : Bool := decide ((from, to) ∈ transitions)

/-- Bounded graph reachability.  A path in this finite table can be shortened
to a simple path, so `states.length` bounds every reachable endpoint. -/
def reachesWithin : Nat → RouteState → RouteState → Bool
  | 0, from, to => from == to
  | fuel + 1, from, to =>
      from == to || transitions.any (fun e =>
        if e.1 == from then reachesWithin fuel e.2 to else false)

/-- Reachability in the level-1 finite table. -/
def reaches (from to : RouteState) : Bool := reachesWithin states.length from to

/-- A concrete record path conforms exactly when all adjacent pairs are table
edges. -/
def conforms : List RouteState → Bool
  | [] => true
  | [_] => true
  | from :: to :: rest => edge from to && conforms (to :: rest)

/-- No finite-table path from an active injury can enter ordinary selection.
This is decided over the transcribed transition table. -/
theorem noFallback : reaches activeInjury ordinarySelection = false := by decide

/-- Click 1 record witness.  Source:
`futon3c/data/wm-click-run-bindings/click-run-binding-wm-click-576d3263-6d44-4299-ae58-609eeabd53c2.edn`
sha256 `89f0c25b061eb4a5ac132d2f7696a9cac3ca10ce35bd3c91d7e2490ff7f180dc`.
Its dedicated-route disposition is recorded in futon2 PACKETS F2c. -/
def click1Path : List RouteState :=
  [ activeInjury, readinessReady, reviewRefused, routeRefused, terminalRecord ]

/-- Click 1 conforms to the post-ruling route table. -/
theorem click1_conforms : conforms click1Path = true := by decide

/-- Click 2 record witness.  Source:
`futon2/data/wm-runs/terminal-publication-2026-10-19-08771834-5add-4b3e-9459-abeaab21477c.edn`
sha256 `fd9b8ca9b5f9a9fa46ba3a37429992d2815a84cbbe9446a341370dae4db0daf0`.
It ran under the reverted F2c fallback and entered ordinary selection after a
review refusal. -/
def click2RevertedPath : List RouteState :=
  [ activeInjury, readinessReady, reviewRefused, ordinarySelection, terminalRecord ]

/-- Click 2 is a certified violation of the post-ruling table, not an intended
behaviour: its `reviewRefused → ordinarySelection` pair is absent. -/
theorem click2_isViolation : conforms click2RevertedPath = false := by decide

end DarkTower.WarMachine.SelfHealRoute
