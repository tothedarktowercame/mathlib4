import Mathlib.Data.List.Basic

/-!
# Self-heal route, level 1

`CLOSED-BY-RECORD`: this is the finite control-flow table transcribed from
`futon2/holes/labs/wm-contract/logic-model/phases.md`, "Injury vs ordinary,
level 1", under Joe's 2026-10-19 ruling, and from the runtime order in
`futon2/src/futon2/aif/full_loop_runtime.clj:475-505` (futon2 `e4e53617a`).
It certifies the routing law, not that an admission or enactment has
succeeded in a serving run.

Revision 2 (claude-5, 2026-10-19), after claude-2's L1 reading
(job `invoke-1792436329058-17707-36486211`): refusals of the diagnosis and
acceptance stages do not terminate directly; the runtime runs readiness and
then `route!` after every acceptance observation, and it is `route!` that
refuses with `[:acceptance-test]` (click 4). Readiness never emits
`:acceptance-test`; its refusal terms are port terms. The absence vocabulary
is therefore split by stage and kept out of the state, so that `RouteState`
is finite and a record's terms are reported beside its path (unit L2) rather
than encoded in it.

**Scope.** The table covers a click without `:meta-repair-retry`. The
attributable retry (`full_loop_runtime.clj:492-499`,
`attributable-retry-readiness`) runs ordinary work under an active injury by
design of the runtime and is not transcribed here; `noFallback` says nothing
about it. Whether that retry is within Joe's ruling is open (hole, not
decided here).

Revision 3 (claude-2, 2026-10-19, Joe's go): `route!` has two refusals
after readiness besides missing configuration. A refused
`coordinator/prepare` is `preparationRefused` (futon2 `df2209a33`); a
transaction whose pins disagree with the diagnosis or acceptance observation
is `bindingRefused`. Before `df2209a33` the first was recorded as the second
(click `wm-click-c78d0f27`); the decided account is
`futon2/holes/labs/wm-contract/logic-model/jit/SelfHealPrepare.lean`.

**AIF leg.** None. No module under `DarkTower/AIF` or `DarkTower/WarMachine`
models injury, repair or route arbitration (claude-2, 2026-10-19). Typed none
until one is named.
-/

namespace DarkTower.WarMachine.SelfHealRoute

/-- Absence terms a readiness refusal can carry
(`meta_self_heal_production.clj`, `production-readiness`, futon2 `e4e53617a`). -/
inductive ReadinessTerm where
  | transactionPath | repairPorts | acceptanceRunPort | diagnosisPort
  | acceptanceProposalPort | acceptanceReviewPort
  deriving DecidableEq, Repr

/-- Absence terms a `route!` refusal can carry (`route!`, same file). Only
`route!` emits `diagnosisEvidence` and `acceptanceTest`. -/
inductive RouteTerm where
  | transactionPath | repairPorts | acceptanceRunPort | diagnosisEvidence | acceptanceTest
  deriving DecidableEq, Repr

/-- The level-1 states. Each refusal is its own typed state; the terms it
carried are record detail for the certificate producer, not part of the
state. -/
inductive RouteState where
  | noActiveInjury
  | activeInjury
  -- diagnosis stage (`prepare-diagnosis`)
  | diagnosisPrepared
  | diagnosisRefused
  -- acceptance stage (`prepare-acceptance`)
  | acceptanceUnavailable   -- diagnosis not `:available`: `:acceptance-diagnosis-unavailable`
  | proposalRefused         -- `produce-acceptance!` did not return `:proposed`
  | admissionRun            -- `admit-acceptance!` entered
  | admissionRefused        -- admission refused before or without a reviewer answer
  | reviewAccepted
  | reviewRefused
  -- readiness (`production-readiness`)
  | readinessReady
  | readinessRefused        -- `:production-config-required` with port terms
  | ledgerUnreadable        -- `:ledger-unreadable`
  -- route (`route!`)
  | routeEnacted
  | routeRefused            -- `:production-config-required` with route terms
  | preparationRefused      -- `:preparation-refused`: `coordinator/prepare` returned no transaction
  | bindingRefused          -- `:diagnosis-transaction-mismatch` / `:acceptance-transaction-mismatch`
  | enacted
  | ordinarySelection
  | terminalRecord
  deriving DecidableEq, Repr

open RouteState

/-- The acceptance observations after which the runtime runs readiness. -/
def acceptanceOutcomes : List RouteState :=
  [ acceptanceUnavailable, proposalRefused, admissionRefused, reviewAccepted, reviewRefused ]

/-- Finite level-1 transition table in the runtime order: prepare diagnosis,
prepare acceptance (propose, run, review), readiness, route, enact. Every
acceptance observation, refused or not, is followed by readiness; typed
refusal dispositions end at `terminalRecord`, never at ordinary selection. -/
def transitions : List (RouteState × RouteState) :=
  [ -- `phases.md`, "Injury vs ordinary, level 1": ordinary is only no-active-injury.
    (noActiveInjury, ordinarySelection),
    (ordinarySelection, terminalRecord),
    -- `full_loop_runtime.clj:475-477`: prepare diagnosis.
    (activeInjury, diagnosisPrepared),
    (activeInjury, diagnosisRefused),
    -- `prepare-acceptance` (`meta_self_heal_production.clj:662-683`).
    (diagnosisRefused, acceptanceUnavailable),
    (diagnosisPrepared, proposalRefused),
    (diagnosisPrepared, admissionRun),
    (admissionRun, admissionRefused),
    (admissionRun, reviewAccepted),
    (admissionRun, reviewRefused),
    -- `full_loop_runtime.clj:492-496`: readiness after every acceptance observation.
    (acceptanceUnavailable, readinessReady), (acceptanceUnavailable, readinessRefused),
    (acceptanceUnavailable, ledgerUnreadable),
    (proposalRefused, readinessReady), (proposalRefused, readinessRefused),
    (proposalRefused, ledgerUnreadable),
    (admissionRefused, readinessReady), (admissionRefused, readinessRefused),
    (admissionRefused, ledgerUnreadable),
    (reviewAccepted, readinessReady), (reviewAccepted, readinessRefused),
    (reviewAccepted, ledgerUnreadable),
    (reviewRefused, readinessReady), (reviewRefused, readinessRefused),
    (reviewRefused, ledgerUnreadable),
    -- `full_loop_runtime.clj:502-505`: ready input enters dedicated `route!`.
    (readinessReady, routeEnacted),
    (readinessReady, routeRefused),
    -- `route!` after futon2 `df2209a33`: a refused prepare is its own refusal;
    -- the binding checks run only against a transaction (rev 3).
    (readinessReady, preparationRefused),
    (readinessReady, bindingRefused),
    (routeEnacted, enacted),
    -- `phases.md`, ruling: typed refusals terminate and do not fall back.
    (readinessRefused, terminalRecord),
    (ledgerUnreadable, terminalRecord),
    (routeRefused, terminalRecord),
    (preparationRefused, terminalRecord),
    (bindingRefused, terminalRecord),
    (enacted, terminalRecord) ]

/-- Every state of the (now finite) vocabulary; the fuel bound for `reaches`. -/
def allStates : List RouteState :=
  [ noActiveInjury, activeInjury, diagnosisPrepared, diagnosisRefused,
    acceptanceUnavailable, proposalRefused, admissionRun, admissionRefused,
    reviewAccepted, reviewRefused, readinessReady, readinessRefused, ledgerUnreadable,
    routeEnacted, routeRefused, preparationRefused, bindingRefused, enacted,
    ordinarySelection, terminalRecord ]

/-- Boolean equality for the route-state vocabulary. -/
def stateEq (left right : RouteState) : Bool := decide (left = right)

/-- Whether a table edge is present. -/
def edge (source destination : RouteState) : Bool :=
  transitions.any fun pair => stateEq source pair.1 && stateEq destination pair.2

/-- Bounded table reachability; the bound is the size of the vocabulary. -/
def reachesWithin : Nat → RouteState → RouteState → Bool
  | 0, source, destination => stateEq source destination
  | fuel + 1, source, destination =>
      stateEq source destination || transitions.any (fun pair =>
        if stateEq pair.1 source then reachesWithin fuel pair.2 destination else false)

/-- Reachability in the level-1 finite table. -/
def reaches (source destination : RouteState) : Bool :=
  reachesWithin allStates.length source destination

/-- Adjacent pairs are table edges. On its own this accepts `[]`, singletons
and truncated paths; a producer must use `conformsPath` or `conformsSuffix`. -/
def conforms : List RouteState → Bool
  | [] => true
  | [_] => true
  | source :: destination :: rest => edge source destination && conforms (destination :: rest)

/-- A path ends at `terminalRecord`. -/
def endsTerminal (path : List RouteState) : Bool :=
  match path.getLast? with
  | some terminalRecord => true
  | _ => false

/-- A complete click path: starts at an injury state, ends at
`terminalRecord`, and every step is a table edge. -/
def conformsPath (path : List RouteState) : Bool :=
  match path with
  | noActiveInjury :: _ => conforms path && endsTerminal path
  | activeInjury :: _ => conforms path && endsTerminal path
  | _ => false

/-- A recorded suffix whose prefix the record does not establish: non-empty,
ends at `terminalRecord`, every step a table edge. The producer reports the
unrecorded prefix as a typed gap beside this verdict (unit L2). -/
def conformsSuffix (path : List RouteState) : Bool :=
  !path.isEmpty && conforms path && endsTerminal path

/-- No table path from an active injury enters ordinary selection. Decided
over the transcribed table; the attributable retry is outside its scope (see
the module docstring). -/
theorem noFallback : reaches activeInjury ordinarySelection = false := by decide

/-- Every acceptance observation reaches readiness: no acceptance-stage
refusal terminates directly. -/
theorem acceptanceOutcomes_reachReadiness :
    acceptanceOutcomes.all (fun s => edge s readinessReady) = true := by decide

/-- The bad cases `conforms` alone would accept. -/
theorem emptyPath_notComplete : conformsPath [] = false := by decide
theorem truncatedPath_notComplete :
    conformsPath [activeInjury, diagnosisPrepared] = false := by decide
theorem truncatedPath_conformsOnly :
    conforms [activeInjury, diagnosisPrepared] = true := by decide

/-- OBSERVED-NOT-RECORDED click 1 witness. Its durable binding
`futon3c/data/wm-click-run-bindings/click-run-binding-wm-click-576d3263-6d44-4299-ae58-609eeabd53c2.edn`
sha256 `89f0c25b061eb4a5ac132d2f7696a9cac3ca10ce35bd3c91d7e2490ff7f180dc`
records only `:binding-status :absent`, `:run-record-absence`, and
`[:run-id-observation :status] :absent`; no durable record carries this path.
The serving API last-result fields `:diagnosis :status :available`,
`[:acceptance :status] :refused`, `[:route] :dedicated-meta-self-heal`, and
`:ordinary-selection-called? false` were transcribed in PACKETS finding F2c,
commit `fba86a35b`. Those fields do not say which acceptance-stage refusal
occurred; `reviewRefused` is carried over from the first transcription of
this file (`01df7da6d9`) and is not established. F7 (futon3c `baa9d55fa`)
now retains a refused click's disposition in its binding, so clicks from
click 3 on can be record witnesses; click 1 itself remains unrecorded. -/
def click1ObservedPath : List RouteState :=
  [ activeInjury, diagnosisPrepared, admissionRun, reviewRefused, readinessReady,
    routeRefused, terminalRecord ]

/-- The observed click-1 path is a complete table path; this theorem does not
promote the serving observation into a durable record witness. -/
theorem click1_observedConforms : conformsPath click1ObservedPath = true := by decide

/-- Click 2 durable witness. The terminal publication
`data/wm-runs/terminal-publication-2026-10-19-08771834-5add-4b3e-9459-abeaab21477c.edn`
sha256 `fd9b8ca9b5f9a9fa46ba3a37429992d2815a84cbbe9446a341370dae4db0daf0`
pins `:run-record`
`data/wm-runs/tick-run-record-2026-10-19-08771834-5add-4b3e-9459-abeaab21477c.edn`
sha256 `923239a8acbd52097cea7968de10959e32a5ff373a5ca53e837dbf771816a4a0`.
That tick record's `:acceptance-observation {:status :refused
:reason :meta-self-heal/acceptance-review-refused :review-status :refused}`
establishes `reviewRefused` (revision 2a: the kind is recorded; the earlier
"carried over" remark was wrong). Its `:meta-self-heal/readiness`
`{:status :absent :absent-terms [:acceptance-test]}` is the F2a preflight
observation retained by the runner (`full_loop_runner.clj:1320`), not a
`production-readiness` result; it is mapped to `readinessReady` because the
click went on to spend a ration in selection, which a refused readiness
(returned before ration spend) would have prevented. Its
`:failure {:kind :abstained :stage :selection-world}` establishes the
reverted ordinary-selection terminal observation. -/
def click2RevertedPath : List RouteState :=
  [ activeInjury, diagnosisPrepared, admissionRun, reviewRefused, readinessReady,
    ordinarySelection, terminalRecord ]

/-- Click 2 is a certified violation of the post-ruling table: its
`readinessReady → ordinarySelection` pair is absent. -/
theorem click2_isViolation : conforms click2RevertedPath = false := by decide

/-- The click-2 verdict does not depend on which acceptance-stage refusal
occurred: the violated edge is the readiness-to-ordinary step itself. -/
theorem click2_violationIsTheOrdinaryStep :
    edge readinessReady ordinarySelection = false := by decide

/-- Click 4 record witness. Durable binding
`futon3c/data/wm-click-run-bindings/click-run-binding-wm-click-fca1c921-75a7-4ebf-8713-0c464ffbfb0f.edn`
sha256 `0e3f984b4a43530ecc70c8b842f0fa7eb62bec915c0f393ae6aef875964f99e6`
carries `:runtime-disposition {:status :refused
:reason :meta-self-heal/production-config-required :route :dedicated-meta-self-heal
:ordinary-selection-called? false :absent-terms [:acceptance-test]}`. Only
`route!` emits `:acceptance-test`, so the binding establishes the suffix
`[readinessReady, routeRefused, terminalRecord]`. The prefix is from the
serving result transcribed in PACKETS ("Click 4 verified", 18:35Z, and
codex-7's entry `c0b07a784`): diagnosis `:available` (pin
`diagnosis-83b348…`) and acceptance `{:status :refused
:reason :meta-self-heal/acceptance-unavailable}` from a producer failure
before any admission, i.e. `proposalRefused`. -/
def click4RecordedSuffix : List RouteState :=
  [ readinessReady, routeRefused, terminalRecord ]

def click4ObservedPath : List RouteState :=
  [ activeInjury, diagnosisPrepared, proposalRefused, readinessReady, routeRefused,
    terminalRecord ]

theorem click4_suffixConforms : conformsSuffix click4RecordedSuffix = true := by decide
theorem click4_observedConforms : conformsPath click4ObservedPath = true := by decide

/-- Under the first transcription (`01df7da6d9`) click 4's runtime order,
acceptance refused then `route!` refused, was not a table path: that table
sent an acceptance refusal straight to `terminalRecord`. -/
theorem click4_runtimeOrderIsTabled :
    edge proposalRefused readinessReady && edge readinessReady routeRefused = true := by decide

/-- Click `wm-click-c78d0f27` (closed 2026-10-19 19:43:49Z). Its durable binding
`futon3c/data/wm-click-run-bindings/click-run-binding-wm-click-c78d0f27-deca-4390-9b30-f36418714a54.edn`
carries `:runtime-disposition {:status :refused
:reason :meta-self-heal/diagnosis-transaction-mismatch :route :dedicated-meta-self-heal
:ordinary-selection-called? false}`. The recorded reason is masked: no
transaction existed, because production supplied 5 of the 10 work-order
fields (`SelfHealPrepare.production_prepare_refuses_c78d0f27`), and the binding
check compared the diagnosis with an absent work order
(`SelfHealPrepare.click_c78d0f27_masked`). The record establishes only the
suffix after readiness; the step is `preparationRefused`, by that account,
not `bindingRefused` as the reason word suggests. -/
def clickC78d0f27Suffix : List RouteState :=
  [ readinessReady, preparationRefused, terminalRecord ]

theorem clickC78d0f27_suffixConforms : conformsSuffix clickC78d0f27Suffix = true := by decide

/-- A refused prepare ends the click; it never reaches enactment or ordinary
work. -/
theorem preparationRefused_terminates :
    reaches preparationRefused enacted = false ∧
      reaches preparationRefused ordinarySelection = false := by decide

end DarkTower.WarMachine.SelfHealRoute
