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

Revision 4 (claude-2, 2026-10-20, packet M2a from claude-5): a defect
vocabulary for the author/reviewer boundary, the class-1 rows of
`futon2/holes/labs/wm-contract/logic-model/refusal-totality-2026-10-19.md`
(futon2 `315425cbd`). Five clicks on 2026-10-19 all stopped at
`routeRefused [:acceptance-test]`, and the route alone cannot tell them apart. Their
causes sit in the acceptance observation, so they are given as `ProposalDefect` and
`AdmissionDefect` *beside* the path. `RouteState` is unchanged (20 states; rev 4 said 22, corrected in rev 5): this is
the rev 2 principle, terms beside the state rather than in it. `BoundaryDefect.state`
places each defect by the state docstrings. A transport failure at review has no
reviewer answer, so it is `admissionRefused`, not `reviewRefused`.
`wm_route_check.py` at futon2 `8c48e2a16` sends it to `reviewRefused`
(`checkerPlacement_isViolation`). Line citations P = futon2 `9b97bb99c`
`src/futon2/aif/meta_self_heal_production.clj` (unchanged since `e5c5208c9`),
A = futon3c `840251d7c` `src/futon3c/wm/meta_self_heal_adapters.clj`.

**Hole (not decided).** Should a bounded run whose test does not compile refuse at
admission, before a reviewer invoke, as F16 does for passes-before-repair? Today the
runner records it as `:failed` exit 1 (A:373, click `1a6de51f`), so nothing before
review can tell it from a test that fails for the injury.

Revision 5 (claude-2, 2026-10-20, packet M4L from claude-5): the coordination stage
after `routeEnacted`, refusal class 3 of `refusal-totality-2026-10-19.md`. Three new
states, `coordinationHeld`, `coordinationRefused` and `persistRefused`, each ending at
`terminalRecord`, so `RouteState` has 23 states. Why a click stopped inside the
transaction is given beside the path, as `CoordinationOutcome`, in the same way as
`BoundaryDefect`. The table is written against the record shape of packet M4a
(codex-3, `~/notes/packet-codex-route-coordinator-result-2026-10-20.md`), not against
today's code. Today the checkpoint loop in `route!` persists every result and carries a
held or refused result on through the remaining phases (order error 4), and it reports a
coordinator refusal that has no ledger as `:checkpoint-persist-failed` (row #66,
`coordination_66_masked`). After M4a, a held or refused result ends the route, as these
edges say. Line citations C = futon2 `1b923e904`
`src/futon2/aif/meta_repair_coordinator.clj`; P = the same commit,
`meta_self_heal_production.clj`.

**Run-time witness leg (rev 5).** None. No click has reached coordination: every click
on 2026-10-19 stopped at the author/reviewer boundary or earlier. The first click that
reaches coordination after M4a is live is the witness for a later revision.

**Holes (rev 5, not decided).**
* #54: an admission receipt can fail to persist after an accepted review (P:650), and
  there is no edge from `reviewAccepted` to a refusal.
* The attributable retry path (class 5) is still not transcribed.
* #5: `route!` returns nil when the active set is not computed, so the click runs ordinary
  work, and there is no edge for it.

Revision 6 (claude-2, 2026-10-20, packet M6L from claude-5): the route now begins at
the ledger read. `ledgerRead` is the start state. Every row decided at that read has its
own state there: #3 and #6 go to `noActiveInjury`, #4 to `ledgerUnreadable`, #5 to
`activeSetUnavailable`. The uncomputable active set is a terminal refusal with no edge to
ordinary work, per Joe's ruling of 2026-10-19: a refusal inside the self-heal route is a
symptom to investigate, never a reason to route the click around it. Order error 1 is
corrected: `ledgerUnreadable` is reachable from the start without `activeInjury`
(`ledgerUnreadable_withoutInjury`). `RouteState` has 25 states. P = futon2 `c0b9a794b`
`src/futon2/aif/meta_self_heal_production.clj`, S = the same commit, `full_loop_runtime.clj`.

The table elides the acceptance observation that the runtime makes after a decision taken
at the read. `run-opportunity!` always calls `prepare-acceptance`, and a diagnosis that is
not `:available` gives `:acceptance-diagnosis-unavailable` (P:685). So a runtime conforms
to `(ledgerRead, ledgerUnreadable)` and `(activeSetUnavailable, terminalRecord)` only if
it ends the click before that observation, or if the observation is dropped from the
record. `fallthrough_5_today` keeps the observation, because it describes today's code.

**Run-time witness leg (rev 6).** None. No click has reached #5: the five 2026-10-19
clicks all had a computed active set.

**Holes (rev 6, not decided).**
* Order error 2: readiness runs twice (the click preflight with `:readiness-route
  :ordinary`, then `run-opportunity!`), and rev 6 models only the second run.
* Which conformance M6a chooses, given the elision above: end the click before the
  acceptance observation, or extend the table with
  `(activeSetUnavailable, acceptanceUnavailable)` and a `route!`-level refusal.
* `activeSetUnavailable` cannot be reached from a ledger file (claude-5's finding, M7L).
  futon2 `05e71feb9`: `meta_injury_store.clj` L36-49 `load-ledger` refuses
  `:store/tampered-ledger` unless `validate-ledger` is `:valid`, and
  `meta_injury_ledger.clj` L284-288 `active-injuries` runs the same `validate-ledger`
  on the same in-memory value (`diagnosis-context`, P:761-764). `validate-ledger`
  (L231) reads no clock and does no IO, so the second check cannot disagree with the
  first. A throw inside `transitions` would escape as an exception rather than give
  `:unavailable`. The state is reachable only by construction, like
  `:acceptance-review-malformed` (refusal-totality #52).

Revision 7 (claude-2, 2026-10-20, packet M9L from claude-5): the retry click, refusal
class 5. It is a separate start, `retryClick`, which is not reachable from `ledgerRead`.
It has one decision, the attribution (`retryReady` or `retryRefused`), and one edge into
ordinary work, `retryReady → ordinarySelection`. Ordinary work therefore has exactly
two doors (`ordinaryWork_twoDoors`). `RouteState` has 28 states. Citations: R = futon2
`b2c2d9941` `full_loop_runtime.clj`, P = `meta_self_heal_production.clj`,
T = `meta_terminal_injury.clj`, I = `meta_injury_store.clj`; A and S = futon3c `80516025d`
`wm/meta_self_heal_adapters.clj` and `wm/runner_service.clj`.

**How the retry closes the injury** (packet question, settled by reading). The retry
port never answers anything except `:queued` (A:480-495). The injury is closed by the
child click's own terminal record: the ordinary runner's `:meta-terminal-injury-ingest`
sink (futon2 `full_loop_runner.clj` L8256-8266) calls `ingest-record-file!` (I:136),
which calls `transact-classification!` (I:111), which calls `terminal/integrate`. When
the classification's click id equals the `:enacted` entry's `:retry-click`, `integrate`
does one of two things:
* a `:non-injury` record appends `:discharged` with `:outcome :success` (T:195-211);
* an `:injury` record calls `append-retry-result`, giving `:reopened` or `:abandoned`
  (T:241-256).
The close happens after `ordinarySelection → terminalRecord`, so it is beside the path,
not in it: rev 5's `ClosingStatus` names its outcomes, and no state is added for it.

**Holes (rev 7, not decided).**
* An abstained retry discharges the injury as a success. `classify` (T:111-150) makes
  every abstention `:non-injury` unless its cause is
  `:outer-policy-evidence-provider-required` (T:63-65, T:77-82). The same holds for
  `:operator-cancelled`, `:declared-no-work`, `:diagnostic-only`, and a record with no
  failure kind and no outcome (`:absent-terminal-failure`). A retry that does no work
  can therefore discharge the repair it was meant to test. This is a finding about the
  code, not a modelling choice.
* A retry click that writes no run record leaves the injury `:enacted`, which is still
  an active state. The next click routes it again: `route!` resumes `transaction.edn`
  (P:705-710), and `coordinate` replays the recorded `:queued` retry receipt (C:178,
  `invoke-once`) and ends `:awaiting-retry`. The retry port is not called again, so no
  child is queued. By reading, every later click then ends `:awaiting-retry` with no
  retry. Not run.
* Duplicate launch: the idempotency key `meta-retry/<retry-click>` (S:991) is the only
  thing that stops a second child click for the same retry. The table models one child
  and does not need the key; a record with two would show it.
* `#22` (`:acceptance-retry-not-prepared`) is the typed acceptance observation of every
  retry click, not a state.

**Run-time witness leg (rev 7).** None: there is no `wm-retry-*` click-state under
`futon3c/data/wm-click-acceptances/`.

**AIF leg.** None. No module under `DarkTower/AIF` or `DarkTower/WarMachine`
models injury, repair or route arbitration (claude-2, 2026-10-19). Typed none
until one is named.
-/

namespace DarkTower.WarMachine.SelfHealRoute

-- Rev 7: with 28 states the bounded `reaches` unfolds deeper than the default limit
-- allows `decide` to evaluate.
set_option maxRecDepth 8192

/-- Absence terms a readiness refusal can carry
(`meta_self_heal_production.clj`, `production-readiness`, futon2 `e4e53617a`).

Rev 4 note (claude-5 confirmed, futon3c `840251d7c` `runner_service.clj:368`):
`meta-self-heal-preflight!` returns its `configured` map, so a production click's
options carry `:meta-self-heal/readiness-route :ordinary` into the worker. The
runtime readiness therefore waives `diagnosisPort`, `acceptanceRunPort`,
`acceptanceProposalPort` and `acceptanceReviewPort`, and in production a
`readinessRefused` carries only `transactionPath` or `repairPorts`. `route!` still
checks the run port, as `RouteTerm.acceptanceRunPort`. -/
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
  /-- Rev 6: the one ledger read, `diagnosis-context` (P:755). `prepare-diagnosis` (P:769)
  and `production-readiness` (P:797) decide from it, before any injury is known.
  Order error 3: `route!` reads the ledger a second time (P:923-925), and that read has no
  state here. A runtime that reads twice conforms only while the two reads agree. M6a is
  to make `route!` use the context's read. -/
  | ledgerRead
  | noActiveInjury
  | activeInjury
  /-- Rev 6, row #5: the ledger loaded, but `ledger/active-injuries` did not return
  `:computed` (P:786, `:diagnosis-active-set-unavailable`). A terminal refusal. -/
  | activeSetUnavailable
  /-- Rev 7: the start of a retry click. Its options carry `:meta-repair-retry`
  (S:989-995): the child of a parent that ended `:awaiting-retry`, launched only after
  the parent click is durably complete. It makes no ledger read of its own and no
  diagnosis (R:473-477). It carries the acceptance observation
  `:acceptance-retry-not-prepared` (#22), which is typed, not a state. -/
  | retryClick
  /-- Rev 7: `attributable-retry-readiness` (P:896-915) returns `:ready` with the
  attribution. The retry then runs ordinary work (R:500-502), and `route!` is not
  called. -/
  | retryReady
  /-- Rev 7, #57: `:meta-self-heal/retry-attribution-refused` (P:914), with `:expected`
  and `:supplied`. -/
  | retryRefused
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
  | coordinationHeld        -- rev 5: a port answered and the transaction waits (`:held`)
  | coordinationRefused     -- rev 5: `coordinator/coordinate` refused, with or without a ledger
  | persistRefused          -- rev 5: a `:checkpoint` result's ledger or transaction write failed
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
  [ -- rev 6: the ledger read decides #3/#6 (P:780, P:789), #4 (P:783; P:831 at
    -- readiness is the same fact), #5 (P:786), or an active injury.
    (ledgerRead, noActiveInjury),
    (ledgerRead, activeInjury),
    (ledgerRead, ledgerUnreadable),
    (ledgerRead, activeSetUnavailable),
    (activeSetUnavailable, terminalRecord),
    -- rev 7: the retry click, a separate start (S:983-996, R:473-505, P:896-915).
    (retryClick, retryReady),
    (retryClick, retryRefused),
    (retryRefused, terminalRecord),
    (retryReady, ordinarySelection),
    -- `phases.md`, "Injury vs ordinary, level 1": ordinary is only no-active-injury.
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
    -- rev 5: the coordination stage (after M4a, futon2 `route!` ends on any
    -- non-checkpoint result).
    (routeEnacted, coordinationHeld),
    (routeEnacted, coordinationRefused),
    (routeEnacted, persistRefused),
    -- `phases.md`, ruling: typed refusals terminate and do not fall back.
    (readinessRefused, terminalRecord),
    (ledgerUnreadable, terminalRecord),
    (routeRefused, terminalRecord),
    (preparationRefused, terminalRecord),
    (bindingRefused, terminalRecord),
    (coordinationHeld, terminalRecord),
    (coordinationRefused, terminalRecord),
    (persistRefused, terminalRecord),
    (enacted, terminalRecord) ]

/-- Every state of the (now finite) vocabulary; the fuel bound for `reaches`. -/
def allStates : List RouteState :=
  [ ledgerRead, activeSetUnavailable, retryClick, retryReady, retryRefused, noActiveInjury, activeInjury, diagnosisPrepared, diagnosisRefused,
    acceptanceUnavailable, proposalRefused, admissionRun, admissionRefused,
    reviewAccepted, reviewRefused, readinessReady, readinessRefused, ledgerUnreadable,
    routeEnacted, routeRefused, preparationRefused, bindingRefused, enacted,
    coordinationHeld, coordinationRefused, persistRefused,
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
  | ledgerRead :: _ => conforms path && endsTerminal path
  | retryClick :: _ => conforms path && endsTerminal path
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

/-! ## Rev 4: the author/reviewer boundary's defects -/

/-- Why `produce-acceptance!` did not return `:proposed`. Every constructor is placed
at `proposalRefused`. -/
inductive ProposalDefect where
  /-- Transport or seat failure on the author's proposal invoke:
  `:producer-invoke-failed` (A:233) or `:producer-seat-unavailable` (A:227),
  carried as `:acceptance-reason` of `:acceptance-unavailable` (P:460).
  Unwitnessed at proposal on disk. -/
  | transport
  /-- The author answered, but not with one EDN map: `:producer-response-malformed`
  (A:237) as `:acceptance-reason` of `:acceptance-unavailable` (P:460).
  Witness: click `8df4e8d2`. -/
  | unreadableAnswer
  /-- The author's own typed refusal: `:acceptance-status :refused` under
  `:acceptance-unavailable` (P:460). Witness: click `fca1c921`. -/
  | authorRefused
  /-- `:acceptance-prose-or-malformed` (P:470): the answer is not a concrete test.
  Unwitnessed. -/
  | prose
  /-- `:acceptance-proposal-source-mismatch` (P:467): the test source's namespace or
  path disagree. Unwitnessed. -/
  | sourceMismatch
  /-- `:acceptance-request-function-unresolvable` (P:526): a function the diagnosis
  names does not resolve in the serving JVM. Unwitnessed. -/
  | unresolvableFunction
  deriving DecidableEq, Repr

/-- Why `admit-acceptance!` did not return `:accepted`. -/
inductive AdmissionDefect where
  /-- `:acceptance-run-refused` (P:618): the bounded run did not return a valid `:ran`
  result (it covers A:359, A:390-398 and the un-namespaced A:393). Unwitnessed. -/
  | runRefused
  /-- `:acceptance-test-passes-before-repair` (P:622, F16): refused before any reviewer
  invoke. Unwitnessed on a click (off-click replay 5 only). -/
  | passesBeforeRepair
  /-- `:acceptance-review-refused` (P:628) with `:review-status :failed`: the review
  invoke failed in transport (`:producer-invoke-failed`, A:233), so there is no reviewer
  answer. Witnesses: clicks `36b47627`, `fdc08aea`, `78180753` (429). -/
  | noReviewerAnswer
  /-- `:acceptance-review-refused` (P:628) with `:review-status :refused`: the reviewer
  answered on the merits. Witnesses: click `1a6de51f`
  (`:acceptance-test-did-not-fail-for-injury-reason`) and click `6cdf2a7c` (reason not
  recorded, under the pre-run contract). -/
  | reviewerRefused
  deriving DecidableEq, Repr

/-- A defect at the author/reviewer boundary. -/
inductive BoundaryDefect where
  | proposal (defect : ProposalDefect)
  | admission (defect : AdmissionDefect)
  deriving DecidableEq, Repr

/-- The placement law: the state each defect belongs to, by the `RouteState`
docstrings. `admissionRefused` is "refused before or without a reviewer answer", so
only a reviewer's own refusal is `reviewRefused`. -/
def BoundaryDefect.state : BoundaryDefect → RouteState
  | .proposal _ => proposalRefused
  | .admission .runRefused => admissionRefused
  | .admission .passesBeforeRepair => admissionRefused
  | .admission .noReviewerAnswer => admissionRefused
  | .admission .reviewerRefused => reviewRefused

/-- What a bounded run recorded (A:372-373). A test that does not compile is recorded
`failed` (see the module hole). -/
inductive RunOutcome where
  | passed | failed | errored
  deriving DecidableEq, Repr

/-- An acceptance observation as a route check reports it: the state, the defect
beside it, and the bounded run's outcome when there was one.

Why a record plus a placement function, rather than a defect-indexed state: the
function is the single placement law, and the record is what a click's observation
gives a checker. A checker's verdict is then a record, and `placed` says whether it
obeys the law. Putting the defect inside the state would grow `RouteState`, and every
edge would have to be repeated per defect. -/
structure BoundaryObservation where
  state : RouteState
  defect : Option BoundaryDefect
  run : Option RunOutcome
  deriving DecidableEq, Repr

/-- An observation obeys the placement law. -/
def BoundaryObservation.placed (o : BoundaryObservation) : Bool :=
  match o.defect with
  | none => true
  | some d => stateEq d.state o.state

/-! Frozen witnesses. Each is read from the click's acceptance record under
`futon3c/data/wm-click-acceptances/`. That is run data and not in git, so each is cited
by path and sha256 (read 2026-10-20) rather than at a commit. -/

/-- Click `wm-click-8df4e8d2-e6ad-4768-9af1-c79a78e67680` (Zai cast, 21:14Z):
`:acceptance-unavailable`, `:acceptance-reason :meta-self-heal/producer-response-malformed`.
No bounded run. File `click-wm-click-8df4e8d2-e6ad-4768-9af1-c79a78e67680.edn`, sha256
`5d5508fcb26fee687a822a6cef850cc883078b9e716ab1268c46caf79394f2f7`. -/
def click8df4e8d2 : BoundaryObservation :=
  { state := proposalRefused, defect := some (.proposal .unreadableAnswer), run := none }

/-- Click `wm-click-1a6de51f-47bd-418e-a008-8a1ce6600bee` (21:03Z):
`:acceptance-review-refused`, `:review-status :refused`,
`:review-reason :acceptance-test-did-not-fail-for-injury-reason`. The bounded run is
`:ran :failed` exit 1. The PACKETS prose says the test did not compile, and the run
recorded `failed`, not `errored`. The run is read from this file at
`[:result :runtime-disposition :acceptance-observation :request :result]`: the review
request that `admit-acceptance!` carries on its refusal. File
`click-wm-click-1a6de51f-47bd-418e-a008-8a1ce6600bee.edn`, sha256
`8dc5edeaf73bafa72adeb084209e5ad51c65af9554b98f456191986126c8d442`. -/
def click1a6de51f : BoundaryObservation :=
  { state := reviewRefused, defect := some (.admission .reviewerRefused), run := some .failed }

/-- Clicks `wm-click-36b47627-6e08-4402-a09f-1ef09caa8bdc`,
`wm-click-fdc08aea-f82e-4d85-9ca7-5cbce88bad85` and
`wm-click-78180753-7302-44a2-9710-932e571d2f58` (20:41-20:57Z). Each has the same
observation: `:acceptance-review-refused`, `:review-status :failed`,
`:review-reason :meta-self-heal/producer-invoke-failed` (429), and bounded run
`:ran :failed` exit 1, read from each file at
`[:result :runtime-disposition :acceptance-observation :request :result]`. sha256 respectively
`2cf7272a570702b00c9d263085bd8091b19627d4f5056dcfe994ba01e1300bb4`,
`49d46875fd942b7eaed36d850d19d4a2bcd783ba9dc74f640dd0c004b027b515`,
`3674d5a972c6a08eb1f447c78172010c1f91338ad559f5dcfc7ad1ab6731825a`. -/
def click36b47627 : BoundaryObservation :=
  { state := admissionRefused, defect := some (.admission .noReviewerAnswer), run := some .failed }
def clickFdc08aea : BoundaryObservation := click36b47627
def click78180753 : BoundaryObservation := click36b47627

/-- Click `wm-click-fca1c921-75a7-4ebf-8713-0c464ffbfb0f`: `:acceptance-unavailable`,
`:acceptance-status :refused`, `:acceptance-reason nil` (the author's own refusal,
F10/F11 era). sha256
`a2cfe991a6f528181bb87a39d2c48a224446a617aa82efe2fe7d89ad90559b2a`. -/
def clickFca1c921 : BoundaryObservation :=
  { state := proposalRefused, defect := some (.proposal .authorRefused), run := none }

/-- Click `wm-click-6cdf2a7c-fc11-4988-840c-2a03184b1772`: `:acceptance-review-refused`,
`:review-status :refused`, reason not recorded. Its acceptance record holds no
bounded-run result (the runner arrived after this click). sha256
`d5b2e9dc2f64dbf09789ea3925f963d4522679e181e7c175c4478a24ec3a9d32`. -/
def click6cdf2a7c : BoundaryObservation :=
  { state := reviewRefused, defect := some (.admission .reviewerRefused), run := none }

/-- Every witness obeys the placement law. -/
theorem witnesses_placed :
    click8df4e8d2.placed = true ∧ click1a6de51f.placed = true ∧
      click36b47627.placed = true ∧ clickFdc08aea.placed = true ∧
      click78180753.placed = true ∧ clickFca1c921.placed = true ∧
      click6cdf2a7c.placed = true := by decide

/-- The 2026-10-19 Zai click, the uncompilable-test click and the 429 clicks are three
distinct (state, defect) pairs. The route alone gave all of them the same
`routeRefused`. -/
theorem todaysClicks_distinct :
    (click8df4e8d2.state, click8df4e8d2.defect) ≠ (click1a6de51f.state, click1a6de51f.defect) ∧
      (click8df4e8d2.state, click8df4e8d2.defect) ≠ (click36b47627.state, click36b47627.defect) ∧
      (click1a6de51f.state, click1a6de51f.defect) ≠ (click36b47627.state, click36b47627.defect) := by
  decide

/-- What `wm_route_check.py` (futon2 `8c48e2a16`, rule `reviewRefused` on a non-nil
`review-status`) would report for the observation of clicks `36b47627`, `fdc08aea`,
`78180753`. Their bindings carry no run record (the runner returned none), so the checker
read only the runtime disposition and their sidecars show the `routeRefused` suffix with a
position-0 gap: the rule was wrong but never fired on them. Corrected at futon2 `43d649752`
(M2b, claude-5): `:review-status :failed` projects to `admissionRefused`. -/
def checkerPlacement_36b47627 : BoundaryObservation :=
  { click36b47627 with state := reviewRefused }

/-- The checker's placement of the 429 clicks violates the law: their defect belongs at
`admissionRefused`, and `reviewRefused` is not that state. -/
theorem checkerPlacement_isViolation :
    (BoundaryDefect.admission .noReviewerAnswer).state = admissionRefused ∧
      admissionRefused ≠ reviewRefused ∧
      checkerPlacement_36b47627.placed = false := by decide

/-- Every witness state continues to readiness, as the runtime does after any
acceptance observation. -/
theorem witnesses_reachReadiness :
    edge click8df4e8d2.state readinessReady = true ∧
      edge click1a6de51f.state readinessReady = true ∧
      edge click36b47627.state readinessReady = true := by decide

/-! ## Rev 5: coordination outcomes -/

/-- Where the checkpoint loop stopped (`checkpoints`, P:12), or `final` for the
`coordinate` call after the loop, which runs without `:stop-after`. The record's
`:phase` is the coordinator's own when it gives one (`:port-receipt-refused` C:188 and
`:port-threw` C:194 carry the port's phase), else the loop's; so `retry` can appear: the
retry port (C:337) runs inside the final call. Rev 5 review (claude-5, 2026-10-20). -/
inductive CoordinationPhase where
  | claim | author | review | enact | retry | final
  deriving DecidableEq, Repr

/-- `:held` reasons (`held!`, C:208). The port answered and the transaction waits. -/
inductive HeldReason where
  /-- `:author-failed` (C:268). -/
  | authorFailed
  /-- `:review-rejected` (C:290). -/
  | reviewRejected
  /-- `:enact-failed` (C:313). -/
  | enactFailed
  deriving DecidableEq, Repr

/-- `:refused` reasons of `coordinate` (C:216). Those marked *no ledger* return a map
without `:ledger`, and today `store/persist-ledger!` refuses it, so `route!` reports
`:checkpoint-persist-failed` instead (row #66). -/
inductive CoordinatorRefusal where
  /-- `:coordinator/input-refused` (C:237); no ledger. -/
  | inputRefused
  /-- `:coordinator/resume-state-refused` (C:257); no ledger. -/
  | resumeStateRefused
  /-- `:coordinator/port-receipt-refused` (C:188); carries `:phase`, no ledger. -/
  | portReceiptRefused
  /-- `:coordinator/port-threw` (C:194); carries `:phase`, no ledger. -/
  | portThrew
  /-- `:coordinator/author-payload-refused` (C:272); carries a ledger. -/
  | authorPayloadRefused
  /-- `:coordinator/review-patch-substitution` (C:292); carries a ledger. -/
  | reviewPatchSubstitution
  /-- `:coordinator/enact-payload-refused` (C:318); carries a ledger. -/
  | enactPayloadRefused
  /-- `:coordinator/retry-attribution-refused` (C:345); carries a ledger. -/
  | retryAttributionRefused
  /-- `:coordinator/ledger-transition-refused` (C:201); carries the ledger it refused. -/
  | ledgerTransitionRefused
  /-- `:coordinator/malformed` (C:379, C:381); no ledger. -/
  | malformed
  deriving DecidableEq, Repr

/-- The two writes after a `:checkpoint` result (`:meta-self-heal/checkpoint-persist-failed`,
P:990). -/
inductive PersistWrite where
  | ledgerWrite | transactionWrite
  deriving DecidableEq, Repr

/-- How a transaction closed after enactment: the final `coordinate` result's `:status`. -/
inductive ClosingStatus where
  /-- `:discharged` (C:357, C:364): the retry succeeded. -/
  | discharged
  /-- `:reopened` (C:375, via `ledger/append-retry-result`): the retry did not discharge. -/
  | reopened
  /-- `:abandoned` (C:375): the attempt after this one would exceed the budget. -/
  | abandoned
  /-- `:awaiting-retry` (C:349): the retry port queued the retry click. The production
  retry port only persists and enqueues, so this is the closing status a production
  click is expected to reach. The M4a shape does not name it (finding). -/
  | awaitingRetry
  deriving DecidableEq, Repr

/-- Why the route ended inside, or at the end of, the transaction. -/
inductive CoordinationOutcome where
  | held (reason : HeldReason)
  | refused (reason : CoordinatorRefusal)
  | persistFailed (write : PersistWrite)
  | closed (status : ClosingStatus)
  deriving DecidableEq, Repr

/-- The placement law for the coordination stage. -/
def CoordinationOutcome.state : CoordinationOutcome → RouteState
  | .held _ => coordinationHeld
  | .refused _ => coordinationRefused
  | .persistFailed _ => persistRefused
  | .closed _ => enacted

/-- A coordination result as a route check reports it, after M4a: its state, the loop
phase (`:phase`), and the outcome. -/
structure CoordinationObservation where
  state : RouteState
  phase : CoordinationPhase
  outcome : CoordinationOutcome
  deriving DecidableEq, Repr

/-- An observation obeys the placement law. -/
def CoordinationObservation.placed (o : CoordinationObservation) : Bool :=
  stateEq o.outcome.state o.state

/-- Every new state ends the route. -/
theorem coordinationStates_terminate :
    reaches coordinationHeld terminalRecord = true ∧
      reaches coordinationRefused terminalRecord = true ∧
      reaches persistRefused terminalRecord = true := by decide

/-- A held, refused or persist-failed transaction never goes on to enactment or to
ordinary work (order error 4: true of the runtime only after M4a). -/
theorem coordinationStops_beforeEnactment :
    reaches coordinationHeld enacted = false ∧ reaches coordinationRefused enacted = false ∧
      reaches persistRefused enacted = false ∧
      reaches coordinationHeld ordinarySelection = false ∧
      reaches coordinationRefused ordinarySelection = false ∧
      reaches persistRefused ordinarySelection = false := by decide

/-- `routeEnacted` reaches each coordination outcome's state. -/
theorem routeEnacted_reachesOutcomes :
    reaches routeEnacted coordinationHeld = true ∧
      reaches routeEnacted coordinationRefused = true ∧
      reaches routeEnacted persistRefused = true ∧ reaches routeEnacted enacted = true := by
  decide

/-- Rev 5 adds no path from an active injury to ordinary work. -/
theorem noFallback_rev5 : reaches activeInjury ordinarySelection = false := by decide

/-- Every outcome is placed at a state `routeEnacted` reaches. -/
theorem outcomes_reachable (o : CoordinationOutcome) : reaches routeEnacted o.state = true := by
  cases o <;> rename_i x <;> cases x <;> decide

/-- Row #66: what today's `route!` records when `coordinate` refuses with no ledger
(`:coordinator/input-refused`, at the claim checkpoint). `store/persist-ledger!` refuses
the missing ledger, and the loop reports `:meta-self-heal/checkpoint-persist-failed`
(P:990). -/
def coordination_66_reportedToday : CoordinationObservation :=
  { state := persistRefused, phase := .claim, outcome := .persistFailed .ledgerWrite }

/-- The same result as M4a records it: the coordinator's own refusal. -/
def coordination_66_afterM4a : CoordinationObservation :=
  { state := coordinationRefused, phase := .claim, outcome := .refused .inputRefused }

/-- **The reason M4a exists.** Today's record places a coordinator refusal at
`persistRefused`, but by the law the outcome's own state is `coordinationRefused`, and the
two differ. Each record is internally placed, so `placed` alone cannot catch the mask. The
mask is that the outcome is replaced: a route check over today's records would certify a
persist failure that never happened. -/
theorem coordination_66_masked :
    coordination_66_reportedToday.outcome.state = persistRefused ∧
      (CoordinationOutcome.refused .inputRefused).state = coordinationRefused ∧
      persistRefused ≠ coordinationRefused ∧
      coordination_66_reportedToday.state ≠ coordination_66_afterM4a.state ∧
      coordination_66_afterM4a.placed = true := by decide

/-! ## Rev 6: the start of the route -/

/-- An uncomputable active set never reaches ordinary work, and rev 6 opens no path
from an active injury to it. -/
theorem noFallback_rev6 :
    reaches activeSetUnavailable ordinarySelection = false ∧
      reaches activeInjury ordinarySelection = false := by decide

/-- The read decides each of the four. -/
theorem ledgerRead_decides :
    reaches ledgerRead noActiveInjury = true ∧ reaches ledgerRead activeInjury = true ∧
      reaches ledgerRead ledgerUnreadable = true ∧
      reaches ledgerRead activeSetUnavailable = true := by decide

/-- Order error 1, corrected: an unreadable ledger is a complete path that asserts no
injury. -/
theorem ledgerUnreadable_withoutInjury :
    conformsPath [ledgerRead, ledgerUnreadable, terminalRecord] = true := by decide

/-- Row #5 as today's runtime runs it:
* `ledgerRead → activeSetUnavailable`: `prepare-diagnosis` (P:786);
* `→ acceptanceUnavailable`: `prepare-acceptance`'s `:else` (P:685);
* `→ readinessReady`: `production-readiness` `:else` with `:active-injury? false`
  (P:846), since `(seq (:injuries active))` is nil and no port term is required;
* `→ ordinarySelection`: `route!` reads again and returns nil (P:923-926), and
  `(or routed (run-ordinary-opportunity! …))` runs ordinary work (S:502-503).

The packet's version omitted the acceptance observation. -/
def fallthrough_5_today : List RouteState :=
  [ ledgerRead, activeSetUnavailable, acceptanceUnavailable, readinessReady,
    ordinarySelection, terminalRecord ]

/-- **The reason M6a exists.** Today's path for #5 is not a table path. Its first
missing edge is the step out of `activeSetUnavailable`, which by the table ends the
click. -/
theorem fallthrough_5_isViolation :
    conformsPath fallthrough_5_today = false ∧
      edge ledgerRead activeSetUnavailable = true ∧
      edge activeSetUnavailable acceptanceUnavailable = false := by decide

/-- Without the acceptance observation (the packet's form), the first missing edge is
`(activeSetUnavailable, readinessReady)`. Either way the path does not conform. -/
theorem fallthrough_5_elided_isViolation :
    conformsPath [ledgerRead, activeSetUnavailable, readinessReady, ordinarySelection,
      terminalRecord] = false ∧
      edge activeSetUnavailable readinessReady = false := by decide

/-! ## Rev 7: the retry click -/

/-- The four fields `attributable-retry-readiness` compares (P:909-913): the supplied
retry against the last `:enacted` entry, and the patch sha against its `:authored`
entry. -/
inductive RetryField where
  | injuryId | repairId | retryClick | patchSha
  deriving DecidableEq, Repr

/-- Why the attribution refused (P:905-914). Every constructor is placed at
`retryRefused`. -/
inductive RetryAttributionDefect where
  /-- The ledger did not load (`(= :loaded (:status durable))` fails). -/
  | ledgerNotLoaded
  /-- No `:enacted` entry in the ledger. -/
  | noEnactedEntry
  /-- No `:authored` entry for the enacted injury and repair. -/
  | noAuthoredEntry
  /-- One field of `:supplied` differs from `:expected`. -/
  | fieldDiffers (field : RetryField)
  deriving DecidableEq, Repr

/-- The placement law for the retry attribution. -/
def RetryAttributionDefect.state : RetryAttributionDefect → RouteState
  | _ => retryRefused

/-- Ordinary work has exactly two doors: no active injury, and an attributed retry. -/
theorem ordinaryWork_twoDoors :
    (transitions.filter (fun pair => stateEq pair.2 ordinarySelection)).map Prod.fst =
      [retryReady, noActiveInjury] := by decide

/-- The retry start cannot be reached from the ordinary start, so rev 7 opens no path
from an injury to ordinary work. -/
theorem retryClick_separateStart :
    reaches ledgerRead retryClick = false ∧ reaches activeInjury retryReady = false ∧
      reaches activeSetUnavailable ordinarySelection = false ∧
      reaches activeInjury ordinarySelection = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- A refused attribution ends the click; it never reaches ordinary work. -/
theorem retryRefused_terminates :
    reaches retryRefused terminalRecord = true ∧
      reaches retryRefused ordinarySelection = false := by decide

/-- Both retry paths are complete table paths. -/
theorem retryPaths_conform :
    conformsPath [retryClick, retryReady, ordinarySelection, terminalRecord] = true ∧
      conformsPath [retryClick, retryRefused, terminalRecord] = true := by decide

end DarkTower.WarMachine.SelfHealRoute
