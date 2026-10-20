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
* a `:non-injury` record appends `:discharged` with `:outcome :success` (T:202-224; rev 8 review corrected the line);
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

Revision 8 (claude-2, 2026-10-20, packet M10L from claude-5): the closing law for a
retry click. A retry discharges the injury only when it ran the injured work and came
out successful. An abstention or a no-work outcome is inconclusive: it neither
discharges nor reopens. Today's discharge-on-abstention is the violation witness
`retryClose_todayDischargesAbstention`, and it is the reason for M10a. T = futon2
`343b60ef3` `src/futon2/aif/meta_terminal_injury.clj`, L = the same commit,
`meta_injury_ledger.clj`.

**Holes (rev 8, not decided).**
* Finding 2 of rev 7 is not modelled. A retry that writes no run record leaves the entry
  `:enacted`; the next click resumes `transaction.edn`, `coordinate` replays the
  `:queued` receipt and ends `:awaiting-retry`, and no child is queued again. The table
  would need a re-queue edge, from `retryInconclusive` (and from a missing record) back
  to a queued retry. It is not added here.
* Rev 9 said (2026-10-20, M11L), with the commit that answered each sentence
  (rev 10, read at futon2 `493388b7b` and futon3c `7efc13bd8`):
  - "a re-queue at the same attempt would reuse the id": answered by futon3c
    `e4f58cfc4`. `retry-click-id` mints by ordinal (A:414-426); ordinal 0 keeps
    `wm-retry-...`, and positive ordinals give the disjoint `wm-requeue-<n>-...`.
  - "either way no fresh retry runs": answered by futon3c `f2e5a9fa6` and `7efc13bd8`.
    The child is keyed `meta-retry/<retry-click>` (S:997), and a re-queue carries a fresh
    click, so the runner's reused-key branches are not reached by it.
  - "a second enacted-stage entry is invalid": answered by futon2 `6308c946a`.
    `append-requeue` (L:367-404) appends a new enacted-stage entry with
    `:requeues (inc requeues)`, and the validator steps `:requeues` by one (L:151-152).
  - "`retryBudgetSpent` cannot be recorded today": answered by `6308c946a`. L:394-398
    appends `:abandoned :retry-budget-spent`, and L:174-175 admits it at
    `requeues = retry-limit`.
  - "M10b therefore touches the ledger, the adapter's id, the coordinator and the
    runner": it did (`6308c946a`, `e4f58cfc4`, `aa3ec313b`, `f2e5a9fa6`, `7efc13bd8`,
    `493388b7b`).
  The table is the law; it is not weakened to fit.
* Rev 9: `successfulTaskOutcome` is the only discharge, but `:successful-task-outcome`
  (T:126-128) means the ordinary task succeeded, not that it exercised the injured work.
  Whether a successful retry of different work tests the repair is not decided here.
* `otherInjury` (see `RetryClickOutcome`): a retry that fails with a different cause
  opens a new injury and leaves the enacted one untouched. The law calls that
  inconclusive for the enacted injury. That is a modelling decision, and whoever rules
  on M10a should confirm it.

Revision 9 (claude-2, 2026-10-20, packet M11L from claude-5): the code meets the closing
law (`closingToday_eq_closing`, futon2 `11fe9094a`). The law adds the re-queue edge,
`RetryClickOutcome.next`: an inconclusive close queues a fresh retry under a re-queue
budget kept separate from `:attempt-limit`. `requeue_todayAwaitsForever` is the reason for
M10b. The rev 8 code is kept as `closingBefore83f72ba1e`. T and L are cited at futon2
`11fe9094a`, C at the same commit (`meta_repair_coordinator.clj`).

Revision 10 (claude-2, 2026-10-20, packet M12L from claude-5): the re-queue edge is met
for the outcomes the code observes, and not for two. C, L, T and P are cited at futon2
`493388b7b`; A and S at futon3c `7efc13bd8`. The rev 9 functions are kept as
`nextBeforeAa3ec313b` and `resumeBeforeAa3ec313b`. `nextToday_eq_next_ofObserved` says
the code meets `next` on every outcome except `otherInjury` and `recordUnreadable`.
`requeue_todayMissesUnobserved` is the witness for those two.

Revision 11 (claude-2, 2026-10-20, from claude-5 after M10b-4, futon2 `d0a890f22`,
review `b5dd9269c`): the ingested different-cause arms now write the observation
(T:185-196, T:246-301 at `b5dd9269c`), so `otherInjury` is met
(`requeue_otherInjuryMet`). The refused arms are split off as `otherInjuryRefused`, which
joins `recordUnreadable` in the disagreement.

**Holes (rev 10, not decided).**
* The re-queue detector is `pending-requeue` (L:331-344): it needs a `:retry-inconclusive`
  observation that names the current retry click. Only the no-work branch of `integrate`
  writes one (T:222-227). At rev 10, a retry that failed with a different cause
  (T:233-277: open, repeat observation, or refusal) wrote none, and neither did a retry
  that left no record. Since rev 11 (`b5dd9269c`) the open and repeat arms write it
  (T:253-266, T:288-297); the refusal arms (T:268-286, T:299-300) and a missing record
  still do not. In those cases the coordinator ends `:awaiting-retry` with nothing queued
  (C:247-251), every later click repeats that, and the retry budget is never spent. This
  is rev 9's await-forever for those two outcomes. The law is not weakened; the code is
  the open side (`requeue_todayMissesUnobserved`).
* No live click has re-queued yet. No `:retry-requeue-<n>` receipt exists, and on
  2026-10-20 there is no `transaction.edn` under `data/wm-meta-injuries`. Rev 10 states
  by reading that the code meets the law; the record witness is missing (observed, not
  recorded, as for L1's click 1).
* `retriesSpent` is a Bool in the law. Today it is `requeues >= retry-limit`, with the
  limit kept on the ledger (L:92, L:394). Whether the counter belongs in the model is not
  decided here.
* `RetryEntry` carries no click id. The across-click edge (rev 7: a queued retry is the
  next click's `retryClick` start) relies on the re-queued child being keyed
  `meta-retry/<new click>` (S:997), with the new id minted at ordinal `requeues + 1`
  (C:252-257). No field is added for this without a case.
* The rev 9 question whether a successful retry of different work tests the repair still
  stands.

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
  and `production-readiness` (P:801) decide from it, before any injury is known.
  Order error 3: `route!` reads the ledger a second time (P:923-925), and that read has no
  state here. A runtime that reads twice conforms only while the two reads agree. M6a is
  to make `route!` use the context's read.
  Rev 8 note: with one read, a stale context overwrites a ledger file that changed
  between the read and coordination's persist. That is the one-read design taken
  literally, and it is pinned by `route-decides-from-the-context-read-not-a-second-read`
  (futon2 `6dd147e6a`).
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P diagnosis-context {:durable-ledger :active-injuries})`.
  The map has no `:status`, so no status literal is the site. Since then `route!` takes
  `(:meta-diagnosis-context opts)` and reads the ledger itself only when it is given no
  context (`(P route! durable)`), so order error 3 no longer arises from `run-opportunity!`. -/
  | ledgerRead
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): no ledger file,
  `(P prepare-diagnosis {:status :not-required :reason :meta-self-heal/no-durable-injury-ledger})`
  (#3); an empty active set,
  `(P prepare-diagnosis {:status :not-required :reason :meta-self-heal/no-active-injury})`
  (#6). `route!` then returns nil (`(P route! (when (seq (:injuries active))))`). -/
  | noActiveInjury
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P prepare-diagnosis :else)`: the ledger loaded, the
  active set computed and is non-empty, and `produce-diagnosis!` is called on its first
  injury id. That branch has no status literal of its own. -/
  | activeInjury
  /-- Rev 6, row #5: the ledger loaded, but `ledger/active-injuries` did not return
  `:computed` (P:780, `:diagnosis-active-set-unavailable`). A terminal refusal.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): the observation
  `(P prepare-diagnosis {:status :unavailable :reason :meta-self-heal/diagnosis-active-set-unavailable})`,
  then the refusal
  `(R run-opportunity! {:status :refused :reason :meta-self-heal/active-set-unavailable})`
  in the first `cond` arm. `(P route! :meta-self-heal/active-set-unavailable)` is the
  same guard for a caller that is not `run-opportunity!`; from `run-opportunity!` it is
  not reached, because the R arm ends the click on the same context first. -/
  | activeSetUnavailable
  /-- Rev 7: the start of a retry click. Its options carry `:meta-repair-retry`
  (S:989-995): the child of a parent that ended `:awaiting-retry`, launched only after
  the parent click is durably complete. It makes no ledger read of its own and no
  diagnosis (R:473-477). It carries the acceptance observation
  `:acceptance-retry-not-prepared` (#22), which is typed, not a state.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(S close-click! :meta-repair-retry)` sets the option, in the
  child `click!` it launches after the parent's release. In `run-opportunity!` the branch is
  `(R run-opportunity! retry)`, and its one site is the observation
  `(R run-opportunity! {:status :not-required :reason :meta-self-heal/acceptance-retry-not-prepared})`. -/
  | retryClick
  /-- Rev 7: `attributable-retry-readiness` (P:896-915) returns `:ready` with the
  attribution. The retry then runs ordinary work (R:500-502), and `route!` is not
  called.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P attributable-retry-readiness {:status :ready :attribution})`,
  then `(R run-opportunity! retry)` runs `run-ordinary-opportunity!`. -/
  | retryReady
  /-- Rev 7, #57: `:meta-self-heal/retry-attribution-refused` (P:918), with `:expected`
  and `:supplied`.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P attributable-retry-readiness :meta-self-heal/retry-attribution-refused)`,
  returned by `(R run-opportunity! (= :refused (:status readiness)))`. -/
  | retryRefused
  -- diagnosis stage (`prepare-diagnosis`)
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P produce-diagnosis! {:status :available})`, after
  `persist-diagnosis!` returned `:persisted`; or a supplied pin,
  `(P prepare-diagnosis {:status :present :source :supplied})`. -/
  | diagnosisPrepared
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): every non-`:available` result of `produce-diagnosis!`:
  `(P produce-diagnosis! :meta-self-heal/diagnosis-source-pin-unavailable)`,
  `(P produce-diagnosis! :meta-self-heal/diagnosis-port-unavailable)`,
  `(P produce-diagnosis! :meta-self-heal/diagnosis-port-returned-nil)`,
  `(P produce-diagnosis! :meta-self-heal/diagnosis-port-malformed)`,
  `(P produce-diagnosis! :meta-self-heal/diagnosis-unavailable)` (a port that threw lands
  here, its reason carried as `:diagnosis-reason`),
  `(P produce-diagnosis! :meta-self-heal/diagnosis-response-missing)`,
  `(P produce-diagnosis! :meta-self-heal/diagnosis-production-functions-absent)`;
  passed through from `(P source-record :meta-self-heal/diagnosis-source-pin-mismatch)`,
  `(P source-record :meta-self-heal/diagnosis-source-unreadable)`,
  `(P persist-diagnosis! :meta-self-heal/diagnosis-path-conflict)` and
  `(P persist-diagnosis! :meta-self-heal/diagnosis-persist-failed)`. -/
  | diagnosisRefused
  -- acceptance stage (`prepare-acceptance`)
  /-- Diagnosis not `:available`: `:acceptance-diagnosis-unavailable`.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P prepare-acceptance {:status :unavailable :reason :meta-self-heal/acceptance-diagnosis-unavailable})`,
  the `:else` arm. -/
  | acceptanceUnavailable
  /-- `produce-acceptance!` did not return `:proposed`.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): from `(P read-diagnosis-receipt)`:
  `:meta-self-heal/acceptance-diagnosis-pin-unavailable`,
  `:meta-self-heal/acceptance-diagnosis-pin-mismatch`,
  `:meta-self-heal/acceptance-diagnosis-unreadable`,
  `:meta-self-heal/acceptance-diagnosis-identity-mismatch`, and that function's own
  `:meta-self-heal/acceptance-diagnosis-unavailable` and
  `:meta-self-heal/diagnosis-production-functions-absent`;
  `(P produce-acceptance! :meta-self-heal/acceptance-port-unavailable)`,
  `(P produce-acceptance! :meta-self-heal/acceptance-request-function-unresolvable)`;
  `(P produce-acceptance-from-request! :meta-self-heal/acceptance-port-returned-nil)`,
  `(P produce-acceptance-from-request! :meta-self-heal/acceptance-port-malformed)`,
  `(P produce-acceptance-from-request! :meta-self-heal/acceptance-unavailable)` (a port
  that threw lands here), `(P produce-acceptance-from-request! :meta-self-heal/acceptance-proposal-source-mismatch)`,
  `(P produce-acceptance-from-request! :meta-self-heal/acceptance-prose-or-malformed)`;
  and the proposal receipt's write, `(P persist-acceptance! :meta-self-heal/acceptance-path-conflict)`,
  `(P persist-acceptance! :meta-self-heal/acceptance-persist-failed)`. -/
  | proposalRefused
  /-- `admit-acceptance!` entered.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): no producing site. `(P prepare-acceptance)` calls
  `admit-acceptance!` when `produce-acceptance!` returns
  `(P produce-acceptance-from-request! {:status :proposed})`; the entry has no status
  literal. -/
  | admissionRun
  /-- Admission refused before or without a reviewer answer.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): before the reviewer is called: from
  `(P read-acceptance-proposal)`, `:meta-self-heal/acceptance-proposal-pin-unavailable`,
  `:meta-self-heal/acceptance-proposal-pin-mismatch`,
  `:meta-self-heal/acceptance-proposal-unreadable`,
  `:meta-self-heal/acceptance-proposal-not-proposed`,
  `:meta-self-heal/acceptance-proposal-review-state-invalid`,
  `:meta-self-heal/acceptance-proposal-identity-mismatch`, that function's
  `:meta-self-heal/acceptance-proposal-source-mismatch` and
  `:meta-self-heal/acceptance-proposal-not-concrete`;
  `(P admit-acceptance! :meta-self-heal/acceptance-run-port-unavailable)`,
  `(P admit-acceptance! :meta-self-heal/acceptance-review-port-unavailable)`,
  `(P admit-acceptance! :meta-self-heal/acceptance-run-refused)` (a run that threw lands
  here), `(P admit-acceptance! :meta-self-heal/acceptance-test-passes-before-repair)`.
  A reviewer that throws is not here: its answer becomes `{:status :failed}` and lands in
  `reviewRefused`. -/
  | admissionRefused
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P admit-acceptance! {:status :accepted :acceptance-admission-pin})`,
  after `persist-acceptance!` returned `:persisted`. -/
  | reviewAccepted
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): the reviewer was called and gave no usable acceptance:
  `(P admit-acceptance! :meta-self-heal/acceptance-review-malformed)`,
  `(P admit-acceptance! :meta-self-heal/acceptance-review-refused)` (a reviewer that
  threw lands here, `:review-status :failed`),
  `(P admit-acceptance! :meta-self-heal/acceptance-review-identity-mismatch)`. -/
  | reviewRefused
  -- readiness (`production-readiness`)
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P production-readiness {:status :ready :active-injury?})`,
  the `:else` arm, or the ordinary-route arm that keeps the absence as
  `{:self-heal {:status :absent}}`. -/
  | readinessReady
  /-- `:production-config-required` with port terms.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P production-readiness :meta-self-heal/production-config-required)`,
  with `:route :dedicated-meta-self-heal` and `:before-ration-spend? true`. -/
  | readinessRefused
  /-- `:ledger-unreadable`.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P production-readiness :meta-self-heal/ledger-unreadable)`.
  Diagnosis has already recorded the same fact as
  `(P prepare-diagnosis {:status :unavailable :reason :meta-self-heal/diagnosis-ledger-unavailable})`. -/
  | ledgerUnreadable
  -- route (`route!`)
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): no producing site. `(P route!)` enters the checkpoint loop
  when `(P diagnosis-transaction-binding {:status :valid})` and
  `(P acceptance-transaction-binding {:status :valid})` both hold; the entry has no status
  literal. -/
  | routeEnacted
  /-- `:production-config-required` with route terms.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P route! :meta-self-heal/production-config-required)`,
  with `:absent-terms` from `:transaction-path`, `:repair-ports`, `:acceptance-run-port`,
  `:diagnosis-evidence`, `:acceptance-test`. -/
  | routeRefused
  /-- `:preparation-refused`: `coordinator/prepare` returned no transaction.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P route! :meta-self-heal/preparation-refused)`. -/
  | preparationRefused
  /-- `:diagnosis-transaction-mismatch` / `:acceptance-transaction-mismatch`.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P diagnosis-transaction-binding :meta-self-heal/diagnosis-transaction-mismatch)`,
  `(P acceptance-transaction-binding :meta-self-heal/acceptance-transaction-mismatch)`,
  and also `(P acceptance-transaction-binding :meta-self-heal/acceptance-transaction-unadmitted)`,
  which the trailing comment did not name; `(P route! (if-not (= :valid (:status binding))))`
  returns them. -/
  | bindingRefused
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P route! settle)` on the result of the `coordinate` call after
  the checkpoint loop, when that result is a closing: the status literals are those of
  `ClosingStatus`, `(C coordinate-queued-retry {:status :awaiting-retry})`,
  `(C coordinate {:status :discharged})` and the computed `(C coordinate {:status (get-in reopened [:entry :state])})`. -/
  | enacted
  /-- Rev 5: a port answered and the transaction waits (`:held`).
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(C held! {:status :held})`, returned through `(P route! settle)`.
  The reasons are `HeldReason`'s. -/
  | coordinationHeld
  /-- Rev 5: `coordinator/coordinate` refused, with or without a ledger.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): a `(C coordinate)` refusal returned through
  `(P route! settle)`. The reasons are `CoordinatorRefusal`'s. -/
  | coordinationRefused
  /-- Rev 5: a `:checkpoint` result's ledger or transaction write failed.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P route! :meta-self-heal/checkpoint-persist-failed)`. -/
  | persistRefused
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): no status literal. `(R run-opportunity! run-ordinary-opportunity!)`,
  from two branches: `retry` after `retryReady`, and `(or routed ...)` when `route!`
  returned nil. -/
  | ordinarySelection
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): no producing site in the files read (P, C, R, A, S, T). It is
  the click's record, written after `run-opportunity!` returns. -/
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
    -- readiness is the same fact), #5 (P:780), or an active injury.
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
  `:producer-invoke-failed` (A:347) or `:producer-seat-unavailable` (A:342),
  carried as `:acceptance-reason` of `:acceptance-unavailable` (P:485).
  Unwitnessed at proposal on disk. -/
  | transport
  /-- The author answered, but not with one EDN map: `:producer-response-malformed`
  (A:355) as `:acceptance-reason` of `:acceptance-unavailable` (P:485).
  Witness: click `8df4e8d2`. -/
  | unreadableAnswer
  /-- The author's own typed refusal: `:acceptance-status :refused` under
  `:acceptance-unavailable` (P:485). Witness: click `fca1c921`. -/
  | authorRefused
  /-- `:acceptance-prose-or-malformed` (P:497): the answer is not a concrete test.
  Unwitnessed. -/
  | prose
  /-- `:acceptance-proposal-source-mismatch` (P:493): the test source's namespace or
  path disagree. Unwitnessed. -/
  | sourceMismatch
  /-- `:acceptance-request-function-unresolvable` (P:556): a function the diagnosis
  names does not resolve in the serving JVM. Unwitnessed. -/
  | unresolvableFunction
  deriving DecidableEq, Repr

/-- Why `admit-acceptance!` did not return `:accepted`. -/
inductive AdmissionDefect where
  /-- `:acceptance-run-refused` (P:648): the bounded run did not return a valid `:ran`
  result (it covers A:485, A:516-525 and the un-namespaced A:519). Unwitnessed. -/
  | runRefused
  /-- `:acceptance-test-passes-before-repair` (P:652, F16): refused before any reviewer
  invoke. Unwitnessed on a click (off-click replay 5 only). -/
  | passesBeforeRepair
  /-- `:acceptance-review-refused` (P:658) with `:review-status :failed`: there is no
  reviewer answer that could be read. That covers a transport or seat failure (A:342,
  A:347), a malformed answer (A:355), or the review port throwing (P:642); widened in
  rev 8 to match the checker and refusal-totality #48b (M8R). Witnesses: clicks
  `36b47627`, `fdc08aea`, `78180753` (429). -/
  | noReviewerAnswer
  /-- `:acceptance-review-refused` (P:658) with `:review-status :refused`: the reviewer
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

/-- What a bounded run recorded (A:498-499). A test that does not compile is recorded
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
  /-- `:discharged` (C:357, C:364): the retry succeeded.
  Rev 14 anchor (futon2 `43bb57fc7`; C, T and L unchanged since `d0a890f22`): `(C coordinate :discharged)`,
  the arm `(= :succeeded (:status retry-receipt))`, after
  `append-transition!` of `:state :discharged`. The C cites above are from before C moved;
  at this HEAD the literal is C:415. -/
  | discharged
  /-- `:reopened` (C:375, via `ledger/append-retry-result`): the retry did not discharge.
  Rev 14 anchor (futon2 `43bb57fc7`; C, T and L unchanged since `d0a890f22`): `(C coordinate ledger/append-retry-result)`, the `:else`
  arm of the retry receipt. The status is computed, `(get-in reopened [:entry :state])`
  (C:426 at this HEAD), and is `:reopened` when `(L append-retry-result :reopened)` takes
  its second arm. -/
  | reopened
  /-- `:abandoned` (C:375): the attempt after this one would exceed the budget.
  Rev 14 anchor (futon2 `43bb57fc7`; C, T and L unchanged since `d0a890f22`): `(C coordinate ledger/append-retry-result)`, the same
  computed status (C:426 at this HEAD), `:abandoned` when
  `(L append-retry-result :attempt-limit-exhausted)` takes its first arm. A second
  abandoned literal exists; it is `RetryNext.abandoned .retryBudgetSpent`, not
  this constructor: `(not C coordinate-queued-retry :retry-budget-spent)`. -/
  | abandoned
  /-- `:awaiting-retry` (C:349): the retry port queued the retry click. The production
  retry port only persists and enqueues, so this is the closing status a production
  click is expected to reach. The M4a shape does not name it (finding).
  Rev 14 anchor (futon2 `43bb57fc7`; C, T and L unchanged since `d0a890f22`): `(C coordinate-queued-retry :awaiting-retry)` (C:248 at
  this HEAD), returned by `coordinate` through its `(= :queued (:status retry-receipt))`
  arm, when `ledger/pending-requeue` finds nothing. -/
  | awaitingRetry
  /-- Rev 8: the retry click ran but did not test the repair (`RetryClickOutcome.closing`).
  The injury is neither discharged nor reopened, and the transaction stays `:enacted`
  and active.
  Rev 14 anchor (futon2 `43bb57fc7`; C, T and L unchanged since `d0a890f22`): not a `coordinate` status. It is the retry
  click's `(T integrate :retry-inconclusive)` observation: the non-injury arm for every
  reason except a successful task outcome (T:236), `(not T classify :successful-task-outcome)`,
  and
  `(T append-other-injury-retry-observation :retry-inconclusive)` (T:189). -/
  | retryInconclusive
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
* `ledgerRead → activeSetUnavailable`: `prepare-diagnosis` (P:780);
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

/-! ## Rev 8: the closing law for a retry click -/

/-- What `classify` (T:111-167) says of the retry click's terminal record, as `integrate`
(T:185-275) receives it. -/
inductive RetryClickOutcome where
  /-- `:successful-task-outcome` (T:126-128): no failure kind, and an outcome in
  `successful-outcomes` (T:15). The only outcome that tests the repair and passes.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T classify :successful-task-outcome)`, the `non-injury-reason` arm for a nil
  failure kind and an outcome in `successful-outcomes`; `integrate` then appends
  `(T integrate :discharged)` for the enacted entry. -/
  | successfulTaskOutcome
  /-- `:injury` with the enacted entry's injury id: `append-retry-result` (T:244, L:299-317).
  The retry failed for the same cause.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T integrate ledger/append-retry-result)`, the arm
  `(= :enacted (:state previous))` with `(= (:retry-click previous) (:click-id classification))`;
  the transition is the computed `(get-in appended [:entry :state])`, so there is no
  keyword literal. -/
  | sameInjury
  /-- `:injury` with a different injury id, and the record is ingested. Cited at futon2
  `b5dd9269c` (M10b-4). `integrate` binds `other-injury-retry?` (T:247-251). If the
  different id is unknown, it opens a new injury (T:253-266). If it is active, it appends
  a `:repeated-active-injury` observation (T:288-297). Either way it then appends the
  attributed `:retry-inconclusive` observation for the enacted entry through
  `append-other-injury-retry-observation` (T:185-196). The enacted entry's state is
  untouched. Added in rev 8 (finding) and widened by the rev 8 review. Rev 11 split off
  the refused arms as `otherInjuryRefused`.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`), re-anchored in rev 16
  to the call the function makes: `(T append-other-injury-retry-observation ledger/append-observation)`
  which appends the retry-inconclusive observation for the enacted entry. The
  function is called from `(T integrate)` on the `(nil? previous)` arm with transition `:open` and on
  the `ledger/active-states` arm with transition `:active-injury-retained`. -/
  | otherInjury
  /-- Rev 11: `:injury` with a different injury id, and the record is refused, not
  ingested (at `b5dd9269c`). This happens when the different id is itself `:enacted` and
  this click is not its retry click (`:injury/retry-click-mismatch`, T:268-286), or when
  the different id is terminal (`:injury/terminal-history-requires-new-transaction`,
  T:299-300). `integrate` returns `{:status :refused}` with no ledger, so no observation is
  written and the pin stays un-ingested. It is a separate constructor, not an
  unobserved `otherInjury`, because the coordinator receives a refusal rather than an
  ingested record without an observation. Under the law it is still inconclusive for the
  enacted injury.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T integrate :injury/retry-click-mismatch)`,
  `(T integrate :injury/terminal-history-requires-new-transaction)`. -/
  | otherInjuryRefused
  /-- `:ordinary-selection-abstention` (T:82): an abstention.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T abstention-reason :ordinary-selection-abstention)`, the `:else`
  arm, reached from `classify` when the failure kind is `:abstained` and the route is
  configured. The `{:abstained :ordinary-selection-abstention}` entry of
  `explicit-non-injury-kinds` is never read for it: `classify` takes the `:abstained`
  branch first. -/
  | ordinarySelectionAbstention
  /-- `:evaluated-no-action` (T:81, T:66-70): scored, and no action chosen.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T abstention-reason :evaluated-no-action)`, guarded by
  `evaluated-no-action?` (`:policy-nondiscrimination` among the causes). -/
  | evaluatedNoAction
  /-- `:partial-frontier-continuation` (T:80, T:71-76).
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T abstention-reason :partial-frontier-continuation)`, guarded by
  `partial-frontier-continuation?`. -/
  | partialFrontierContinuation
  /-- `:operator-cancelled` (T:12).
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T explicit-non-injury-kinds :operator-cancelled)`, read in
  `classify`'s `non-injury-reason`. -/
  | operatorCancelled
  /-- `:declared-no-work` (T:13).
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T explicit-non-injury-kinds :declared-no-work)`, read in
  `classify`'s `non-injury-reason`. -/
  | declaredNoWork
  /-- `:diagnostic-only` (T:14).
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T explicit-non-injury-kinds :diagnostic-only)`, read in
  `classify`'s `non-injury-reason`. -/
  | diagnosticOnly
  /-- `:absent-terminal-failure` (T:129-130): no failure kind and no outcome.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T classify :absent-terminal-failure)`, the `non-injury-reason` arm for a nil
  failure kind and a nil outcome. -/
  | absentTerminalFailure
  /-- Rev 9: the retry click left no record that can be read. Then nothing reaches
  `integrate`, and the entry stays `:enacted`. Absence is evidence of neither success nor
  failure, so this is inconclusive (the 2026-09-24 rule that absence must not read as a
  value).
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): no producing site in T for a retry that wrote no record:
  nothing is ingested. A record that exists but cannot be ingested stops before
  `integrate` at `(meta-injury-store ingest-record-file! :store/record-ingest-failed)` or at
  `read-one-form`'s non-`:read` result (that file has no tag), and a record that does not
  classify stops at `(T classify :terminal-record/malformed)`. Reading those as this
  constructor is my reading, not something the Lean states. -/
  | recordUnreadable
  deriving DecidableEq, Repr

/-- The closing law. Only a successful task outcome discharges. The same injury reopens,
or is abandoned when the next attempt would exceed `:attempt-limit` (L:308-314; this is
the `budgetSpent` parameter). Everything else is inconclusive for the enacted injury. -/
def RetryClickOutcome.closing (budgetSpent : Bool) : RetryClickOutcome → ClosingStatus
  | .successfulTaskOutcome => .discharged
  | .sameInjury => if budgetSpent then .abandoned else .reopened
  | _ => .retryInconclusive

/-- `integrate` before futon2 `83f72ba1e` (M10a), at `343b60ef3`. Kept as the record of
the disagreement that M10a removed. Every `:non-injury` classification of the retry click
appended `:discharged :outcome :success` (T:202-224 at `343b60ef3`). The same injury went
through `append-retry-result`; another injury, or no record at all, left the enacted
entry as it was, which by its effect is `retryInconclusive`. -/
def RetryClickOutcome.closingBefore83f72ba1e (budgetSpent : Bool) :
    RetryClickOutcome → ClosingStatus
  | .sameInjury => if budgetSpent then .abandoned else .reopened
  | .otherInjury => .retryInconclusive
  | .otherInjuryRefused => .retryInconclusive
  | .recordUnreadable => .retryInconclusive
  | _ => .discharged

/-- Only a successful task outcome discharges, under either budget. -/
theorem closing_dischargesOnlyOnSuccess (b : Bool) (o : RetryClickOutcome) :
    o.closing b = .discharged ↔ o = .successfulTaskOutcome := by
  cases b <;> cases o <;> decide

/-- **The reason M10a existed.** `integrate` at `343b60ef3` (T:202-224), given `classify`'s
abstention (T:111-167, T:77-82), recorded an abstained retry as `:discharged`; the law
records it as `retryInconclusive`. The two differed, so the repair was recorded as healed
without having been tested. -/
theorem retryClose_todayDischargesAbstention :
    RetryClickOutcome.ordinarySelectionAbstention.closingBefore83f72ba1e false = .discharged ∧
      RetryClickOutcome.ordinarySelectionAbstention.closing false = .retryInconclusive ∧
      ClosingStatus.discharged ≠ ClosingStatus.retryInconclusive := by decide

/-- The law and the code before `83f72ba1e` disagreed on exactly the seven no-work
outcomes. -/
theorem retryClose_disagreement (b : Bool) (o : RetryClickOutcome) :
    o.closingBefore83f72ba1e b ≠ o.closing b ↔
      o ∈ [.ordinarySelectionAbstention, .evaluatedNoAction, .partialFrontierContinuation,
           .operatorCancelled, .declaredNoWork, .diagnosticOnly, .absentTerminalFailure] := by
  cases b <;> cases o <;> decide

/-- An inconclusive close is placed at `enacted`, like the other closings. -/
theorem retryInconclusive_placedAtEnacted :
    (CoordinationOutcome.closed .retryInconclusive).state = enacted := by decide

/-! ## Rev 9: the law is met; the re-queue edge -/

/-- `integrate` today (futon2 `11fe9094a`, after M10a `83f72ba1e`), case by case:
* on the retry click, `:successful-task-outcome` appends `:discharged` (T:204-221);
* every other `:non-injury-reason` on the retry click appends an observation
  `:retry-inconclusive` and leaves the entry `:enacted` (T:222-225);
* the same injury calls `append-retry-result` (T:241-256 region, from T:231), giving
  `:reopened`, or `:abandoned` past `:attempt-limit` (L:308-314);
* another injury does not touch the enacted entry (T:227-239);
* no record reaches `integrate` at all. -/
def RetryClickOutcome.closingToday (budgetSpent : Bool) : RetryClickOutcome → ClosingStatus
  | .successfulTaskOutcome => .discharged
  | .sameInjury => if budgetSpent then .abandoned else .reopened
  | .otherInjury => .retryInconclusive
  | .otherInjuryRefused => .retryInconclusive
  | .recordUnreadable => .retryInconclusive
  | .ordinarySelectionAbstention => .retryInconclusive
  | .evaluatedNoAction => .retryInconclusive
  | .partialFrontierContinuation => .retryInconclusive
  | .operatorCancelled => .retryInconclusive
  | .declaredNoWork => .retryInconclusive
  | .diagnosticOnly => .retryInconclusive
  | .absentTerminalFailure => .retryInconclusive

/-- The code now meets the closing law, case by case. -/
theorem closingToday_eq_closing (b : Bool) (o : RetryClickOutcome) :
    o.closingToday b = o.closing b := by
  cases b <;> cases o <;> decide

/-- Why an injury was abandoned. -/
inductive AbandonReason where
  /-- `:attempt-limit-exhausted` (L:314): the next authoring would exceed `:attempt-limit`.
  Rev 15 anchor (futon2 `5a066d9ab`; C and L unchanged since `aa3ec313b`): `(L append-retry-result :attempt-limit-exhausted)`
  (L:360 at this HEAD; the L:314 cite is from before L moved), reached through
  `(C coordinate ledger/append-retry-result)`. `validate-ledger`'s abandonment check
  (L:173) accepts it only at `attempt = limit`. -/
  | attemptLimitExhausted
  /-- Rev 9 (new, M10b): the re-queue budget for inconclusive retries is spent. A re-queue
  authors nothing, so it does not count against `:attempt-limit`.
  Rev 15 anchor (futon2 `5a066d9ab`; C and L unchanged since `aa3ec313b`): `(L append-requeue :retry-budget-spent)` (L:397), the
  arm where the entry's requeue count has reached the ledger's retry limit (L:394), with
  the attempt carried over unchanged. `(C coordinate-queued-retry :retry-budget-spent)`
  (C:261) returns it, after reading the appended entry's state (C:260), before any
  retry port call. `validate-ledger` accepts it only when the requeue count equals the
  retry limit (L:174-176). -/
  | retryBudgetSpent
  deriving DecidableEq, Repr

/-- The enacted entry a retry belongs to: its attempt (authorings) and the re-queues so
far. -/
structure RetryEntry where
  attempt : Nat
  requeues : Nat
  deriving DecidableEq, Repr

/-- What the injury does after a retry click closes. -/
inductive RetryNext where
  /-- A fresh retry click is queued for the same enacted entry.
  Rev 15 anchor (futon2 `5a066d9ab`; C and L unchanged since `aa3ec313b`): `(C coordinate-queued-retry ledger/append-requeue)`
  (C:258), on the arm where `ledger/pending-requeue` (C:247, L:331) finds the attributed
  observation, and then `(L append-requeue :enacted)` (L:402), a new enacted entry with a
  new retry click. The entry's fields: `attempt` is the ledger's attempt, copied from the
  previous entry (L:392); `requeues` is the ledger's requeue count, read at L:390 and
  written incremented at L:404. On the `recur` (C:267), C reads that count back (C:232)
  and, being positive, calls the retry port with the requeue ordinal (C:233-238). The
  queued click then ends the same way as `awaitingNothingQueued`: the new entry has no
  observation yet, so `coordinate` returns the awaiting-retry status. In the code the
  two constructors differ by the appended entry and the port call, not by the status. -/
  | queued (entry : RetryEntry)
  /-- The transaction ends `:awaiting-retry`, and nothing is queued.
  Rev 15 anchor (futon2 `5a066d9ab`; C and L unchanged since `aa3ec313b`): `(C coordinate-queued-retry :awaiting-retry)`
  (C:248), the arm where `ledger/pending-requeue` (C:247) returns nil. -/
  | awaitingNothingQueued
  /-- Rev 15 anchor (futon2 `5a066d9ab`; C and L unchanged since `aa3ec313b`): no producing site of its own; see
  `ClosingStatus.discharged`, which `next` passes through. -/
  | discharged
  /-- Rev 15 anchor (futon2 `5a066d9ab`; C and L unchanged since `aa3ec313b`): no producing site of its own; see
  `ClosingStatus.reopened`, which `next` passes through. -/
  | reopened
  /-- Rev 15 anchor (futon2 `5a066d9ab`; C and L unchanged since `aa3ec313b`): no producing site of its own; see the
  two `AbandonReason` constructors, which carry the sites. -/
  | abandoned (reason : AbandonReason)
  deriving DecidableEq, Repr

/-- The law for the next step. An inconclusive close re-queues a retry without using an
attempt, unless the re-queue budget (`retriesSpent`) is spent, in which case the injury is
abandoned with `retryBudgetSpent`. The across-click edge is: a queued retry is the next
click's `retryClick` start (rev 7). -/
def RetryClickOutcome.next (budgetSpent retriesSpent : Bool) (o : RetryClickOutcome)
    (e : RetryEntry) : RetryNext :=
  match o.closing budgetSpent with
  | .discharged => .discharged
  | .reopened => .reopened
  | .abandoned => .abandoned .attemptLimitExhausted
  | .retryInconclusive =>
      if retriesSpent then .abandoned .retryBudgetSpent
      else .queued { e with requeues := e.requeues + 1 }
  | .awaitingRetry => .awaitingNothingQueued

/-- The next step before futon2 `aa3ec313b` (M10b-3b), at `11fe9094a`. Kept as the record
of the disagreement that M10b removed. After an inconclusive close the entry stayed
`:enacted`. The next click resumed `transaction.edn` (P:705-710). `coordinate` reaches the retry phase, `invoke-once` finds
the recorded `:queued` receipt and returns it without calling the port (C:177-179). The
`:queued` branch then ends `:awaiting-retry` (C:348-352), and no child is queued. -/
def RetryClickOutcome.nextBeforeAa3ec313b (budgetSpent : Bool) (o : RetryClickOutcome)
    (_e : RetryEntry) : RetryNext :=
  match o.closingToday budgetSpent with
  | .discharged => .discharged
  | .reopened => .reopened
  | .abandoned => .abandoned .attemptLimitExhausted
  | _ => .awaitingNothingQueued

/-- The resume of an `:awaiting-retry` transaction before `aa3ec313b`: the same replay,
the same end. Renamed with `nextBeforeAa3ec313b`; rev 10 defines no `resumeToday`, since
today's resume is the call to `coordinate-queued-retry` that `nextToday` describes. -/
def resumeBeforeAa3ec313b : RetryNext → RetryNext
  | .awaitingNothingQueued => .awaitingNothingQueued
  | n => n

/-- An inconclusive close with retries unspent queues a fresh retry. -/
theorem inconclusive_requeues (b : Bool) (o : RetryClickOutcome) (e : RetryEntry)
    (h : o.closing b = .retryInconclusive) :
    o.next b false e = .queued { e with requeues := e.requeues + 1 } := by
  simp [RetryClickOutcome.next, h]

/-- With retries spent, an inconclusive close abandons the injury. -/
theorem inconclusive_abandonsWhenSpent (b : Bool) (o : RetryClickOutcome) (e : RetryEntry)
    (h : o.closing b = .retryInconclusive) :
    o.next b true e = .abandoned .retryBudgetSpent := by
  simp [RetryClickOutcome.next, h]

/-- A re-queued retry keeps the enacted entry's attempt. -/
theorem requeue_consumesNoAttempt (b r : Bool) (o : RetryClickOutcome) (e e' : RetryEntry)
    (h : o.next b r e = .queued e') : e'.attempt = e.attempt := by
  cases r <;> cases hc : o.closing b <;> simp [RetryClickOutcome.next, hc] at h
  all_goals (subst h; rfl)

/-- **The reason M10b existed.** Under the abstention regime every retry was inconclusive.
Before `aa3ec313b` the next step was then `awaitingNothingQueued`, and resuming it gave the
same step again, while the law queues a fresh retry. -/
theorem requeue_todayAwaitsForever (b : Bool) (e : RetryEntry) :
    RetryClickOutcome.ordinarySelectionAbstention.nextBeforeAa3ec313b b e =
        .awaitingNothingQueued ∧
      resumeBeforeAa3ec313b .awaitingNothingQueued = .awaitingNothingQueued ∧
      RetryClickOutcome.ordinarySelectionAbstention.next b false e =
        .queued { e with requeues := e.requeues + 1 } ∧
      RetryNext.awaitingNothingQueued ≠ .queued { e with requeues := e.requeues + 1 } := by
  cases b <;> simp [RetryClickOutcome.nextBeforeAa3ec313b, RetryClickOutcome.next,
    RetryClickOutcome.closingToday, RetryClickOutcome.closing, resumeBeforeAa3ec313b]

/-! ## Rev 10: the re-queue edge, as the code now has it -/

/-- Whether the retry click's outcome leaves a `:retry-inconclusive` observation that
names the enacted entry's click. That observation is what `pending-requeue` (L:331-344)
detects. The no-work branch of `integrate` writes it (T:222-227 at `493388b7b`). Since
rev 11 (futon2 `b5dd9269c`, M10b-4), the ingested different-cause arms also write it,
through `append-other-injury-retry-observation` (T:185-196, T:253-266, T:288-297). The
refused arms (T:268-286, T:299-300) write none, and a missing record reaches `integrate`
not at all. -/
def RetryClickOutcome.observedInconclusive : RetryClickOutcome → Bool
  | .otherInjuryRefused => false
  | .recordUnreadable => false
  | _ => true

/-- The next step today (futon2 `aa3ec313b`, wired by futon3c `7efc13bd8` and futon2
`493388b7b`). The `:queued` branch of the retry phase enters `coordinate-queued-retry`
(C:401-402, C:227-267). When `pending-requeue` finds the observation (C:247), it mints
`(retry-click-id repair-id attempt (inc n))` (C:252-257, A:414-426) and calls
`append-requeue` (C:258). With `requeues >= retry-limit` (L:394) that appends `:abandoned
:retry-budget-spent` (L:397-398), and the coordinator returns with no port call (C:261).
Otherwise it appends a new enacted-stage entry with the same `:attempt` and
`:requeues (inc requeues)` (L:399-404), and the recur queues the new click (C:267). With
no observation it ends `:awaiting-retry` and queues nothing (C:247-251). The other
closings are as in `next`. -/
def RetryClickOutcome.nextToday (budgetSpent retriesSpent : Bool) (o : RetryClickOutcome)
    (e : RetryEntry) : RetryNext :=
  match o.closingToday budgetSpent with
  | .discharged => .discharged
  | .reopened => .reopened
  | .abandoned => .abandoned .attemptLimitExhausted
  | .retryInconclusive =>
      if !o.observedInconclusive then .awaitingNothingQueued
      else if retriesSpent then .abandoned .retryBudgetSpent
      else .queued { e with requeues := e.requeues + 1 }
  | .awaitingRetry => .awaitingNothingQueued

/-- The code meets `next` on every outcome that leaves the observation. -/
theorem nextToday_eq_next_ofObserved (b r : Bool) (o : RetryClickOutcome) (e : RetryEntry)
    (h : o.observedInconclusive = true) : o.nextToday b r e = o.next b r e := by
  cases b <;> cases r <;> cases o <;>
    simp_all [RetryClickOutcome.nextToday, RetryClickOutcome.next,
      RetryClickOutcome.closingToday, RetryClickOutcome.closing,
      RetryClickOutcome.observedInconclusive]

/-- The code and the law differ on exactly `otherInjuryRefused` and `recordUnreadable`
(rev 11; at rev 10 the list held `otherInjury` instead of `otherInjuryRefused`). -/
theorem nextToday_disagreement (b r : Bool) (o : RetryClickOutcome) (e : RetryEntry) :
    o.nextToday b r e ≠ o.next b r e ↔ o ∈ [.otherInjuryRefused, .recordUnreadable] := by
  cases b <;> cases r <;> cases o <;>
    simp [RetryClickOutcome.nextToday, RetryClickOutcome.next,
      RetryClickOutcome.closingToday, RetryClickOutcome.closing,
      RetryClickOutcome.observedInconclusive]

/-- **Witness: the re-queue misses two inconclusive outcomes.** A retry that left no
record, or whose different-cause record was refused (T:268-286, T:299-300 at
`b5dd9269c`), is inconclusive under the law, which queues a fresh retry. Today no
`:retry-inconclusive` observation is written for it, so `pending-requeue` is nil
(L:331-344) and the coordinator ends `:awaiting-retry` with nothing queued (C:247-251).
At rev 10 the second outcome was every `otherInjury`; M10b-4 closed the ingested arms. -/
theorem requeue_todayMissesUnobserved (b : Bool) (e : RetryEntry) :
    RetryClickOutcome.recordUnreadable.nextToday b false e = .awaitingNothingQueued ∧
      RetryClickOutcome.otherInjuryRefused.nextToday b false e = .awaitingNothingQueued ∧
      RetryClickOutcome.recordUnreadable.next b false e =
        .queued { e with requeues := e.requeues + 1 } ∧
      RetryClickOutcome.otherInjuryRefused.next b false e =
        .queued { e with requeues := e.requeues + 1 } := by
  cases b <;> simp [RetryClickOutcome.nextToday, RetryClickOutcome.next,
    RetryClickOutcome.closingToday, RetryClickOutcome.closing,
    RetryClickOutcome.observedInconclusive]

/-- The no-work outcome the abstention regime produces is met: an abstained retry
re-queues today. -/
theorem requeue_abstentionMet (b r : Bool) (e : RetryEntry) :
    RetryClickOutcome.ordinarySelectionAbstention.nextToday b r e =
      RetryClickOutcome.ordinarySelectionAbstention.next b r e :=
  nextToday_eq_next_ofObserved b r _ e rfl

/-- Rev 11 (M10b-4): an ingested different-cause retry re-queues today. -/
theorem requeue_otherInjuryMet (b r : Bool) (e : RetryEntry) :
    RetryClickOutcome.otherInjury.nextToday b r e = RetryClickOutcome.otherInjury.next b r e :=
  nextToday_eq_next_ofObserved b r _ e rfl

end DarkTower.WarMachine.SelfHealRoute
