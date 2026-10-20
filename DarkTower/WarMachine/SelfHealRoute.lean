import Mathlib.Data.List.Basic

/-!
# Self-heal route, level 1

`CLOSED-BY-RECORD`: this is the finite control-flow table transcribed from
`futon2/holes/labs/wm-contract/logic-model/phases.md`, "Injury vs ordinary,
level 1", under Joe's 2026-10-19 ruling, and from the runtime order in
`futon2/src/futon2/aif/full_loop_runtime.clj`, `(R run-opportunity!)` (futon2 `e4e53617a`).
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
attributable retry (`(R run-opportunity! :meta-repair-retry)`,
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
runner records it as `:failed` exit 1 (`(A launch-bounded-acceptance! "test-failure")`, click `1a6de51f`), so nothing before
review can tell it from a test that fails for the injury.

Revision 5 (claude-2, 2026-10-20, packet M4L from claude-5): the coordination stage
after `routeEnacted`, refusal class 3 of `refusal-totality-2026-10-19.md`. Three new
states, `coordinationHeld`, `coordinationRefused` and `persistRefused`, each ending at
`terminalRecord`, so `RouteState` has 23 states. (Rev 23, F31: one click may now run
several author attempts, so `coordinationHeld` may stand for several attempts of one
click; see `HeldReason.authorFailed`. Rev 24 puts that loop in the table as the cycle
through `transactionRetired`.) Why a click stopped inside the
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
* #54: an admission receipt can fail to persist after an accepted review (`(P admit-acceptance* "persist-acceptance!")`), and
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
not `:available` gives `(P prepare-acceptance :meta-self-heal/acceptance-diagnosis-unavailable)`. So a runtime conforms
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
  futon2 `05e71feb9`: `(I load-ledger)` refuses
  `:store/tampered-ledger` unless `validate-ledger` is `:valid`, and
  `(L active-injuries "validate-ledger")` runs the same `validate-ledger`
  on the same in-memory value (`(P diagnosis-context ledger/active-injuries)`). `validate-ledger`
  (`(L validate-ledger)`) reads no clock and does no IO, so the second check cannot disagree with the
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
port never answers anything except `:queued` (`(A ports :repair-retry-fn)`). The injury is closed by the
child click's own terminal record: the ordinary runner's `:meta-terminal-injury-ingest`
sink (`(U run-opportunity! :meta-terminal-injury-ingest)`) calls `(I ingest-record-file!)`,
which calls `(I transact-classification!)`, which calls `terminal/integrate`. When
the classification's click id equals the `:enacted` entry's `:retry-click`, `integrate`
does one of two things:
* a `:non-injury` record appends `:discharged` with `:outcome :success` (`(T integrate :discharged)`; rev 8 review corrected the cite);
* an `:injury` record calls `append-retry-result`, giving `:reopened` or `:abandoned`
  (`(T integrate ledger/append-retry-result)`).
The close happens after `ordinarySelection → terminalRecord`, so it is beside the path,
not in it: rev 5's `ClosingStatus` names its outcomes, and no state is added for it.

**Holes (rev 7, not decided).**
* An abstained retry discharges the injury as a success. `(T classify)` makes
  every abstention `:non-injury` unless its cause is
  `:outer-policy-evidence-provider-required` (`(T unconfigured-route?)`, `(T abstention-reason)`). The same holds for
  `:operator-cancelled`, `:declared-no-work`, `:diagnostic-only`, and a record with no
  failure kind and no outcome (`:absent-terminal-failure`). A retry that does no work
  can therefore discharge the repair it was meant to test. This is a finding about the
  code, not a modelling choice.
* A retry click that writes no run record leaves the injury `:enacted`, which is still
  an active state. The next click routes it again: `route!` resumes `transaction.edn`
  (`(P route! "load-transaction")`), and `coordinate` replays the recorded `:queued` retry receipt (`(C invoke-once)`)
  and ends `:awaiting-retry`. The retry port is not called again, so no
  child is queued. By reading, every later click then ends `:awaiting-retry` with no
  retry. Not run.
* Duplicate launch: the idempotency key `meta-retry/<retry-click>` (`(S close-click! "meta-retry/")`) is the only
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
    `e4f58cfc4`. `retry-click-id` mints by ordinal (`(A retry-click-id)`); ordinal 0 keeps
    `wm-retry-...`, and positive ordinals give the disjoint `wm-requeue-<n>-...`.
  - "either way no fresh retry runs": answered by futon3c `f2e5a9fa6` and `7efc13bd8`.
    The child is keyed `meta-retry/<retry-click>` (`(S close-click! "meta-retry/")`), and a re-queue carries a fresh
    click, so the runner's reused-key branches are not reached by it.
  - "a second enacted-stage entry is invalid": answered by futon2 `6308c946a`.
    `(L append-requeue)` appends a new enacted-stage entry with
    `:requeues (inc requeues)`, and the validator steps `:requeues` by one (`(L state-defects :requeues)`).
  - "`retryBudgetSpent` cannot be recorded today": answered by `6308c946a`. `(L append-requeue :retry-budget-spent)`
    appends `:abandoned :retry-budget-spent`, and `(L state-defects :retry-budget-spent)` admits it at
    `requeues = retry-limit`.
  - "M10b therefore touches the ledger, the adapter's id, the coordinator and the
    runner": it did (`6308c946a`, `e4f58cfc4`, `aa3ec313b`, `f2e5a9fa6`, `7efc13bd8`,
    `493388b7b`).
  The table is the law; it is not weakened to fit.
* Rev 9: `successfulTaskOutcome` is the only discharge, but `:successful-task-outcome`
  (`(T classify :successful-task-outcome)`) means the ordinary task succeeded, not that it exercised the injured work.
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
(`(T append-other-injury-retry-observation)`, `(T integrate)` at `b5dd9269c`), so `otherInjury` is met
(`requeue_otherInjuryMet`). The refused arms are split off as `otherInjuryRefused`, which
joins `recordUnreadable` in the disagreement.

**Holes (rev 10, not decided).**
* The re-queue detector is `(L pending-requeue :retry-inconclusive)`: it needs a `:retry-inconclusive`
  observation that names the current retry click. Only the no-work branch of `integrate`
  writes one (`(T integrate :retry-inconclusive)`). At rev 10, a retry that failed with a different cause
  (`(T integrate)`: open, repeat observation, or refusal) wrote none, and neither did a retry
  that left no record. Since rev 11 (`b5dd9269c`) the open and repeat arms write it
  (`(T integrate "nil? previous")`, `(T integrate ledger/active-states)`); the refusal arms (`(T integrate :injury/retry-click-mismatch)`, `(T integrate :injury/terminal-history-requires-new-transaction)`) and a missing record
  still do not. In those cases the coordinator ends `:awaiting-retry` with nothing queued
  (`(C coordinate-queued-retry :awaiting-retry)`), every later click repeats that, and the retry budget is never spent. This
  is rev 9's await-forever for those two outcomes. The law is not weakened; the code is
  the open side (`requeue_todayMissesUnobserved`).
* No live click has re-queued yet. No `:retry-requeue-<n>` receipt exists, and on
  2026-10-20 there is no `transaction.edn` under `data/wm-meta-injuries`. Rev 10 states
  by reading that the code meets the law; the record witness is missing (observed, not
  recorded, as for L1's click 1).
* `retriesSpent` is a Bool in the law. Today it is `requeues >= retry-limit`, with the
  limit kept on the ledger (`(L state-defects :retry-limit)`, `(L append-requeue :retry-limit)`). Whether the counter belongs in the model is not
  decided here.
* `RetryEntry` carries no click id. The across-click edge (rev 7: a queued retry is the
  next click's `retryClick` start) relies on the re-queued child being keyed
  `meta-retry/<new click>` (`(S close-click! "meta-retry/")`), with the new id minted at ordinal `requeues + 1`
  (`(C coordinate-queued-retry :retry-click-id)`). No field is added for this without a case.
* The rev 9 question whether a successful retry of different work tests the repair still
  stands.

Revision 24 (claude-2, 2026-10-20, packet M23L from claude-5; P = futon2 `b463d85cc`,
A = futon3c `fe7d3d28e`): the in-click author loop of F31 is in the table. Two new states,
`transactionRetired` and `transactionRetireFailed`, so `RouteState` has 30 states. The
continuation is the cycle `coordinationHeld → transactionRetired → routeEnacted`, and its
refusals are placed by `ContinuationRefusal.state`. `reaches coordinationHeld enacted` is
now true, so `coordinationStops_beforeEnactment` loses that conjunct
(`heldReachesEnactment_onlyByRetirement` says how it is reached). The table does not bound
the cycle; the ledger does, and `retiredVisits_le_attemptBudget` proves the count over an
`AttemptPath` whose passes obey it. `ContinuationOutcome` and `ContinuedAttempt` are on the
held observation, beside the path. `CarriedBindings` gives F32's carried-bindings
observation its own vocabulary.

**AIF leg.** None. No module under `DarkTower/AIF` or `DarkTower/WarMachine`
models injury, repair or route arbitration (claude-2, 2026-10-19). Typed none
until one is named.
-/

namespace DarkTower.WarMachine.SelfHealRoute

-- Rev 7: with 28 states (30 since rev 24) the bounded `reaches` unfolds deeper than the default limit
-- allows `decide` to evaluate.
set_option maxRecDepth 8192

/-- Absence terms a readiness refusal can carry
(`meta_self_heal_production.clj`, `production-readiness`, futon2 `e4e53617a`).

Rev 4 note (claude-5 confirmed, futon3c `840251d7c` `(S meta-self-heal-preflight!)`):
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
  /-- Rev 6: the one ledger read, `(P diagnosis-context)`. `(P prepare-diagnosis)`
  and `(P production-readiness)` decide from it, before any injury is known.
  Order error 3: `route!` reads the ledger a second time (`(P route! :durable-ledger)`), and that read has no
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
  (#6). `route!` then returns nil (`(P route! "(when (seq (:injuries active))")`). -/
  | noActiveInjury
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P prepare-diagnosis :else)`: the ledger loaded, the
  active set computed and is non-empty, and `produce-diagnosis!` is called on its first
  injury id. That branch has no status literal of its own. -/
  | activeInjury
  /-- Rev 6, row #5: the ledger loaded, but `ledger/active-injuries` did not return
  `:computed` (`:diagnosis-active-set-unavailable`). A terminal refusal.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): the observation
  `(P prepare-diagnosis {:status :unavailable :reason :meta-self-heal/diagnosis-active-set-unavailable})`,
  then the refusal
  `(R run-opportunity! {:status :refused :reason :meta-self-heal/active-set-unavailable})`
  in the first `cond` arm. `(P route! :meta-self-heal/active-set-unavailable)` is the
  same guard for a caller that is not `run-opportunity!`; from `run-opportunity!` it is
  not reached, because the R arm ends the click on the same context first. -/
  | activeSetUnavailable
  /-- Rev 7: the start of a retry click. Its options carry `:meta-repair-retry`
  (`(S close-click! :meta-repair-retry)`): the child of a parent that ended `:awaiting-retry`, launched only after
  the parent click is durably complete. It makes no ledger read of its own and no
  diagnosis (`(not R run-opportunity! meta-self-heal/diagnosis-context)`). It carries the acceptance observation
  `:acceptance-retry-not-prepared` (#22), which is typed, not a state.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(S close-click! :meta-repair-retry)` sets the option, in the
  child `click!` it launches after the parent's release. In `run-opportunity!` the branch is
  `(R run-opportunity! retry)`, and its one site is the observation
  `(R run-opportunity! {:status :not-required :reason :meta-self-heal/acceptance-retry-not-prepared})`. -/
  | retryClick
  /-- Rev 7: `(P attributable-retry-readiness)` returns `:ready` with the
  attribution. The retry then runs ordinary work (`(R run-opportunity! "run-ordinary-opportunity!")`), and `route!` is not
  called.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P attributable-retry-readiness {:status :ready :attribution})`,
  then `(R run-opportunity! retry)` runs `run-ordinary-opportunity!`. -/
  | retryReady
  /-- Rev 7, #57: `:meta-self-heal/retry-attribution-refused`, with `:expected`
  and `:supplied`.
  Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P attributable-retry-readiness :meta-self-heal/retry-attribution-refused)`,
  returned by `(R run-opportunity! "(= :refused (:status readiness))")`. -/
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
  `admit-acceptance!` when `produce-acceptance!` returns `{:status :proposed}` from
  `(P produce-acceptance-from-request!)`; the entry has no status literal. Rev 22: the
  `:proposed` map is a guard, cited by function only, so it makes no edge. -/
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
  `(P admit-acceptance* :meta-self-heal/acceptance-run-port-unavailable)`,
  `(P admit-acceptance* :meta-self-heal/acceptance-review-port-unavailable)`,
  `(P admit-acceptance* :meta-self-heal/acceptance-run-refused)` (a run that threw lands
  here), `(P admit-acceptance* :meta-self-heal/acceptance-test-passes-before-repair)`.
  A reviewer that throws is not here: its answer becomes `{:status :failed}` and lands in
  `reviewRefused`. -/
  | admissionRefused
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P admit-acceptance* {:status :accepted :acceptance-admission-pin})`,
  after `persist-acceptance!` returned `:persisted`. -/
  | reviewAccepted
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): the reviewer was called and gave no usable acceptance:
  `(P admit-acceptance* :meta-self-heal/acceptance-review-malformed)`,
  `(P admit-acceptance* :meta-self-heal/acceptance-review-refused)` (a reviewer that
  threw lands here, `:review-status :failed`),
  `(P admit-acceptance* :meta-self-heal/acceptance-review-identity-mismatch)`. -/
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
  when `(P diagnosis-transaction-binding)` and `(P acceptance-transaction-binding)` both
  return `{:status :valid}`; the entry has no status literal. Rev 22: the two `:valid` maps
  are guards, cited by function only, so they make no edge. -/
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
  which the trailing comment did not name; `(P route! "(if-not (= :valid (:status binding))")`
  returns them. -/
  | bindingRefused
  /-- Rev 12 anchor (futon2 `3fe0a2b6d`, futon3c `c16a86952`): `(P route! settle)` on the result of the `coordinate` call after
  the checkpoint loop, when that result is a closing: the status literals are those of
  `ClosingStatus`: `:awaiting-retry` from `(C coordinate-queued-retry)`, `:discharged` from
  `(C coordinate)` and the computed `(C coordinate "{:status (get-in reopened [:entry :state])")`.
  Rev 22: the maps are cited by function only; they realise `ClosingStatus`, not this state. -/
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
  /-- Rev 24 (futon2 `b463d85cc`, F31; packet M23L): the click's continuation after an
  author failure. The edge from `coordinationHeld` is taken only when every part of the
  guard in `(P route! run-attempt)`'s loop holds: the attempt is held, its reason is
  `:author-failed`, its ledger and transaction writes are both `:persisted`, the reload
  `store/load-durable-ledger` is `:loaded`, and the injury's active entry is `:reopened`
  (at attempt n+1, from the authored attempt n). The producing site is
  `(P retire-stale-transaction! :retired)`, called as `(P route! retire-stale-transaction!)`
  on the attempt-n transaction. Then `coordinator/prepare` builds attempt n+1 with
  `(P continued-work-order-options)` and the two bindings re-run: a transaction with both
  bindings valid is `routeEnacted` again (there is no separate prepared state; on the first
  pass `readinessReady` goes to `routeEnacted` the same way), no transaction is
  `preparationRefused`, and a binding that is not valid is `bindingRefused`. Both refusals
  carry `(P route! :continued-from)`. The pass is bounded by the ledger, not by the table
  (`retiredVisits_le_attemptBudget`). -/
  | transactionRetired
  /-- Rev 24 (F31): the retirement was refused,
  `(P retire-stale-transaction! :meta-self-heal/transaction-retire-failed)`, returned by
  `(P route! retire-stale-transaction!)` in two places: before the first prepare, when a
  resumed transaction belongs to an earlier attempt than the ledger's (from
  `readinessReady`), and in the continuation (from `coordinationHeld`, the refusal sibling
  of `transactionRetired`). The second carries `(P route! :continued-from)`, with the
  refused retirement's status and reason in its last entry. A terminal refusal. -/
  | transactionRetireFailed
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
  [ -- rev 6: the ledger read decides #3/#6 (`(P prepare-diagnosis :meta-self-heal/no-durable-injury-ledger :meta-self-heal/no-active-injury)`), #4 (`(P prepare-diagnosis "not= :loaded")`; `(P production-readiness "not= :loaded")` at
    -- readiness is the same fact), #5 (`(P prepare-diagnosis :meta-self-heal/diagnosis-active-set-unavailable)`), or an active injury.
    (ledgerRead, noActiveInjury),
    (ledgerRead, activeInjury),
    (ledgerRead, ledgerUnreadable),
    (ledgerRead, activeSetUnavailable),
    (activeSetUnavailable, terminalRecord),
    -- rev 7: the retry click, a separate start (`(S close-click! :meta-repair-retry)`, `(R run-opportunity!)`, `(P attributable-retry-readiness)`).
    (retryClick, retryReady),
    (retryClick, retryRefused),
    (retryRefused, terminalRecord),
    (retryReady, ordinarySelection),
    -- `phases.md`, "Injury vs ordinary, level 1": ordinary is only no-active-injury.
    (noActiveInjury, ordinarySelection),
    (ordinarySelection, terminalRecord),
    -- `(R run-opportunity! meta-self-heal/diagnosis-context)`: prepare diagnosis.
    (activeInjury, diagnosisPrepared),
    (activeInjury, diagnosisRefused),
    -- `(P prepare-acceptance)`.
    (diagnosisRefused, acceptanceUnavailable),
    (diagnosisPrepared, proposalRefused),
    (diagnosisPrepared, admissionRun),
    (admissionRun, admissionRefused),
    (admissionRun, reviewAccepted),
    (admissionRun, reviewRefused),
    -- `(R run-opportunity! meta-self-heal/production-readiness)`: readiness after every acceptance observation.
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
    -- `(R run-opportunity! meta-self-heal/route!)`: ready input enters dedicated `route!`.
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
    -- rev 24 (F31): a resumed transaction from an earlier attempt is retired before the
    -- first prepare; a refused retirement ends the click.
    (readinessReady, transactionRetireFailed),
    -- rev 24 (F31): the in-click continuation after a persisted `:author-failed` hold
    -- (`(P route! run-attempt)`): retire, prepare attempt n+1, bind, run it again.
    (coordinationHeld, transactionRetired),
    (coordinationHeld, transactionRetireFailed),
    (transactionRetired, routeEnacted),
    (transactionRetired, preparationRefused),
    (transactionRetired, bindingRefused),
    (transactionRetireFailed, terminalRecord),
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
    transactionRetired, transactionRetireFailed,
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
observation retained by the runner (`(U persist-run-record! :meta-self-heal/readiness)`), not a
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
  `(A producer-invoke! :meta-self-heal/producer-invoke-failed)` or `(A producer-invoke! :meta-self-heal/producer-seat-unavailable)`,
  carried as `:acceptance-reason` of `(P produce-acceptance-from-request! :meta-self-heal/acceptance-unavailable)`.
  Unwitnessed at proposal on disk. -/
  | transport
  /-- The author answered, but not with one EDN map: `:producer-response-malformed`
  (`(A producer-invoke! :meta-self-heal/producer-response-malformed)`) as `:acceptance-reason` of `(P produce-acceptance-from-request! :meta-self-heal/acceptance-unavailable)`.
  Witness: click `8df4e8d2`.
  Note (futon3c `33f7fc241`): a map whose test source does not read is not this
  constructor. A removes the one surplus delimiter the reader names (F23, `:repaired`)
  or re-asks once (F22); a source that still does not read is returned as the
  proposal with `:source-read-error`, not as `:producer-response-malformed`. -/
  | unreadableAnswer
  /-- The author's own typed refusal: `:acceptance-status :refused` under
  `(P produce-acceptance-from-request! :meta-self-heal/acceptance-unavailable)`. Witness: click `fca1c921`. -/
  | authorRefused
  /-- `(P produce-acceptance-from-request! :meta-self-heal/acceptance-prose-or-malformed)`: the answer is not a concrete test.
  Unwitnessed. -/
  | prose
  /-- `(P produce-acceptance-from-request! :meta-self-heal/acceptance-proposal-source-mismatch)`: the test source's namespace or
  path disagree. Unwitnessed. -/
  | sourceMismatch
  /-- `(P produce-acceptance! :meta-self-heal/acceptance-request-function-unresolvable)`: a function the diagnosis
  names does not resolve in the serving JVM. Unwitnessed. -/
  | unresolvableFunction
  deriving DecidableEq, Repr

/-- Why `admit-acceptance!` did not return `:accepted`.
Note (futon2 `ef89bd061`): two refusals after the review have no constructor here.
`(P admit-acceptance* :meta-self-heal/acceptance-review-malformed)` is a review port that returned no map.
`(P admit-acceptance* :meta-self-heal/acceptance-review-identity-mismatch)` (F24) is an accepted review whose
identity differs from the request's: `:injury-id`, `:source-record-pin`,
`:diagnosis-evidence-pin`, `:proposal-evidence-pin`, and the acceptance test's `:id`,
`:command` and `:expected` (`(P admit-acceptance* "identity-keys")`); a `:source` echo is ignored. That refusal
carries `:review-identity {:differs … :response-keys …}`. -/
inductive AdmissionDefect where
  /-- `(P admit-acceptance* :meta-self-heal/acceptance-run-refused)`: the bounded run did not return a valid `:ran`
  result. It covers `(A launch-bounded-acceptance! :meta-self-heal/acceptance-unit-launch-failed)`,
  `(A run-acceptance! :meta-self-heal/acceptance-source-path-refused :meta-self-heal/acceptance-command-not-admissible)`,
  the un-namespaced `(A run-acceptance! :acceptance-test-id-invalid)`, and the run port throwing,
  `(P admit-acceptance* :meta-self-heal/acceptance-run-threw)`. Unwitnessed. -/
  | runRefused
  /-- `(P admit-acceptance* :meta-self-heal/acceptance-test-passes-before-repair)` (F16): refused before any reviewer
  invoke. Unwitnessed on a click (off-click replay 5 only). -/
  | passesBeforeRepair
  /-- `(P admit-acceptance* :meta-self-heal/acceptance-review-refused)` with `:review-status :failed`: there is no
  reviewer answer that could be read. That covers a transport or seat failure (`(A producer-invoke! :meta-self-heal/producer-seat-unavailable)`,
  `(A producer-invoke! :meta-self-heal/producer-invoke-failed)`), a malformed answer (`(A producer-invoke! :meta-self-heal/producer-response-malformed)`), or the review port throwing (`(P admit-acceptance* :meta-self-heal/acceptance-review-threw)`); widened in
  rev 8 to match the checker and refusal-totality #48b (M8R). Witnesses: clicks
  `36b47627`, `fdc08aea`, `78180753` (429). -/
  | noReviewerAnswer
  /-- `(P admit-acceptance* :meta-self-heal/acceptance-review-refused)` with `:review-status :refused`: the reviewer
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

/-- What a bounded run recorded (`(A launch-bounded-acceptance! "test-failure" "write-run-result")`). A test that does not compile is recorded
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

/-- Where the checkpoint loop stopped (`(P checkpoints)`), or `final` for the
`coordinate` call after the loop, which runs without `:stop-after`. The record's
`:phase` is the coordinator's own when it gives one (`(C invoke-once :coordinator/port-receipt-refused)` and
`(C invoke-once :coordinator/port-threw)` carry the port's phase), else the loop's; so `retry` can appear: the
retry port (`(C coordinate :retry)`) runs inside the final call. Rev 5 review (claude-5, 2026-10-20). -/
inductive CoordinationPhase where
  | claim | author | review | enact
  /-- The retry port's phase, `(C coordinate :retry)`. Not the carried-bindings absence on a
  retry click, `(not R run-opportunity! :retry)`, which is `CarriedBindings.retryClick`. -/
  | retry
  | final
  deriving DecidableEq, Repr

/-- `:held` reasons (`(C held!)`). The port answered and the transaction waits. -/
inductive HeldReason where
  /-- `(C coordinate :author-failed)`. Rev 21 (futon2 `4e7b31cdc`, F26): the hold is the
  click's disposition (`coordinationHeld`, then `terminalRecord`), but it is no longer the
  injury's end. Before holding, the author arm calls `(C coordinate ledger/append-retry-result)`
  with `:reason :author-failed` and the sealed failed receipt's pin as `:port-receipt-pin`, and
  `held!` carries that ledger. The ledger's latest entry is then `:reopened` at attempt n+1
  from `:claimed`, or `:abandoned` with `(L append-retry-result :attempt-limit-exhausted)`
  (the same pin) when n+1 would exceed `:attempt-limit`; `(L allowed-predecessors :claimed)`
  admits both, and `(L state-defects :reopen/author-failure-evidence)` and
  `(L state-defects :abandonment/author-failure-evidence)` refuse them without the pin.
  Rev 23 (futon2 `fba25030a`, F31): the click does not stop there. `route!` runs the
  checkpoint loop as `(P route! run-attempt)` and loops over attempts. When an attempt is
  held `:author-failed` with both its ledger and transaction writes persisted, the ledger is
  reloaded, and if the injury's active entry is `:reopened` the same click goes on:
  `(P route! retire-stale-transaction!)` retires the attempt-n transaction (a refused
  retirement is the click's disposition), `prepare` builds attempt n+1 from the reloaded
  ledger with `(P continued-work-order-options)` (the three claim sessions suffixed
  `/attempt-` and the attempt number, because `(L state-defects :claim/session-not-fresh)`
  refuses a reused one), the diagnosis and acceptance bindings are re-run against the new
  transaction, and `run-attempt` runs again. The loop stops on any other result, or when the
  active entry is `:abandoned`; the ledger's `:attempt-limit` bounds it. `coordinationHeld`
  is where the click ends only when the last attempt of the loop is held; the attempts it
  moved past are listed in order in the disposition's `(P route! :continued-from)`, each with
  its attempt, reason and retired transaction. Rev 24 (packet M23L): the loop is in the
  state graph as the cycle `coordinationHeld → transactionRetired → routeEnacted`, with the
  refusals `transactionRetireFailed`, `preparationRefused` and `bindingRefused` reached from
  it (`ContinuationRefusal`); the attempts moved past are `ContinuedAttempt`s on the
  observation, and when both writes persisted but the loop did not go on, the held result
  says why (`ContinuationOutcome`). -/
  | authorFailed
  /-- `(C coordinate :review-rejected)`. -/
  | reviewRejected
  /-- `(C coordinate :enact-failed)`. -/
  | enactFailed
  deriving DecidableEq, Repr

/-- `:refused` reasons of `(C coordinate)`. Those marked *no ledger* return a map
without `:ledger`, and today `store/persist-ledger!` refuses it, so `route!` reports
`:checkpoint-persist-failed` instead (row #66). -/
inductive CoordinatorRefusal where
  /-- `(C coordinate :coordinator/input-refused)`; no ledger. -/
  | inputRefused
  /-- `(C coordinate :coordinator/resume-state-refused)`; no ledger. -/
  | resumeStateRefused
  /-- `(C invoke-once :coordinator/port-receipt-refused)`; carries `:phase`, no ledger. -/
  | portReceiptRefused
  /-- `(C invoke-once :coordinator/port-threw)`; carries `:phase`, no ledger. -/
  | portThrew
  /-- `(C coordinate :coordinator/author-payload-refused)`; carries a ledger. -/
  | authorPayloadRefused
  /-- `(C coordinate :coordinator/review-patch-substitution)`; carries a ledger. -/
  | reviewPatchSubstitution
  /-- `(C coordinate :coordinator/enact-payload-refused)`; carries a ledger. -/
  | enactPayloadRefused
  /-- `(C coordinate-queued-retry :coordinator/retry-attribution-refused)`, `(C coordinate :coordinator/retry-attribution-refused)`; carries a ledger. -/
  | retryAttributionRefused
  /-- `(C append-transition! :coordinator/ledger-transition-refused)`; carries the ledger it refused. -/
  | ledgerTransitionRefused
  /-- `(C coordinate :coordinator/malformed)`; no ledger. -/
  | malformed
  deriving DecidableEq, Repr

/-- The two writes after a `:checkpoint` result
(`(P route! :meta-self-heal/checkpoint-persist-failed)`). -/
inductive PersistWrite where
  | ledgerWrite | transactionWrite
  deriving DecidableEq, Repr

/-- How a transaction closed after enactment: the final `coordinate` result's `:status`. -/
inductive ClosingStatus where
  /-- `:discharged`: the retry succeeded.
  Rev 14 anchor (futon2 `43bb57fc7`; C, T and L unchanged since `d0a890f22`): `(C coordinate :discharged)`,
  the arm `(= :succeeded (:status retry-receipt))`, after
  `append-transition!` of `:state :discharged`. -/
  | discharged
  /-- `:reopened` (via `ledger/append-retry-result`): the retry did not discharge.
  Rev 14 anchor (futon2 `43bb57fc7`; C, T and L unchanged since `d0a890f22`): `(C coordinate ledger/append-retry-result)`, the `:else`
  arm of the retry receipt. The status is computed, `(get-in reopened [:entry :state])`
  (`(C coordinate "get-in reopened")`), and is `:reopened` when `(L append-retry-result :reopened)` takes
  its second arm.
  Rev 21 (futon2 `4e7b31cdc`, F26): this is the enacted path only, with predecessor
  `:enacted` and the retry's reason. The author arm of `coordinate` also appends a
  `:reopened` (or `:abandoned`) ledger entry, with predecessor `:claimed` and
  `:reason :author-failed` (`HeldReason.authorFailed`), but `coordinate` returns `:held`
  there, so it does not produce this closing status. `(L allowed-predecessors :claimed)`
  lists `:reopened` and `:abandoned` from both `:enacted` and `:claimed`, and
  `(L state-defects :reopen/reason-unexpected)` refuses an `:author-failed` reopen from
  `:enacted`, so the two paths cannot be confused in a valid ledger.
  Rev 23 (F31): the author arm's `:reopened` entry is consumed by the same click, whose
  continuation (`(P route! run-attempt)`) retires the attempt-n transaction and authors
  attempt n+1. Rev 24: that is the edge `coordinationHeld → transactionRetired`. -/
  | reopened
  /-- `:abandoned`: the attempt after this one would exceed the budget.
  Rev 14 anchor (futon2 `43bb57fc7`; C, T and L unchanged since `d0a890f22`): `(C coordinate ledger/append-retry-result)`, the same
  computed status (`(C coordinate "get-in reopened")`), `:abandoned` when
  `(L append-retry-result :attempt-limit-exhausted)` takes its first arm. A second
  abandoned literal exists; it is `RetryNext.abandoned .retryBudgetSpent`, not
  this constructor: `(not C coordinate-queued-retry :retry-budget-spent)`.
  Rev 21: as for `reopened`, the author arm's `:abandoned :attempt-limit-exhausted` entry
  (predecessor `:claimed`, carrying `:port-receipt-pin`) is returned under `:held`, not as
  this closing status. Rev 23 (F31): that entry ends the click's continuation; the hold
  of that attempt is the click's disposition. -/
  | abandoned
  /-- `:awaiting-retry`: the retry port queued the retry click. The production
  retry port only persists and enqueues, so this is the closing status a production
  click is expected to reach. The M4a shape does not name it (finding).
  Rev 14 anchor (futon2 `43bb57fc7`; C, T and L unchanged since `d0a890f22`): `(C coordinate-queued-retry :awaiting-retry)`
  returned by `coordinate` through its `(= :queued (:status retry-receipt))`
  arm, when `ledger/pending-requeue` finds nothing. -/
  | awaitingRetry
  /-- Rev 8: the retry click ran but did not test the repair (`RetryClickOutcome.closing`).
  The injury is neither discharged nor reopened, and the transaction stays `:enacted`
  and active.
  Rev 14 anchor (futon2 `43bb57fc7`; C, T and L unchanged since `d0a890f22`): not a `coordinate` status. It is the retry
  click's `(T integrate :retry-inconclusive)` observation: the non-injury arm for every
  reason except a successful task outcome, `(not T classify :successful-task-outcome)`,
  and
  `(T append-other-injury-retry-observation :retry-inconclusive)`. -/
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

/-- Rev 24 (futon2 `16be63148`, F32): why the loop did not go on after an attempt held
`:author-failed` with both writes `:persisted`. P puts it on the held result as
`(P route! :continuation)`; it is beside the path, like `CoordinationOutcome`, and the click
ends at `coordinationHeld`. -/
inductive ContinuationOutcome where
  /-- The reload did not return `:loaded`:
  `(P route! :meta-self-heal/reload-unavailable)`, with the durable's status beside it. Any
  reopened entry waits for a later click. -/
  | reloadUnavailable
  /-- The injury is active but its entry is not `:reopened`:
  `(P route! :entry-not-reopened)`, status `:not-continued`, with the entry. -/
  | entryNotReopened
  /-- The injury is no longer active, for instance its last entry is `:abandoned` with
  `(L append-retry-result :attempt-limit-exhausted)`: `(P route! :injury-not-active)`,
  status `:not-continued`, with that last entry. -/
  | injuryNotActive
  deriving DecidableEq, Repr

/-- Rev 24 (F31/F32): one attempt the click moved past, an entry of
`(P route! :continued-from)`: its attempt, its reason (always `:author-failed` today, the
only reason the loop continues on), and whether its transaction was retired (`false` is a
refused retirement, whose status and reason the entry keeps). A list of these is data
beside the path, not a state. -/
structure ContinuedAttempt where
  attempt : Nat
  reason : HeldReason
  retired : Bool
  deriving DecidableEq, Repr

/-- Rev 24: the refusals the continuation can end in, each placed at its state. All three
carry `(P route! :continued-from)` since futon2 `16be63148`. -/
inductive ContinuationRefusal where
  /-- `(P retire-stale-transaction! :meta-self-heal/transaction-retire-failed)` in the
  continuation. -/
  | transactionRetireFailed
  /-- `coordinator/prepare` gave no transaction for attempt n+1:
  `(P route! :meta-self-heal/preparation-refused)`, keeping the coordinator's result under
  `:prepare`: `(C prepare :coordinator/preparation-refused)` with its defects, or
  `(C prepare :coordinator/preparation-malformed)`. -/
  | preparationRefused
  /-- A re-run binding was not valid, returned through `(P route! "if-not (= :valid (:status next-binding))")`;
  the reasons are those of `bindingRefused`:
  `(P diagnosis-transaction-binding :meta-self-heal/diagnosis-transaction-mismatch)`,
  `(P acceptance-transaction-binding :meta-self-heal/acceptance-transaction-mismatch)`,
  `(P acceptance-transaction-binding :meta-self-heal/acceptance-transaction-unadmitted)`. -/
  | bindingRefused
  deriving DecidableEq, Repr

/-- The placement law for the continuation's refusals. -/
def ContinuationRefusal.state : ContinuationRefusal → RouteState
  | .transactionRetireFailed => RouteState.transactionRetireFailed
  | .preparationRefused => RouteState.preparationRefused
  | .bindingRefused => RouteState.bindingRefused

/-- Each continuation refusal is a step out of the cycle and ends the click. -/
theorem continuationRefusals_placed (r : ContinuationRefusal) :
    (edge coordinationHeld r.state || edge transactionRetired r.state) = true ∧
      edge r.state terminalRecord = true ∧ reaches r.state enacted = false := by
  cases r <;> decide

/-- A coordination result as a route check reports it, after M4a: its state, the loop
phase (`:phase`), and the outcome. Rev 24 adds the continuation's two fields.
-/
structure CoordinationObservation where
  state : RouteState
  phase : CoordinationPhase
  outcome : CoordinationOutcome
  /-- Rev 24: `(P route! :continuation)`, when the loop stopped after a persisted
  author failure. -/
  continuation : Option ContinuationOutcome := none
  /-- Rev 24: `(P route! :continued-from)`, the attempts the click moved past, in order. -/
  continuedFrom : List ContinuedAttempt := []
  deriving DecidableEq, Repr

/-- Rev 24: a `:continuation` appears only on an `:author-failed` hold. -/
def CoordinationObservation.continuationPlaced (o : CoordinationObservation) : Bool :=
  match o.continuation with
  | none => true
  | some _ => decide (o.outcome = .held .authorFailed)

/-- An observation obeys the placement law. -/
def CoordinationObservation.placed (o : CoordinationObservation) : Bool :=
  stateEq o.outcome.state o.state

/-- Every new state ends the route. -/
theorem coordinationStates_terminate :
    reaches coordinationHeld terminalRecord = true ∧
      reaches coordinationRefused terminalRecord = true ∧
      reaches persistRefused terminalRecord = true := by decide

/-- A held, refused or persist-failed transaction never goes on to enactment or to
ordinary work (order error 4: true of the runtime only after M4a).
Rev 24 (F31, packet M23L): restated. A held attempt now reaches enactment through the
continuation (`coordinationHeld → transactionRetired → routeEnacted → enacted`), so the
conjunct `reaches coordinationHeld enacted = false` of rev 5 to rev 23 is false of the
table and is replaced by `heldReachesEnactment_onlyByRetirement`. The other five
conjuncts are unchanged. -/
theorem coordinationStops_beforeEnactment :
    reaches coordinationRefused enacted = false ∧
      reaches persistRefused enacted = false ∧
      reaches coordinationHeld ordinarySelection = false ∧
      reaches coordinationRefused ordinarySelection = false ∧
      reaches persistRefused ordinarySelection = false := by decide

/-- Rev 24: out of `coordinationHeld` there are exactly three steps: the click's end, the
continuation's retirement, and its refusal. A held attempt goes on to enactment only by
retiring its transaction first, and a refused retirement goes on to neither. -/
theorem heldReachesEnactment_onlyByRetirement :
    allStates.filter (edge coordinationHeld) =
        [transactionRetired, transactionRetireFailed, terminalRecord] ∧
      reaches coordinationHeld enacted = true ∧
      reaches transactionRetireFailed enacted = false ∧
      reaches transactionRetireFailed ordinarySelection = false := by decide

/-- Rev 24: the continuation is a cycle in the table. -/
theorem continuation_isCycle :
    conforms [coordinationHeld, transactionRetired, routeEnacted, coordinationHeld] = true ∧
      reaches coordinationHeld terminalRecord = true := by decide

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
(`(P route! :meta-self-heal/checkpoint-persist-failed)`). -/
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
* `ledgerRead → activeSetUnavailable`: `(P prepare-diagnosis :meta-self-heal/diagnosis-active-set-unavailable)`;
* `→ acceptanceUnavailable`: `(P prepare-acceptance :else)`;
* `→ readinessReady`: `production-readiness` `:else` with `:active-injury? false`
  (`(P production-readiness :active-injury?)`), since `(seq (:injuries active))` is nil and no port term is required;
* `→ ordinarySelection`: `route!` reads again and returns nil (`(P route! :durable-ledger)`), and
  `(or routed (run-ordinary-opportunity! …))` runs ordinary work (`(R run-opportunity! "or routed")`).

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

/-- The four fields `attributable-retry-readiness` compares (`(P attributable-retry-readiness "select-keys enacted")`): the supplied
retry against the last `:enacted` entry, and the patch sha against its `:authored`
entry. -/
inductive RetryField where
  | injuryId | repairId | retryClick | patchSha
  deriving DecidableEq, Repr

/-- Why the attribution refused (`(P attributable-retry-readiness :meta-self-heal/retry-attribution-refused)`). Every constructor is placed at
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

/-- What `(T classify)` says of the retry click's terminal record, as `(T integrate)`
receives it. -/
inductive RetryClickOutcome where
  /-- `:successful-task-outcome`: no failure kind, and an outcome in
  `(T successful-outcomes)`. The only outcome that tests the repair and passes.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T classify :successful-task-outcome)`, the `non-injury-reason` arm for a nil
  failure kind and an outcome in `successful-outcomes`; `integrate` then appends
  `(T integrate :discharged)` for the enacted entry. -/
  | successfulTaskOutcome
  /-- `:injury` with the enacted entry's injury id: `(L append-retry-result)`.
  The retry failed for the same cause.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T integrate ledger/append-retry-result)`, the arm
  `(= :enacted (:state previous))` with `(= (:retry-click previous) (:click-id classification))`;
  the transition is the computed `(get-in appended [:entry :state])`, so there is no
  keyword literal. -/
  | sameInjury
  /-- `:injury` with a different injury id, and the record is ingested. Cited at futon2
  `b5dd9269c` (M10b-4). `integrate` binds `other-injury-retry?` (`(T integrate "other-injury-retry?")`). If the
  different id is unknown, it opens a new injury (`(T integrate "nil? previous")`). If it is active, it appends
  a `:repeated-active-injury` observation (`(T integrate :repeated-active-injury)`). Either way it then appends the
  attributed `:retry-inconclusive` observation for the enacted entry through
  `(T append-other-injury-retry-observation)`. The enacted entry's state is
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
  this click is not its retry click (`:injury/retry-click-mismatch`), or when
  the different id is terminal (`:injury/terminal-history-requires-new-transaction`).
  `integrate` returns `{:status :refused}` with no ledger, so no observation is
  written and the pin stays un-ingested. It is a separate constructor, not an
  unobserved `otherInjury`, because the coordinator receives a refusal rather than an
  ingested record without an observation. Under the law it is still inconclusive for the
  enacted injury.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T integrate :injury/retry-click-mismatch)`,
  `(T integrate :injury/terminal-history-requires-new-transaction)`. -/
  | otherInjuryRefused
  /-- `:ordinary-selection-abstention`: an abstention.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T abstention-reason :ordinary-selection-abstention)`, the `:else`
  arm, reached from `classify` when the failure kind is `:abstained` and the route is
  configured. The `{:abstained :ordinary-selection-abstention}` entry of
  `explicit-non-injury-kinds` is never read for it: `classify` takes the `:abstained`
  branch first. -/
  | ordinarySelectionAbstention
  /-- `:evaluated-no-action` (`(T evaluated-no-action?)`): scored, and no action chosen.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T abstention-reason :evaluated-no-action)`, guarded by
  `evaluated-no-action?` (`:policy-nondiscrimination` among the causes). -/
  | evaluatedNoAction
  /-- `:partial-frontier-continuation` (`(T partial-frontier-continuation?)`).
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T abstention-reason :partial-frontier-continuation)`, guarded by
  `partial-frontier-continuation?`. -/
  | partialFrontierContinuation
  /-- `:operator-cancelled`.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T explicit-non-injury-kinds :operator-cancelled)`, read in
  `classify`'s `non-injury-reason`. -/
  | operatorCancelled
  /-- `:declared-no-work`.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T explicit-non-injury-kinds :declared-no-work)`, read in
  `classify`'s `non-injury-reason`. -/
  | declaredNoWork
  /-- `:diagnostic-only`.
  Rev 13 anchor (futon2 `9d3026e1a`, T unchanged since `d0a890f22`): `(T explicit-non-injury-kinds :diagnostic-only)`, read in
  `classify`'s `non-injury-reason`. -/
  | diagnosticOnly
  /-- `:absent-terminal-failure`: no failure kind and no outcome.
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
or is abandoned when the next attempt would exceed `:attempt-limit` (`(L append-retry-result :attempt-limit-exhausted)`; this is
the `budgetSpent` parameter). Everything else is inconclusive for the enacted injury. -/
def RetryClickOutcome.closing (budgetSpent : Bool) : RetryClickOutcome → ClosingStatus
  | .successfulTaskOutcome => .discharged
  | .sameInjury => if budgetSpent then .abandoned else .reopened
  | _ => .retryInconclusive

/-- `integrate` before futon2 `83f72ba1e` (M10a), at `343b60ef3`. Kept as the record of
the disagreement that M10a removed. Every `:non-injury` classification of the retry click
appended `:discharged :outcome :success` (`(T integrate :discharged)` at `343b60ef3`). The same injury went
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

/-- **The reason M10a existed.** `integrate` at `343b60ef3` (`(T integrate)`), given `classify`'s
abstention (`(T classify)`, `(T abstention-reason)`), recorded an abstained retry as `:discharged`; the law
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
* on the retry click, `:successful-task-outcome` appends `:discharged` (`(T integrate :discharged)`);
* every other `:non-injury-reason` on the retry click appends an observation
  `:retry-inconclusive` and leaves the entry `:enacted` (`(T integrate :retry-inconclusive)`);
* the same injury calls `append-retry-result` (`(T integrate ledger/append-retry-result)`), giving
  `:reopened`, or `:abandoned` past `:attempt-limit` (`(L append-retry-result :attempt-limit-exhausted)`);
* another injury does not touch the enacted entry (`(T integrate "other-injury-retry?")`);
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
  /-- `:attempt-limit-exhausted`: the next authoring would exceed `:attempt-limit`.
  Rev 15 anchor (futon2 `5a066d9ab`; C and L unchanged since `aa3ec313b`): `(L append-retry-result :attempt-limit-exhausted)`
  reached through
  `(C coordinate ledger/append-retry-result)`. `validate-ledger`'s abandonment check
  (`(L state-defects :attempt-limit-exhausted)`) accepts it only at `attempt = limit`. -/
  | attemptLimitExhausted
  /-- Rev 9 (new, M10b): the re-queue budget for inconclusive retries is spent. A re-queue
  authors nothing, so it does not count against `:attempt-limit`.
  Rev 15 anchor (futon2 `5a066d9ab`; C and L unchanged since `aa3ec313b`): `(L append-requeue :retry-budget-spent)`, the
  arm where the entry's requeue count has reached the ledger's retry limit (`(L append-requeue :retry-limit)`), with
  the attempt carried over unchanged. `(C coordinate-queued-retry :retry-budget-spent)`
  returns it, after reading the appended entry's state (`(C coordinate-queued-retry :abandoned)`), before any
  retry port call. `validate-ledger` accepts it only when the requeue count equals the
  retry limit (`(L state-defects :retry-budget-spent)`). -/
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
  Rev 15 anchor (futon2 `5a066d9ab`; C and L unchanged since `aa3ec313b`): `(C coordinate-queued-retry ledger/append-requeue)`,
  on the arm where `(C coordinate-queued-retry ledger/pending-requeue)` finds the attributed
  observation, and then `(L append-requeue :enacted)`, a new enacted entry with a
  new retry click. The entry's fields: `attempt` is the ledger's attempt, copied from the
  previous entry (`(L append-requeue :attempt)`); `requeues` is the ledger's requeue count, read
  and written incremented (`(L append-requeue "inc requeues")`). On the `recur`, C reads that count back (`(C coordinate-queued-retry :requeues)`)
  and, being positive, calls the retry port with the requeue ordinal (`(C coordinate-queued-retry "requeue-phase")`). The
  queued click then ends the same way as `awaitingNothingQueued`: the new entry has no
  observation yet, so `coordinate` returns the awaiting-retry status. In the code the
  two constructors differ by the appended entry and the port call, not by the status. -/
  | queued (entry : RetryEntry)
  /-- The transaction ends `:awaiting-retry`, and nothing is queued.
  Rev 15 anchor (futon2 `5a066d9ab`; C and L unchanged since `aa3ec313b`): `(C coordinate-queued-retry :awaiting-retry)`
  is the arm where `(C coordinate-queued-retry ledger/pending-requeue)` returns nil. -/
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
`:enacted`. The next click resumed `transaction.edn` (`(P route! "load-transaction")`). `coordinate` reaches the retry phase, `invoke-once` finds
the recorded `:queued` receipt and returns it without calling the port (`(C invoke-once)`). The
`:queued` branch then ends `:awaiting-retry` (`(C coordinate :queued)`), and no child is queued. -/
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
names the enacted entry's click. That observation is what `(L pending-requeue)`
detects. The no-work branch of `integrate` writes it (`(T integrate :retry-inconclusive)` at `493388b7b`). Since
rev 11 (futon2 `b5dd9269c`, M10b-4), the ingested different-cause arms also write it,
through `(T append-other-injury-retry-observation)`, from `(T integrate "nil? previous")` and `(T integrate ledger/active-states)`. The
refused arms (`(T integrate :injury/retry-click-mismatch :injury/terminal-history-requires-new-transaction)`) write none, and a missing record reaches `integrate`
not at all. -/
def RetryClickOutcome.observedInconclusive : RetryClickOutcome → Bool
  | .otherInjuryRefused => false
  | .recordUnreadable => false
  | _ => true

/-- The next step today (futon2 `aa3ec313b`, wired by futon3c `7efc13bd8` and futon2
`493388b7b`). The `:queued` branch of the retry phase enters `coordinate-queued-retry`
(`(C coordinate "coordinate-queued-retry")`). When `(C coordinate-queued-retry ledger/pending-requeue)` finds the observation, it mints
`(retry-click-id repair-id attempt (inc n))` (`(C coordinate-queued-retry :retry-click-id)`, `(A retry-click-id)`) and calls
`(C coordinate-queued-retry ledger/append-requeue)`. With `requeues >= retry-limit` (`(L append-requeue :retry-limit)`) that appends `:abandoned
:retry-budget-spent` (`(L append-requeue :retry-budget-spent)`), and the coordinator returns with no port call (`(C coordinate-queued-retry :retry-budget-spent)`).
Otherwise it appends a new enacted-stage entry with the same `:attempt` and
`:requeues (inc requeues)` (`(L append-requeue "inc requeues")`), and the recur queues the new click (`(C coordinate-queued-retry "recur")`). With
no observation it ends `:awaiting-retry` and queues nothing (`(C coordinate-queued-retry :awaiting-retry)`). The other
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
record, or whose different-cause record was refused (`(T integrate :injury/retry-click-mismatch :injury/terminal-history-requires-new-transaction)` at
`b5dd9269c`), is inconclusive under the law, which queues a fresh retry. Today no
`:retry-inconclusive` observation is written for it, so `pending-requeue` is nil
(`(L pending-requeue)`) and the coordinator ends `:awaiting-retry` with nothing queued (`(C coordinate-queued-retry :awaiting-retry)`).
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

/-! ## Rev 24: the continuation's bound, and the carried bindings -/

/-- A path that carries an attempt number at each state. `List RouteState` cannot express
the bound on the continuation: the cycle through `transactionRetired` is a table cycle, and
what stops it is the ledger's attempt count, which is data. -/
abbrev AttemptPath := List (RouteState × Nat)

/-- The attempts at which a path enters `transactionRetired`: the reopened entry's attempt
n+1 that the pass goes on to author. -/
def AttemptPath.retiredAttempts (p : AttemptPath) : List Nat :=
  (p.filter fun v => stateEq v.1 transactionRetired).map Prod.snd

/-- What the ledger guarantees of the continuation's passes, given the attempt `attempt0`
the click first authored and the ledger's `:attempt-limit`. Each pass needs the injury's
active entry `:reopened` at the attempt after the one just authored, so the attempts
strictly increase and each is above `attempt0`; and `(L append-retry-result :attempt-limit-exhausted)`
appends `:abandoned` instead of `:reopened` when that attempt would exceed the limit, which
the loop leaves as `ContinuationOutcome.injuryNotActive`, so no pass enters above it. -/
structure AttemptPath.ledgerBounded (attemptLimit attempt0 : Nat) (p : AttemptPath) : Prop where
  increasing : p.retiredAttempts.Pairwise (· < ·)
  above : ∀ a ∈ p.retiredAttempts, attempt0 < a
  within : ∀ a ∈ p.retiredAttempts, a ≤ attemptLimit

/-- A strictly increasing list of naturals inside `(lo, hi]` has at most `hi - lo` entries. -/
theorem length_le_of_pairwise_lt_Ioc :
    ∀ (l : List Nat) (lo hi : Nat), l.Pairwise (· < ·) → (∀ a ∈ l, lo < a) →
      (∀ a ∈ l, a ≤ hi) → l.length ≤ hi - lo
  | [], _, _, _, _, _ => Nat.zero_le _
  | a :: rest, lo, hi, hpair, habove, hwithin => by
      rw [List.pairwise_cons] at hpair
      have hlo : lo < a := habove a (List.mem_cons_self ..)
      have hhi : a ≤ hi := hwithin a (List.mem_cons_self ..)
      have ih := length_le_of_pairwise_lt_Ioc rest a hi hpair.2 hpair.1
        (fun b hb => hwithin b (List.mem_cons_of_mem _ hb))
      simp only [List.length_cons]
      omega

/-- **The bound.** A click whose passes obey the ledger visits `transactionRetired` at most
`attemptLimit - attempt0` times, however the table's cycle is unrolled. -/
theorem retiredVisits_le_attemptBudget (attemptLimit attempt0 : Nat) (p : AttemptPath)
    (h : p.ledgerBounded attemptLimit attempt0) :
    (p.filter fun v => stateEq v.1 transactionRetired).length ≤ attemptLimit - attempt0 := by
  have hlen : (p.filter fun v => stateEq v.1 transactionRetired).length =
      p.retiredAttempts.length := by
    simp [AttemptPath.retiredAttempts]
  rw [hlen]
  exact length_le_of_pairwise_lt_Ioc _ _ _ h.increasing h.above h.within

/-- The hypothesis is not vacuous: a fourth attempt under `:attempt-limit 3`, and a
repeated attempt, are each refused by it. -/
theorem ledgerBounded_refusesOverrun :
    ¬ AttemptPath.ledgerBounded 3 2 [(transactionRetired, 3), (transactionRetired, 4)] ∧
      ¬ AttemptPath.ledgerBounded 3 1 [(transactionRetired, 3), (transactionRetired, 3)] := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.within 4 (by decide)
    omega
  · have := h.increasing
    revert this
    decide

/-- Click 10, `wm-click-dfc7501c` (2026-10-20 17:03:02-17:04:02Z), from readiness on.
Attempt 1's resumed transaction was retired before the first prepare
(`data/wm-meta-injuries/transaction.edn.attempt-1.retired.edn`, futon2), attempt 2 was
authored and held `:author-failed`, the continuation retired it
(`transaction.edn.attempt-2.retired.edn`) and authored attempt 3, which was held; the
ledger then has `:abandoned :attempt-limit-exhausted` at attempt 3 under
`:attempt-limit 3`, and the loop's exit is `injuryNotActive`. The click record lacks
`:continued-from` and `:continuation` (futon3c `runner_service.clj` keeps only selected
keys, F34), so the observation below is taken from P's result shape and the ledger, not
from the record. The prefix before readiness is not established here. -/
def click10AttemptSuffix : AttemptPath :=
  [ (readinessReady, 2), (routeEnacted, 2), (coordinationHeld, 2), (transactionRetired, 3),
    (routeEnacted, 3), (coordinationHeld, 3), (terminalRecord, 3) ]

def click10Observation : CoordinationObservation :=
  { state := coordinationHeld, phase := .author, outcome := .held .authorFailed,
    continuation := some .injuryNotActive,
    continuedFrom := [{ attempt := 2, reason := .authorFailed, retired := true }] }

theorem click10_conforms :
    conformsSuffix (click10AttemptSuffix.map Prod.fst) = true ∧
      click10Observation.placed = true ∧ click10Observation.continuationPlaced = true ∧
      click10AttemptSuffix.retiredAttempts = [3] := by decide

theorem click10_ledgerBounded : click10AttemptSuffix.ledgerBounded 3 2 := by
  refine ⟨by decide, ?_, ?_⟩ <;> intro a ha <;>
    simp [click10AttemptSuffix, AttemptPath.retiredAttempts, stateEq] at ha <;> omega

/-- Click 10 used its whole budget: one pass, `3 - 2`. -/
theorem click10_usedBudget :
    (click10AttemptSuffix.filter fun v => stateEq v.1 transactionRetired).length = 3 - 2 := by
  decide

/-- What `(R run-opportunity!)` observes of the bindings carried by a resumed transaction,
`(P carried-bindings-observation)`, before diagnosis. Rev 24 (F32). -/
inductive CarriedBindings where
  /-- `(P carried-bindings-observation :carried-transaction)`: the transaction's work order
  names an active injury; its pins fill the options the caller did not supply. The map has
  no `:status`, so it is no site; the call is
  `(R run-opportunity! meta-self-heal/carried-bindings-observation)`. -/
  | carriedTransaction
  /-- `(P carried-bindings-observation {:status :absent :reason :no-active-injury})`. -/
  | noActiveInjury
  /-- `(P carried-bindings-observation {:status :absent :reason :transaction-injury-not-active})`. -/
  | transactionInjuryNotActive
  /-- `(P carried-bindings-observation {:status :absent :reason :no-transaction})`. -/
  | noTransaction
  /-- A retry click reads no context and carries nothing:
  `(R run-opportunity! {:status :absent :reason :retry})`. Not `CoordinationPhase.retry`. -/
  | retryClick
  deriving DecidableEq, Repr

/-! ## Rev 25: the ledger's table, and the next click predicted before it runs

Rev 25 (claude-5, 2026-10-20 19:30Z) is written before the click it describes, on Joe's word
that evening: the model predicts the click, and the click either matches or yields one
finding. Nothing in this section is transcribed from a click record. It is read from the code
at futon2 `38419663c` and futon3c `1fdd28a3f`, and from the three packets dispatched at
19:25Z: F35 (`(L allowed-predecessors :abandoned)`, `(L state-defects :reopen/correction-evidence)`,
`(L effective-attempt-limit)`), F36 (the reviewer answer contract in `(A agency-invoke!)`),
and F37 (`(A enact! :patch-not-on-canonical-branch)`, `(A enact! :reload-receipts)`). The five
anchors in that list that do not resolve against the code at those shas are the prediction's
claim on the code; they resolve when the packets land. Three of the theorems below say why
those packets exist: each is a place where the never-exercised stretch from review to enact
would have refused a correct repair, found by reading the code against the path this section
predicts. -/

/-- The injury ledger's states, `(L states)`. `:open` is `opened` here because `open` is a
Lean keyword. -/
inductive LedgerState where
  | opened | claimed | authored | reviewed | enacted | discharged | reopened | abandoned
  deriving DecidableEq, Repr

/-- `(L allowed-predecessors)` as F35 leaves it, written as (predecessor, state) pairs. The
one pair F35 adds is `(abandoned, reopened)`: a reopen whose predecessor is `:abandoned` is a
corrected reopen, admitted only with `:reason :port-refusal-corrected`, the sha of the port
fix as `:correction-commit`, and the refused receipts' pins as `:corrected-port-receipt-pins`
(`(L state-defects :reopen/correction-evidence)`). -/
def ledgerTransitions : List (LedgerState × LedgerState) :=
  [ (.opened, .claimed), (.reopened, .claimed),
    (.claimed, .authored),
    (.authored, .reviewed),
    (.reviewed, .enacted), (.enacted, .enacted),
    (.enacted, .discharged),
    (.enacted, .reopened), (.claimed, .reopened),
    (.abandoned, .reopened),
    (.enacted, .abandoned), (.claimed, .abandoned) ]

/-- The same table before F35, at futon2 `38419663c`. -/
def ledgerTransitionsBeforeF35 : List (LedgerState × LedgerState) :=
  ledgerTransitions.filter fun p =>
    !(decide (p = (LedgerState.abandoned, LedgerState.reopened)))

/-- Adjacent pairs of a ledger path are edges of the given table. -/
def ledgerConformsIn (table : List (LedgerState × LedgerState)) : List LedgerState → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
      table.any (fun p => decide (p = (a, b))) && ledgerConformsIn table (b :: rest)

/-- Conformance to the table as F35 leaves it. -/
def ledgerConforms : List LedgerState → Bool := ledgerConformsIn ledgerTransitions

/-- Before F35 nothing follows `:abandoned`: `(L terminal-states)` by state, and no row of
`(L allowed-predecessors)` names it. That is why injury `d755c886`, abandoned on two port
refusals of a correct answer, could not be picked up again. -/
theorem abandoned_terminalBeforeF35 :
    ledgerTransitionsBeforeF35.all (fun p => !(decide (p.1 = LedgerState.abandoned))) = true := by
  decide

/-- The one entry F35 writes by hand to the live ledger, after the fix is reviewed. -/
def f35LedgerWrite : List LedgerState := [.reopened]

/-- What the predicted self-heal click writes: the claim at attempt 4, then one entry per
port phase (`(C coordinate)`: `:authored`, `:reviewed`, `:enacted`). -/
def click11LedgerWrites : List LedgerState := [.claimed, .authored, .reviewed, .enacted]

/-- What the retry child writes when the ordinary click it runs closes successfully:
`(T integrate :discharged)`. -/
def click11RetryLedgerWrites : List LedgerState := [.discharged]

/-- Injury `d755c886`'s ledger path from its ordinal 11 (`:abandoned`, attempt 3) to
discharge, and who writes each part. -/
def d755c886PredictedLedgerPath : List LedgerState :=
  [.abandoned] ++ f35LedgerWrite ++ click11LedgerWrites ++ click11RetryLedgerWrites

theorem d755c886_ledgerPathConforms :
    ledgerConforms d755c886PredictedLedgerPath = true ∧
      d755c886PredictedLedgerPath =
        [.abandoned, .reopened, .claimed, .authored, .reviewed, .enacted, .discharged] := by
  decide

/-- Without F35 the same path is not a ledger path: its first step is the missing edge. -/
theorem d755c886_ledgerPathNeedsF35 :
    ledgerConformsIn ledgerTransitionsBeforeF35 d755c886PredictedLedgerPath = false ∧
      ledgerConformsIn ledgerTransitionsBeforeF35 d755c886PredictedLedgerPath.tail = true := by
  decide

/-- F35: the attempt budget after corrected reopens, `(L effective-attempt-limit)`: the
ledger's `:attempt-limit` plus the number of refused receipts each corrected reopen names.
`(L append-retry-result :attempt-limit-exhausted)` and `(L state-defects :abandonment/not-exhausted)`
read this value, so a later author failure at attempt 4 reopens at 5 and one at 5 abandons at
5, and `:attempt/changed-outside-reopen` is never provoked by an abandonment written below the
attempt it follows (the shape the unmodified `append-retry-result` would have produced). -/
def effectiveAttemptLimit (attemptLimit : Nat) (correctedReceipts : List Nat) : Nat :=
  attemptLimit + correctedReceipts.sum

/-- Injury `d755c886`: limit 3, one correction naming the two refused receipts (ordinals 9 and
11 of the live ledger), so attempts 4 and 5 remain. The predicted click uses attempt 4. -/
theorem d755c886_attemptBudget :
    effectiveAttemptLimit 3 [2] = 5 ∧ effectiveAttemptLimit 3 [] = 3 := by decide

/-- `(C verify-work-order :attempt/exceeds-limit)`: the work order's attempt must not exceed
the limit the order carries. -/
def workOrderAdmitsAttempt (attempt limit : Nat) : Bool := attempt ≤ limit

/-- **Why F38 exists** (rev 25a, found by codex-1's answer to the F35 packet's question, not by
a click). `(C prepare)` copied the ledger's raw `:attempt-limit` onto the work order, so the
corrected injury's attempt 4 was refused at prepare (`preparationRefused`, before any port) and
the predicted path could not leave `readinessReady`. F38 puts `(L effective-attempt-limit)` on
the order. -/
theorem d755c886_prepareNeedsF38 :
    workOrderAdmitsAttempt 4 3 = false ∧
      workOrderAdmitsAttempt 4 (effectiveAttemptLimit 3 [2]) = true := by decide

/-- **The predicted self-heal click**, `(S click!)` on injury `d755c886` after F35, F36 and
F37 are reviewed and reloaded. From the ledger read: the active set is the corrected
`:reopened` at attempt 4; diagnosis and acceptance are supplied from the carried attempt-3
work order (`(P carried-bindings-observation :carried-transaction)`, F32), so admission
accepts without a seat; readiness is ready; `route!` retires the held attempt-3 transaction
at resume time (`(P retire-stale-transaction!)`; data on the result, not a state) and
prepares attempt 4; the bindings are valid; `coordinate` claims, authors on zai-2 (whose
answer the F33 port now reads), reviews on zai-3 under the F36 contract, enacts through
`(A enact!)` under F37 with the repair an ancestor of futon2 main's HEAD, and the retry port
only queues (`(C coordinate-queued-retry :awaiting-retry)`), so the click closes
`:awaiting-retry` and ends. No continuation pass: the author succeeds at the first attempt
of the click. -/
def click11PredictedPath : List RouteState :=
  [ ledgerRead, activeInjury, diagnosisPrepared, admissionRun, reviewAccepted,
    readinessReady, routeEnacted, enacted, terminalRecord ]

/-- The same path with its attempt, for the rev 24 bound. -/
def click11PredictedAttemptPath : AttemptPath :=
  click11PredictedPath.map fun s => (s, 4)

/-- The predicted coordination result: closed `:awaiting-retry`, phase `:final` (the
coordinator's awaiting-retry map carries no `:phase`, so `(P route! settle)` keeps the
loop's), no continuation. -/
def click11PredictedObservation : CoordinationObservation :=
  { state := enacted, phase := .final, outcome := .closed .awaitingRetry }

theorem click11_predictedConforms :
    conformsPath click11PredictedPath = true ∧
      click11PredictedObservation.placed = true ∧
      click11PredictedObservation.continuationPlaced = true ∧
      click11PredictedAttemptPath.retiredAttempts = [] := by
  decide

/-- **The predicted retry child**, launched by `(S close-click! :meta-repair-retry)` after the
parent's release, not charged to the ordinary click budget (its options drop
`:ordinary-click/issue!`). `(P attributable-retry-readiness)` admits it from the enacted
entry; it runs ordinary work; its terminal record is ingested by
`(T classify :successful-task-outcome)` and `(T integrate :discharged)` appends the discharge. -/
def click11RetryPredictedPath : List RouteState :=
  [ retryClick, retryReady, ordinarySelection, terminalRecord ]

theorem click11Retry_predictedConforms : conformsPath click11RetryPredictedPath = true := by
  decide

/-- The retry child's predicted close: a successful task outcome discharges the injury at
attempt 4 with no re-queue; the named alternative is an ordinary abstention, which re-queues
one child (requeue 1 of 3) and discharges nothing. -/
theorem click11Retry_predictedClose :
    RetryClickOutcome.successfulTaskOutcome.nextToday false false ⟨4, 0⟩ = .discharged ∧
      RetryClickOutcome.ordinarySelectionAbstention.nextToday false false ⟨4, 0⟩ =
        .queued ⟨4, 1⟩ := by
  decide

/-- The close outcomes an ordinary click can record without a failure kind
(`outcome-kinds` in futon2 `full_loop_cohort.clj`, the non-failure members). -/
inductive OrdinaryClose where
  | groundedChange | groundedProgress | alreadySatisfied | groundedNoChange | artifactOnly
  | abstained | noSelection
  deriving DecidableEq, Repr

/-- Which of them `(T classify :successful-task-outcome)` counts as success:
`(T successful-outcomes)` is `#{:success :closed :grounded-change :cohort-complete}`, and
of the ordinary closes only `:grounded-change` is in it. -/
def OrdinaryClose.successfulForT : OrdinaryClose → Bool
  | .groundedChange => true
  | _ => false

/-- **Predicted hazard, not fixed before the click.** A retry child that closes
`:grounded-progress`, `:already-satisfied`, `:grounded-no-change` or `:artifact-only` with no
failure kind is not a successful task outcome for `(T classify)`; with a nil failure kind and
a present outcome it takes the injury branch with a nil cause key, so the retry is ingested as
a different injury (`RetryClickOutcome.otherInjury`), the enacted entry gets a
`:retry-inconclusive` observation, and a child is re-queued. If the click ends there, that is
the finding, and the repair is to `(T successful-outcomes)`. -/
theorem retryClose_onlyGroundedChangeDischarges (o : OrdinaryClose) :
    o.successfulForT = true ↔ o = .groundedChange := by
  cases o <;> decide

/-- What `(L state-defects :review/evidence)` and `(C coordinate :coordinator/review-patch-substitution)`
read of a review answer: `:status :succeeded`, the payload's `:patch-sha` equal to the author's,
and a sha-shaped `:reviewer-sha`. -/
structure ReviewAnswer where
  succeeded : Bool
  patchShaMatchesAuthor : Bool
  reviewerShaIsSha : Bool
  deriving DecidableEq, Repr

/-- A review answer reaches enactment only through all three. -/
def ReviewAnswer.reachesEnact (a : ReviewAnswer) : Bool :=
  a.succeeded && a.patchShaMatchesAuthor && a.reviewerShaIsSha

/-- **Why F36 exists.** Before it, the review prompt in `(A agency-invoke!)` stated no answer
shape (only the author phase had a contract, F25), so nothing told the seat to return
`:patch-sha` and `:reviewer-sha`; an answer missing either is refused at the ledger or by the
coordinator, never at the port. F36 puts the three requirements in the prompt. -/
theorem reviewAnswer_needsAllThree (a : ReviewAnswer) :
    a.reachesEnact = true ↔ a = { succeeded := true, patchShaMatchesAuthor := true,
                                  reviewerShaIsSha := true } := by
  cases a with
  | mk s p r => cases s <;> cases p <;> cases r <;> decide

/-- What `(L state-defects :enactment/evidence)` reads of an `:enacted` entry: which of
`:reload-receipt` (a single pin) and `:integration-commit` (a sha) it carries. -/
structure EnactEvidence where
  reloadReceipt : Bool
  integrationCommit : Bool
  deriving DecidableEq, Repr

/-- The ledger admits exactly one of the two. -/
def EnactEvidence.admitted (e : EnactEvidence) : Bool :=
  e.reloadReceipt != e.integrationCommit

/-- `(A enact!)` before F37 answers with both keys, and `(C coordinate)` copies both onto the
entry, so a valid ledger refuses the enactment (`:coordinator/ledger-transition-refused`). -/
def enactPayloadBeforeF37 : EnactEvidence := { reloadReceipt := true, integrationCommit := true }

/-- After F37 the reload records travel on the sealed port receipt as `:reload-receipts` and
the entry carries the integration commit alone. -/
def enactPayloadF37 : EnactEvidence := { reloadReceipt := false, integrationCommit := true }

/-- **Why F37 exists (1).** -/
theorem enactEvidence_beforeF37Refused :
    enactPayloadBeforeF37.admitted = false ∧ enactPayloadF37.admitted = true := by decide

/-- Where the reviewed patch sits relative to the canonical branch's HEAD. -/
structure PatchPlacement where
  onBranch : Bool
  commitsAfter : Nat
  deriving DecidableEq, Repr

/-- `(A enact!)` before F37: the patch must be HEAD itself. -/
def PatchPlacement.integratedBeforeF37 (p : PatchPlacement) : Bool :=
  p.onBranch && p.commitsAfter == 0

/-- `(A enact!)` under F37: the patch must be an ancestor of HEAD
(`git merge-base --is-ancestor`), else `:patch-not-on-canonical-branch`. -/
def PatchPlacement.integratedF37 (p : PatchPlacement) : Bool := p.onBranch

/-- **Why F37 exists (2).** The repair for `d755c886` is futon2 main `b463d85cc`, and main
has taken four unrelated commits since (and takes more before any click); before F37 the
enactment of a correctly integrated repair was refused as `:patch-not-canonical-head`. A
patch off the branch is still refused. -/
theorem d755c886_repairIntegration :
    ({ onBranch := true, commitsAfter := 4 } : PatchPlacement).integratedBeforeF37 = false ∧
      ({ onBranch := true, commitsAfter := 4 } : PatchPlacement).integratedF37 = true ∧
      ({ onBranch := false, commitsAfter := 0 } : PatchPlacement).integratedF37 = false := by
  decide

/-! ## Rev 26: click 11 read against its prediction; click 12 predicted -/

/-- **Click 11 as it ran**, `wm-click-96850427` (2026-10-20 19:35:43-19:37:03Z), read against
`click11PredictedPath` after the click. The record and the ledger agree with the prediction
through `routeEnacted`: the attempt-3 transaction was retired at resume time, attempt 4 was
prepared (F38) and claimed (ordinal 13), zai-2 authored with the repair's own sha
`b463d85cc` (ordinal 14; the F33 port read the answer), zai-3 reviewed under the F36 contract
(ordinal 15, `:approved`, `:reviewer-sha` = main's HEAD). Then `(A enact!)` returned
`:succeeded` with the F37 payload, and sealing the port receipt threw:
`load-file-recorded!` in futon3c `code_identity.clj` returned the value of `load-file`, the
file's last Var, `enact!` put the two Vars in `:reload-receipts`, and `identity/digest`
refuses a Var (`(C invoke-once :coordinator/port-threw)` at `:enact`). The click ended
`coordinationRefused`; no run record, outcome `:unknown`. -/
def click11ObservedPath : List RouteState :=
  [ ledgerRead, activeInjury, diagnosisPrepared, admissionRun, reviewAccepted,
    readinessReady, routeEnacted, coordinationRefused, terminalRecord ]

def click11ObservedObservation : CoordinationObservation :=
  { state := coordinationRefused, phase := .enact, outcome := .refused .portThrew }

/-- The ledger entries click 11 wrote: ordinals 13, 14, 15. -/
def click11ObservedLedgerWrites : List LedgerState := [.claimed, .authored, .reviewed]

theorem click11_observedConforms :
    conformsPath click11ObservedPath = true ∧ click11ObservedObservation.placed = true := by
  decide

/-- **The one finding.** Observed and predicted agree on the first seven states and differ at
the eighth; the ledger writes are the predicted ones short of `:enacted`. -/
theorem click11_oneFinding :
    click11ObservedPath.take 7 = click11PredictedPath.take 7 ∧
      click11ObservedPath[7]? = some coordinationRefused ∧
      click11PredictedPath[7]? = some enacted ∧
      click11ObservedLedgerWrites ++ [.enacted] = click11LedgerWrites := by
  decide

/-- What the reload function returns to `(A enact!)`. Before F39, the loaded value (a Var);
after, the reload record (path, git head, tree sha, content sha, stability, time, pid). The
port receipt is sealed by `identity/digest`, which accepts data and refuses a Var. F39
(futon3c, claude-5) returns the record; no caller used the value. -/
inductive ReloadReturn where
  | loadedValue
  | reloadRecord
  deriving DecidableEq, Repr

def ReloadReturn.sealable : ReloadReturn → Bool
  | .loadedValue => false
  | .reloadRecord => true

theorem enactReceipt_needsF39 :
    ReloadReturn.loadedValue.sealable = false ∧ ReloadReturn.reloadRecord.sealable = true := by
  decide

/-- **Click 12 predicted**, written before it runs. The transaction on disk is attempt 4 with
the author and review receipts recorded, and the ledger's active entry is `:reviewed`
(ordinal 15): no resume-time retirement (the attempt matches), `(C coordinate)` resumes from
`:reviewed` (admitted by `(C coordinate :coordinator/resume-state-refused)`'s set),
`(C invoke-once)` returns the two recorded receipts without calling a seat, enact runs under
F37 and F39 and appends `:enacted` (ordinal 16), the retry port queues, and the click closes
`:awaiting-retry`. The route path and observation are those of click 11's prediction; the
ledger write is the one click 11 did not make. -/
def click12PredictedPath : List RouteState := click11PredictedPath

def click12PredictedObservation : CoordinationObservation := click11PredictedObservation

def click12LedgerWrites : List LedgerState := [.enacted]

theorem click12_predicted :
    conformsPath click12PredictedPath = true ∧ click12PredictedObservation.placed = true ∧
      [LedgerState.abandoned] ++ f35LedgerWrite ++ click11ObservedLedgerWrites ++
          click12LedgerWrites ++ click11RetryLedgerWrites = d755c886PredictedLedgerPath := by
  decide

/-! ## Rev 27: click 12 and its retry child read against their predictions -/

/-- **Click 12 as it ran**, `wm-click-6696240e` (2026-10-20 19:42:5x-19:43:21Z): the
transaction resumed at attempt 4, no retirement, no seat called (the evidence store has no
zai-2 or zai-3 record in the window), `(A enact!)` under F37 and F39 sealed, the ledger took
ordinal 16 `:enacted` with `:integration-commit` at main's HEAD, the retry port queued
`wm-retry-repair/…-4`, and the click closed `:awaiting-retry`. Every element of
`click12_predicted` held. -/
def click12ObservedPath : List RouteState := click12PredictedPath

def click12ObservedObservation : CoordinationObservation := click12PredictedObservation

theorem click12_matched :
    click12ObservedPath = click12PredictedPath ∧
      click12ObservedObservation = click12PredictedObservation := by decide

/-- **The retry child as it ran**, `wm-retry-repair/…-4` (19:43:21-19:47:05Z, run
`2026-10-20-881a8839`): `(P attributable-retry-readiness)` admitted it and ordinary work ran,
but the War Machine selected nothing (`:failure {:kind :no-selection :stage :selection-world}`,
166 missions, 449 excursions and 155 tickets available to choose). `(T classify)` has no
non-injury kind for `:no-selection` (only `:abstained` is in `explicit-non-injury-kinds`),
so the record is an injury with a different cause: `(T integrate "nil? previous")` opened
injury `821c15d0` (ordinal 17, `:open`, attempt 1) and
`(T append-other-injury-retry-observation ledger/append-observation)` left the
`:retry-inconclusive` observation for `d755c886`'s enacted entry (ordinal 18). That is
`RetryClickOutcome.otherInjury`, the third of the model's outcomes, not the two
`click11Retry_predictedClose` named. The repair was not tested: the ordinary click never
reached the loop node it fixes. -/
def click11RetryObservedOutcome : RetryClickOutcome := .otherInjury

/-- The retry child's finding, and what the law says the next self-heal click does with it:
the route path conformed; the outcome was neither of the two named; and a different-cause
retry re-queues one child for attempt 4 (`(C coordinate-queued-retry ledger/append-requeue)`)
without discharging. -/
theorem click11Retry_finding :
    conformsPath click11RetryPredictedPath = true ∧
      click11RetryObservedOutcome ≠ .successfulTaskOutcome ∧
      click11RetryObservedOutcome ≠ .ordinarySelectionAbstention ∧
      click11RetryObservedOutcome.nextToday false false ⟨4, 0⟩ = .queued ⟨4, 1⟩ := by
  decide

/-- The ledger as the two clicks and the child left it, from ordinal 11, for `d755c886` alone:
the predicted path short of its discharge. -/
def d755c886LedgerAfterClick12 : List LedgerState :=
  [.abandoned, .reopened, .claimed, .authored, .reviewed, .enacted]

theorem d755c886_afterClick12 :
    ledgerConforms d755c886LedgerAfterClick12 = true ∧
      d755c886LedgerAfterClick12 ++ [.discharged] = d755c886PredictedLedgerPath := by decide

/-- The requeue budget: with `:retry-limit 3`, three more inconclusive children abandon the
injury `retryBudgetSpent` while the new injury `821c15d0` waits for its own attempt. -/
theorem d755c886_requeueBudget :
    RetryClickOutcome.otherInjury.nextToday false true ⟨4, 3⟩ = .abandoned .retryBudgetSpent := by
  decide

/-! ## Rev 28: the retry child's `:no-selection` read at its source; F40 named -/

/-- The route by which a judge's decision becomes the runner's selected entry,
`(R selected-entry)`: the posterior law `(R selected-entry :cascade-selection-posterior)`, the
META algorithm law `(R selected-entry :meta-algorithm-selection)`, or the sealed outer-policy
handoff of 2026-10-19 (futon2 `9946f92c1`, activated by `926429651`):
`(W cascade-decision :selected-outer-cascade-policy)` projects the verified carrier through
`selected-outer-cascade-policy/decision` into a decision with `:status :selected`, the sealed
entry's `:action`, and `:selection-certificate {:selection-route
:wm/selected-outer-cascade-policy-v1 …}`, and no `:selection-law`. The retry child's judge
decision in the daily trace (`wm-trace-2026-10-20.edn`, run `881a8839`) is exactly that:
status selected, action `M-formal-war-machine/policy-95a29538723f94edfa51`, route set, law nil.
The outer receipt on the run record agrees (`:chosen` M-formal-war-machine, the sealed menu of
seven, objective `:selected`). -/
inductive SelectionRoute where
  | posteriorLaw
  | metaAlgorithm
  | sealedOuterPolicy
  deriving DecidableEq, Repr

/-- `(R selected-entry)` at futon2 `aba9749d6`: a `cond` with an arm for each law and
`:else nil`. Nothing in the runner or the runtime reads `:selection-route`, so a sealed outer
policy yields no entry, the runner throws "selected no addressable action", and the click
closes `:no-selection` (`(R no-entry-failure-data)`: the decision's status is not
`:abstained`) with a chosen target on its outer receipt. The child was the first ordinary
run to take the sealed route; the run before it on the same branch (`08771834`, 10-19
17:40Z) had an outer selector that chose nothing and abstained typed. -/
def SelectionRoute.entryBeforeF40 : SelectionRoute → Bool
  | .posteriorLaw => true
  | .metaAlgorithm => true
  | .sealedOuterPolicy => false

/-- F40a: `(R selected-entry)` admits the sealed route. A decision whose certificate names
`:wm/selected-outer-cascade-policy-v1` and carries a map action and the selected canonical
cascade is the entry, with the sealed entry's own scores. -/
def SelectionRoute.entryF40 : SelectionRoute → Bool
  | _ => true

theorem sealedOuterPolicy_needsF40 :
    SelectionRoute.sealedOuterPolicy.entryBeforeF40 = false ∧
      SelectionRoute.sealedOuterPolicy.entryF40 = true := by decide

/-- Where the run record's `:decision` comes from (`(R persist-run-record!)`,
`retained-decision`): the selection checkpoint's judgment cell, else the `:no-selection`
sorry cell's decision when it has an action. A judgment cell is written only for a selected
entry (`(R retain-selection!)`), but `(R reconcile-selection-publication)` writes the
accumulation receipt into `[:judgment :controller-decision :accumulation]` of whatever cell
is there, and on a sorry cell that creates a judgment cell holding the two receipts and
nothing else. The `or` takes that stub before the sorry's decision. -/
inductive RecordDecisionSource where
  | judgment
  | accumulationStub
  | sorryDecision
  /-- Rev 30: no cell at all. A throw while closing escaped `(R run-opportunity-core!)`
  and `(R run-opportunity!)` answered with an empty checkpoint map under a synthetic
  initialization identity. -/
  | erased
  deriving DecidableEq, Repr

def RecordDecisionSource.carriesAction : RecordDecisionSource → Bool
  | .judgment => true
  | .accumulationStub => false
  | .sorryDecision => true
  | .erased => false

/-- The source retained today, given whether a selected judgment cell exists and whether
the close wrote the accumulation stub onto a sorry cell. -/
def retainedSourceBeforeF40b (judgmentRetained stubWritten : Bool) : RecordDecisionSource :=
  if judgmentRetained then .judgment
  else if stubWritten then .accumulationStub
  else .sorryDecision

/-- F40b: the stub is never a decision; without a selected judgment the sorry cell's decision
is the record's decision, receipts and all. -/
def retainedSourceF40b (judgmentRetained : Bool) : RecordDecisionSource :=
  if judgmentRetained then .judgment else .sorryDecision

/-- **The retry child's record misreports its own cause.** No judgment cell (no entry); the
stub was written at close (`:accumulation` with this run's tick id is the only decision key
the record kept besides the carriers computed at persist); so the record says no chosen
action (`:chosen {:status :absent :reason :no-chosen-action}`, `:selection-event
:selection-abstained`, `:abstention :not-abstained`, four loop nodes `:refused …-not-retained`)
while the trace holds the action. Injury `821c15d0`'s evidence pin is this record, so a
diagnosis read from the pin alone would repair the wrong thing. -/
theorem click11Retry_recordShadowed :
    (retainedSourceBeforeF40b false true).carriesAction = false ∧
      (retainedSourceF40b false).carriesAction = true := by decide

/-- Whether an abandonment carries a `:port-receipt-pin`.
`(L append-retry-result :attempt-limit-exhausted)` keeps the proposed entry's pin (the
author-failed path supplies one; ordinal 11 of the live ledger has it).
`(L append-requeue :retry-budget-spent)` builds its entry from the injury id, attempt and
repair id alone: no pin, ever. -/
def AbandonReason.pinned : AbandonReason → Bool → Bool
  | .attemptLimitExhausted, proposedPin => proposedPin
  | .retryBudgetSpent, _ => false

/-- F35's corrected reopen may cite only this injury's refused receipt pins
(`(L refused-receipt-pins)`: the `:author-failed` reopens and the abandonment, each once,
`(L state-defects :reopen/correction-pins-unknown)`), so a reopen from an abandonment is
reachable only when the abandonment, or an unspent earlier author failure, left a pin. -/
def correctedReopenReachable (r : AbandonReason) (proposedPin unspentRefusalPin : Bool) : Bool :=
  r.pinned proposedPin || unspentRefusalPin

/-- **Law gap (rev 28).** An injury abandoned `retryBudgetSpent` has no pin of its own to
cite, and no other transition leaves `abandoned`. For `d755c886` the two F33 refusals
(ordinals 9 and 11) were spent by ordinal 12's correction, so a third inconclusive child
closes it for good. The next law after F40: a budget-spent abandonment must name what the
inconclusive children refused on, or the re-queue must not count children that failed on
another open injury. -/
theorem budgetSpent_noReopen (p : Bool) :
    correctedReopenReachable .retryBudgetSpent p false = false := by
  cases p <;> rfl

/-- **The three re-queue clicks, predicted before any runs.** Without F40 a child whose outer
selector seals a policy again closes `:no-selection` again, repeats or reopens `821c15d0`,
and leaves another `:retry-inconclusive` observation; the third such child abandons
`d755c886` `retryBudgetSpent` with no pin to reopen from. Whether the outer selector seals a
policy again is not proved from the record (the `:selection-input-digest` is one input of
several); what is proved is that if it does, the child cannot reach the loop node. So the
clicks wait on F40, and the child is predicted after F40 lands. -/
theorem requeuedChildren_beforeF40 (p : Bool) :
    SelectionRoute.sealedOuterPolicy.entryBeforeF40 = false ∧
      RetryClickOutcome.otherInjury.nextToday false true ⟨4, 3⟩ = .abandoned .retryBudgetSpent ∧
      correctedReopenReachable .retryBudgetSpent p false = false := by
  refine ⟨by decide, by decide, ?_⟩
  cases p <;> rfl

/-- **Rev 29: the re-queued child under F40, predicted before the one click.** F40a (futon2
`acea15054`, the fixture projected at `f5c7b6d96`): `(R selected-entry)` has an arm for the
sealed route, so `entryF40` holds on every route. The three consumers of the entry, read at
`acea15054` by codex-1 and checked in review: `[:action :precedence]` on the live decision is a
co-apply map, so the co-apply gate passes; `selected-target` returns the mission;
`construct-selected-action` returns a construction. No refusal between the entry and
`(R retain-selection!)` is known. F40b (futon2 `477a9cae6`, pin corrected at `2196fc575`):
`(R reconcile-selection-publication)` writes the two receipts onto the decision the cell
carries, judgment or sorry, and leaves a decision-less sorry untouched, so the stub of rev 28
is never written and `retainedSourceF40b` is the source whichever cell exists. Prediction for
the one re-queue click after the reload at 21:43Z: if the outer selector seals a policy
again, the child's selection is retained as a judgment, its record's `:selection-event` is
`:cascade-selected` with the chosen target, and the click runs on past selection into
enactment, which no revision has read: the model predicts nothing past the loop node. If the
child instead closes on another injury, it is re-queued, not abandoned (this is the first of
the three re-queues; the witness entry is rev 28's generic ⟨4, 3⟩ with retries unspent): the
budget-spent abandonment of rev 28 needs two more such closes. A `:no-selection` close on
the sealed route is one finding against `entryF40`; a record whose `:decision` lacks the
action while the trace has it is one against `retainedSourceF40b`; a refusal between the
entry and the judgment is a consumer rev 28 did not name. -/
theorem requeuedChild_F40 :
    (∀ r : SelectionRoute, r.entryF40 = true) ∧
      (∀ j : Bool, (retainedSourceF40b j).carriesAction = true) ∧
      RetryClickOutcome.otherInjury.nextToday false false ⟨4, 3⟩ = .queued ⟨4, 4⟩ := by
  refine ⟨fun r => by cases r <;> rfl, fun j => by cases j <;> rfl, by decide⟩


/-! ## Rev 30: the close can be refused (read from click 13) -/

/-- The durable append of the selection cell at close, `(R persist-selection!)` through
`(C append-checkpoint!)`. Rev 29 modelled no refusal after the judgment. Click 13's child
(run `531f4c1f`, attempt-002 of cohort `:wm-contract-machinery-143-v1`) had its cell refused
`:cohort-checkpoint-oversized`: 33,554,433 bytes against the 32 MiB bound, the sealed menu of
8.3 MB carried three times (in the decision's certificate and twice inside
`:outer-task-selection`). The typed sorry was appended (`002-selection.edn`, 21:59:12Z) and
the refusal rethrown, as `(R append-checkpoint-or-refusal-sorry!)` promises. -/
inductive CloseAppend where
  | accepted
  | refused
  deriving DecidableEq, Repr

/-- What the catch does with a throw raised while closing. Today
(`(R run-opportunity-core!)`, the `@closing?` branch): it calls `(C close-attempt!)` without
first writing the required sorries the rethrow skipped, so the cohort refuses
`:required-checkpoints-missing`, and that second throw escapes to `(R run-opportunity!)`,
which answers with an empty checkpoint map. -/
inductive CloseBoundary where
  | closedBuildFailed
  | initializationIdentity
  deriving DecidableEq, Repr

def closeBoundaryToday : CloseAppend → CloseBoundary
  | .accepted => .closedBuildFailed
  | .refused => .initializationIdentity

/-- The record's decision source once the close is reached, after F40b, as a function of
whether the close's append was accepted. -/
def retainedSourceAtClose (judgmentRetained : Bool) (a : CloseAppend) : RecordDecisionSource :=
  match closeBoundaryToday a with
  | .closedBuildFailed => retainedSourceF40b judgmentRetained
  | .initializationIdentity => .erased

/-- **Click 13 witness.** The judgment was retained (the trace holds it; `entryF40` held:
the run went past selection into cascade-resume, 326 s, ending
`:open-cascade-review-answer-invalid`), the close's append was refused, and the record
carries no action. `requeuedChild_F40`'s second conjunct assumed the append accepted; this
is the case it did not name. The third conjunct is consistent so far: ledger ordinals 20 and
21 open injury `75747f06` and observe `:retry-inconclusive` for `d755c886`; no abandonment;
the re-queue entry ⟨4, 4⟩ is expected on the next click, as ordinal 19 followed click 12. -/
theorem click13_recordErased :
    (retainedSourceAtClose true .refused).carriesAction = false ∧
      retainedSourceAtClose true .accepted = .judgment := by decide

/-- F41: the closing branch writes the missing required sorries before the cohort close and,
if the close is still refused, returns the `:build-failed` result with its checkpoints and
the refusal typed, instead of letting the throw escape. -/
def closeBoundaryF41 : CloseAppend → CloseBoundary
  | _ => .closedBuildFailed

def retainedSourceF41 (judgmentRetained : Bool) (a : CloseAppend) : RecordDecisionSource :=
  match closeBoundaryF41 a with
  | .closedBuildFailed => retainedSourceF40b judgmentRetained
  | .initializationIdentity => .erased

/-- Prediction for the next click after F41 lands, before F42 shrinks the cell: the sealed
route's cell is refused again, the attempt closes `:build-failed` with
`:cohort-checkpoint-oversized`, and the record keeps the action whichever cell exists. Not
a heal: the close is still a refusal, which F42 removes. The model predicts nothing past
the loop node; `:open-cascade-review-answer-invalid` at cascade-resume is the enactment
stretch no revision has read. -/
theorem f41_recordKeepsAction :
    ∀ (j : Bool) (a : CloseAppend), (retainedSourceF41 j a).carriesAction = true := by
  intro j a; cases j <;> cases a <;> rfl

end DarkTower.WarMachine.SelfHealRoute
