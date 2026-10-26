import DarkTower.WarMachine.ReadingEraClickPrediction
import DarkTower.WarMachine.MedicLedgerBridge
import DarkTower.WarMachine.AlreadySatisfiedArtifactRefSeam

/-!
# The third click's ledger gate and terminal effect, predicted beside the record

Source: the packet from claude-9, 2026-10-26 15:30Z, and
`~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` R23.

**Why a companion and not a field.**  The second click (`wm-click-b56496c7…`,
13:43Z) produced no record: `meta_self_heal_production.clj` `route!`
(line 1424) loaded the durable injury ledger, found entry 45 open, and refused
before ordinary selection.  No `ClickRecord` field reads that ledger, so the
record prediction could neither hold nor fail.  This module predicts the two
things the third click should show that the second could not, both outside
the 27 fields: the gate finds no effective injury and ordinary selection runs;
and the click's own successful close is classified a non-injury at the
terminal, so the ledger gains an observation and no transition, and the click
after it is not blocked.  `ReadingEraClickPrediction.predictedRecord3` is the
record half; nothing there changes.

**The measured before-state.**  `before` transcribes the authority-aware
serving readback at 15:21:59Z (generation 9, eight scopes;
`45-adoption/live/claude9-readback.json`), re-counted against
`data/wm-meta-injuries-live-2026-10-22/ledger.edn` (sha `ec3cca7d…`):
46 entries, of which 30 carry `:wm/meta-injury-transition-v1` and 16
`:wm/meta-injury-observation-v1` (the medic operation `263dcf88…` is one of
the 16, ordinal 46); raw active 8 (every injury's latest transition is in
`active-states`); effective active 0 with an empty id set (all eight are
covered by medic corrections); the operation present exactly once.  The
ordinary-click budget reads 175 consumed of 178 allocated.  `before2` is the
same readback's fresh prestate before the operation was appended (45 entries,
effective 1, sole id `injury/9c622038…`): the state the second click met.

**The gate.**  `route!` computes `effective-active` (`:computed`) and takes
`(when (seq (:injuries active)) …)`: an empty effective set returns nil and
ordinary selection runs.  `gateState` transcribes that branch into
`SelfHealRoute.RouteState`: `noActiveInjury` when the effective count is 0,
`activeInjury` otherwise.  The table already has the edge
(`SelfHealRoute.transitions`, `(noActiveInjury, ordinarySelection)`) and the
door theorem (`SelfHealRoute.ordinaryWork_twoDoors`); `gate_path` states the
path for this click, `third_click_reaches_ordinary_selection` applies it to
`before`, and `second_click_was_blocked` applies `SelfHealRoute.noFallback`
to `before2`.

**The terminal.**  The predicted close is `:grounded-progress` with no
failure, as click 1.  `classificationOf` transcribes `meta_terminal_injury.clj`
`classify` (line 157, at futon2 `aa8bf5ed5`): when `closeVerdict` decides, the
close decides; when it does not (a failure is present, or an undecided cell),
the failure kind decides, and that verdict is a parameter here (the typed
non-injury kinds and the producer-qualified `:already-satisfied` are outside
this module).  `terminalEffect` transcribes `integrate` (line 250) for a
record no enacted repair names as its retry (`enacted-for-retry` matches on
`:retry-click`, and no entry carries a click id that does not exist yet) and
whose injury id, if any, has no previous entry: a non-injury appends one
observation; a fresh injury opens one transition, which is raw-active and,
uncovered, effective.  Two branches of `integrate` are not modelled: a
repeated active injury (an observation `:repeated-active-injury`) and a
medic-covered recurrence (`MedicRecurrence`).  Neither is predicted for this
click: the repaired classifier does not give click 1's cause key to a
successful close, and a failure kind gives a cause key no entry has.

**Tie to the bridge, not to a literal.**  An observation is an audit row of
`MedicLedgerBridge.LedgerEntry`; `MedicLedgerBridge.audit_projection_inert`
says the projection, hence the effective active set, is unchanged by it.
`shapeOf` reads a `ClickLedgerPrediction` off a bridge ledger, and
`observation_append_is_terminalEffect_nonInjury` says the shape of a ledger
with one audit appended is `terminalEffect` on the non-injury branch, for
every ledger.  `close_nonInjury_leaves_effective` is the packet's first
theorem in general form: for any close the law calls a non-injury, the
effective count after the click is the count before, and the transition
count is unchanged.  `third_click_after_effective_zero` instantiates it at
`CloseOutcomeImage.click1_law_nonInjury` and `before`.  The control is a
close with a failure kind the producer does not qualify: `closeVerdict` is
`none`, the kind's verdict `injury` decides, and `terminalEffect` opens a
transition (raw 9, effective 1), after which `gateState` is `activeInjury`
and `SelfHealRoute.noFallback` blocks the next click.  `miniBefore` runs the
same two appends through the bridge's `project` on a two-row ledger built
from `HistoricalMisclassificationCorrection.entry45` and its correction, so
the counts are computed by the model, not asserted.

**Numeral key** (as in `HistoricalMisclassificationCorrection`): injury
`injury/9c622038…` ↦ 9622; operation `263dcf88…` ↦ 2638; the third click's
record pin and a fresh injury are placeholders 4703, 7001, 4704.  The budget
is not in the ledger; `shapeOf` takes it as a parameter.

**Clojure correspondence** (no Clojure in this packet): the runner ingests
with the verifier (`full_loop_runner.clj`, sink `:meta-terminal-injury-ingest`,
line 9183); the observation it appends is the `:observation-class` row of the
classification with `:non-injury-reason :successful-task-outcome`.
-/

namespace DarkTower.WarMachine.ReadingEraClickLedgerPrediction

open DarkTower.WarMachine.SelfHealRoute (RouteState reaches edge conformsPath)
open DarkTower.WarMachine.CloseOutcomeImage (CloseOutcome image closeVerdict Verdict)
open DarkTower.WarMachine.HistoricalMisclassificationCorrection
open DarkTower.WarMachine.MedicLedgerBridge

-- `SelfHealRoute.reaches` unfolds deeper than the default allows `decide` to evaluate.
set_option maxRecDepth 8192

/-- What a click sees of the durable injury ledger and the click budget,
before and after.  Counts, not rows: the rows are `MedicLedgerBridge.LedgerEntry`
and `shapeOf` reads this off them. -/
structure ClickLedgerPrediction where
  /-- All ledger entries (`:entries` in the serving readback). -/
  entries : Nat
  /-- Entries with `:wm/meta-injury-transition-v1`. -/
  transitions : Nat
  /-- Entries with `:wm/meta-injury-observation-v1`; medic operations are among them. -/
  observations : Nat
  /-- Injuries whose latest transition is in `active-states` (`:raw`). -/
  rawActive : Nat
  /-- Raw-active injuries not covered by a medic correction (`:effective`). -/
  effectiveActive : Nat
  /-- Their ids (`:effective-ids`). -/
  effectiveIds : List InjuryId
  /-- Occurrences of the operation `263dcf88…` (`:operation-count`). -/
  operationCount : Nat
  /-- `:budget :consumed`. -/
  budgetConsumed : Nat
  /-- `:budget :allocated`. -/
  budgetAllocated : Nat
  deriving DecidableEq, Repr

/-- The readback at 15:21:59Z, after the medic operation. -/
def before : ClickLedgerPrediction :=
  ⟨46, 30, 16, 8, 0, [], 1, 175, 178⟩

/-- The same readback's fresh prestate, before the operation: 45 entries,
raw 8, effective 1 with the sole id `injury/9c622038…`, zero occurrences of
the operation.  What the second click met. -/
def before2 : ClickLedgerPrediction :=
  ⟨45, 30, 15, 8, 1, [9622], 0, 175, 178⟩

/-- The medic operation's effect on the shape: one observation row, the one
effective injury retired.  The retirement itself is
`HistoricalMisclassificationCorrection.entry45_correction_qualifies_with_successful_close_replay`. -/
theorem medic_operation_effect :
    before = { before2 with entries := 46, observations := 16, effectiveActive := 0,
                            effectiveIds := [], operationCount := 1 } := rfl

/-! ## The gate -/

/-- `route!`'s branch on the computed effective set: `(when (seq (:injuries
active)) …)` returns nil when the set is empty. -/
def gateState (s : ClickLedgerPrediction) : RouteState :=
  if s.effectiveActive = 0 then .noActiveInjury else .activeInjury

/-- The path the third click is predicted to take, over the transcribed
table: each edge is present, ordinary selection is reached from the ledger
read, and the path is a complete click path. -/
theorem gate_path :
    edge .ledgerRead .noActiveInjury = true ∧
      edge .noActiveInjury .ordinarySelection = true ∧
      reaches .ledgerRead .ordinarySelection = true ∧
      conformsPath [.ledgerRead, .noActiveInjury, .ordinarySelection, .terminalRecord] = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem gate_before : gateState before = .noActiveInjury := rfl

/-- The third click's gate finds no effective injury and ordinary selection runs. -/
theorem third_click_reaches_ordinary_selection :
    reaches (gateState before) .ordinarySelection = true := by decide

/-- The second click's gate, on the prestate: an active injury, from which no
table path enters ordinary selection (`SelfHealRoute.noFallback`).  This is
R23 as the table states it. -/
theorem second_click_was_blocked :
    gateState before2 = .activeInjury ∧
      reaches (gateState before2) .ordinarySelection = false :=
  ⟨rfl, SelfHealRoute.noFallback⟩

/-! ## The terminal -/

/-- `classify` for a record with the given close and failure presence: the
close decides when `closeVerdict` does; otherwise the failure kind's verdict,
supplied, decides. -/
def classificationOf (c : CloseOutcome) (failurePresent : Bool)
    (failureKindVerdict : Verdict) : Verdict :=
  match closeVerdict (image c) failurePresent with
  | some v => v
  | none => failureKindVerdict

/-- `integrate` on a record no enacted repair names as its retry, whose
injury id (if any) has no previous entry: a non-injury appends one
observation; a fresh injury opens one transition, raw-active and effective. -/
def terminalEffect (s : ClickLedgerPrediction) (injury : InjuryId) :
    Verdict → ClickLedgerPrediction
  | .nonInjury => { s with entries := s.entries + 1, observations := s.observations + 1 }
  | .injury => { s with entries := s.entries + 1, transitions := s.transitions + 1,
                        rawActive := s.rawActive + 1,
                        effectiveActive := s.effectiveActive + 1,
                        effectiveIds := s.effectiveIds ++ [injury] }

/-- The click consumes one unit of the ordinary-click budget and ends with the
terminal effect. -/
def afterClick (s : ClickLedgerPrediction) (injury : InjuryId) (v : Verdict) :
    ClickLedgerPrediction :=
  { terminalEffect s injury v with budgetConsumed := s.budgetConsumed + 1 }

/-- The predicted after-state: 47 entries (30 transitions, 17 observations),
raw 8, effective 0, the id set empty, the operation still once, budget 176
of 178. -/
def after : ClickLedgerPrediction :=
  ⟨47, 30, 17, 8, 0, [], 1, 176, 178⟩

/-- The packet's first theorem in general form: for any close the law calls
a non-injury, the click leaves the effective count and the transition count
as they were and adds one observation, whatever the failure-kind verdict
would have been. -/
theorem close_nonInjury_leaves_effective (s : ClickLedgerPrediction) (injury : InjuryId)
    (c : CloseOutcome) (b : Bool) (k : Verdict)
    (h : closeVerdict (image c) b = some .nonInjury) :
    (afterClick s injury (classificationOf c b k)).effectiveActive = s.effectiveActive ∧
      (afterClick s injury (classificationOf c b k)).effectiveIds = s.effectiveIds ∧
      (afterClick s injury (classificationOf c b k)).transitions = s.transitions ∧
      (afterClick s injury (classificationOf c b k)).observations = s.observations + 1 := by
  simp [afterClick, classificationOf, h, terminalEffect]

/-- The predicted close is classified a non-injury by the close alone
(`CloseOutcomeImage.click1_law_nonInjury`); the failure-kind verdict is not
consulted. -/
theorem predicted_close_classified_nonInjury (k : Verdict) :
    classificationOf .groundedProgress false k = .nonInjury := by
  simp [classificationOf, CloseOutcomeImage.click1_law_nonInjury]

/-- The third click's after-state has effective count 0, by the law and the
measured before-state. -/
theorem third_click_after_effective_zero (k : Verdict) :
    (afterClick before 9622 (classificationOf .groundedProgress false k)).effectiveActive = 0 :=
  (close_nonInjury_leaves_effective before 9622 .groundedProgress false k
    CloseOutcomeImage.click1_law_nonInjury).1

/-- The whole predicted after-state, for the predicted close. -/
theorem third_click_after (k : Verdict) :
    afterClick before 9622 (classificationOf .groundedProgress false k) = after := by
  cases k <;> decide

/-- The click after the third is not blocked. -/
theorem fourth_click_not_blocked (k : Verdict) :
    gateState (afterClick before 9622 (classificationOf .groundedProgress false k)) =
        .noActiveInjury ∧
      reaches (gateState (afterClick before 9622 (classificationOf .groundedProgress false k)))
        .ordinarySelection = true := by
  rw [third_click_after]; exact ⟨rfl, by decide⟩

/-! ## The control: a close with a failure kind -/

/-- With a failure present the close does not decide (`closeVerdict … true =
none`), the kind's verdict `injury` decides, and `integrate` opens a
transition: 47 entries (31 transitions, 16 observations), raw 9, effective 1
with the fresh id.  The after-state the structure must be able to refuse. -/
theorem failure_kind_injury_opens_transition :
    closeVerdict (image .groundedProgress) true = none ∧
      classificationOf .groundedProgress true .injury = .injury ∧
      afterClick before 7001 (classificationOf .groundedProgress true .injury) =
        ⟨47, 31, 16, 9, 1, [7001], 1, 176, 178⟩ := by
  refine ⟨rfl, rfl, ?_⟩; decide

/-- After that control, the next click's gate finds an active injury and no
table path enters ordinary selection. -/
theorem control_blocks_next_click :
    gateState (afterClick before 7001 (classificationOf .groundedProgress true .injury)) =
        .activeInjury ∧
      reaches .activeInjury .ordinarySelection = false :=
  ⟨rfl, SelfHealRoute.noFallback⟩

/-- The predicted after-state and the control differ: the prediction is not
vacuous on the terminal. -/
theorem prediction_differs_from_control (k : Verdict) :
    afterClick before 9622 (classificationOf .groundedProgress false k) ≠
      afterClick before 7001 (classificationOf .groundedProgress true .injury) := by
  cases k <;> decide

/-! ## The shape read off a bridge ledger -/

/-- Rows carrying the transition schema. -/
def transitionCount : List LedgerEntry → Nat
  | [] => 0
  | .transition _ :: rest => transitionCount rest + 1
  | _ :: rest => transitionCount rest

/-- Rows carrying the observation schema: audits and medic operations. -/
def observationCount : List LedgerEntry → Nat
  | [] => 0
  | .transition _ :: rest => observationCount rest
  | _ :: rest => observationCount rest + 1

/-- Occurrences of the medic operation with the given id. -/
def operationCount (opId : OperationId) : List LedgerEntry → Nat
  | [] => 0
  | .medic op :: rest => operationCount opId rest + (if op.operationId = opId then 1 else 0)
  | _ :: rest => operationCount opId rest

/-- The shape of a bridge ledger (newest-first), under the given admissions,
with the budget supplied beside it. -/
def shapeOf (misclassification : MisclassificationAdmission) (genuine : GenuineRepairAdmission)
    (budget : Nat × Nat) (opId : OperationId) (ledger : List LedgerEntry) :
    ClickLedgerPrediction :=
  let state := project misclassification genuine ledger
  { entries := ledger.length
    transitions := transitionCount ledger
    observations := observationCount ledger
    rawActive := ((latestEntries state.history).filter (·.active)).length
    effectiveActive := (medicEffectiveActive state).length
    effectiveIds := medicEffectiveActive state
    operationCount := operationCount opId ledger
    budgetConsumed := budget.1
    budgetAllocated := budget.2 }

/-- An appended observation is inert on the projection
(`MedicLedgerBridge.audit_projection_inert`), so the shape of any ledger with
one audit row appended is `terminalEffect` on the non-injury branch: one
entry, one observation, nothing else. -/
theorem observation_append_is_terminalEffect_nonInjury
    (misclassification : MisclassificationAdmission) (genuine : GenuineRepairAdmission)
    (budget : Nat × Nat) (opId : OperationId) (ledger : List LedgerEntry)
    (pin : Nat) (injury : InjuryId) :
    shapeOf misclassification genuine budget opId (.audit pin :: ledger) =
      terminalEffect (shapeOf misclassification genuine budget opId ledger) injury .nonInjury := by
  simp [shapeOf, terminalEffect, transitionCount, observationCount, operationCount,
    audit_projection_inert]

/-! ## A two-row ledger run through the bridge -/

/-- The medic operation retiring entry 45, as a bridge row. -/
def op45 : MedicOperation :=
  ⟨2638, 0, ⟨.historicalMisclassification entry45Payload,
             some (.historicalMisclassification entry45Evidence)⟩⟩

/-- Entry 45 and its correction: raw 1, effective 0, the operation once. -/
def miniBefore : List LedgerEntry := [.medic op45, .transition entry45]

theorem miniBefore_shape :
    shapeOf admitEntry45 HistoricalMisclassificationCorrection.noGenuine (175, 178) 2638 miniBefore =
      ⟨2, 1, 1, 1, 0, [], 1, 175, 178⟩ := by decide

/-- The predicted click's observation row, run through `project`: one more
observation, effective still empty; and it is the non-injury terminal effect. -/
theorem miniBefore_observation :
    shapeOf admitEntry45 HistoricalMisclassificationCorrection.noGenuine (175, 178) 2638 (.audit 4703 :: miniBefore) =
        ⟨3, 1, 2, 1, 0, [], 1, 175, 178⟩ ∧
      shapeOf admitEntry45 HistoricalMisclassificationCorrection.noGenuine (175, 178) 2638 (.audit 4703 :: miniBefore) =
        terminalEffect (shapeOf admitEntry45 HistoricalMisclassificationCorrection.noGenuine (175, 178) 2638 miniBefore) 9622
          .nonInjury :=
  ⟨by decide, observation_append_is_terminalEffect_nonInjury _ _ _ _ _ _ _⟩

/-- The control's open transition for a fresh injury, run through `project`:
one more transition, raw 2, effective 1 with the fresh id; and it is the
injury terminal effect. -/
theorem miniBefore_fresh_injury :
    let fresh : InjuryEntry := ⟨7001, 47, 0, 4703, 4704, true⟩
    shapeOf admitEntry45 HistoricalMisclassificationCorrection.noGenuine (175, 178) 2638 (.transition fresh :: miniBefore) =
        ⟨3, 2, 1, 2, 1, [7001], 1, 175, 178⟩ ∧
      shapeOf admitEntry45 HistoricalMisclassificationCorrection.noGenuine (175, 178) 2638 (.transition fresh :: miniBefore) =
        terminalEffect (shapeOf admitEntry45 HistoricalMisclassificationCorrection.noGenuine (175, 178) 2638 miniBefore) 7001
          .injury := by
  refine ⟨by decide, by decide⟩

#print axioms medic_operation_effect
#print axioms gate_path
#print axioms gate_before
#print axioms third_click_reaches_ordinary_selection
#print axioms second_click_was_blocked
#print axioms close_nonInjury_leaves_effective
#print axioms predicted_close_classified_nonInjury
#print axioms third_click_after_effective_zero
#print axioms third_click_after
#print axioms fourth_click_not_blocked
#print axioms failure_kind_injury_opens_transition
#print axioms control_blocks_next_click
#print axioms prediction_differs_from_control
#print axioms observation_append_is_terminalEffect_nonInjury
#print axioms miniBefore_shape
#print axioms miniBefore_observation
#print axioms miniBefore_fresh_injury

/-! ## The fourth click: the already-satisfied close through the repaired seam

Source: the packet from claude-9, 2026-10-26 18:06Z.  The third click's close
was `:build-failed :invalid-author-refusal` (R24): the terminal opened entry
47 and the readback after the click was the control's shape
(`after3Observed`).  Entry 47 was retired by the medic operation
`987e211a…` (entry 48, 17:53Z).  Both halves of the artifact-ref seam are
repaired and reloaded (`AlreadySatisfiedArtifactRefSeam`, Parts 2 and 4), so
the same answer from the author now closes `:already-satisfied` at
`:author-wait` and the terminal classifies it a non-injury through
`producer-qualified-already-satisfied?`.

**The before-state.**  `before4` transcribes the readback at 18:01:02Z
(generation 10, nine scopes; `fourth-click-2026-10-26/claude9-readback-pre-click.edn`),
re-counted against `ledger.edn` (sha `d41add47…`): 48 entries, 31 with the
transition schema and 17 with the observation schema; raw 9, effective 0, ids
empty; budget 176 of 178.  The structure's `operationCount` field is
documented as counting `263dcf88…`; for this click the operation that matters
is `987e211a…` (entry 48), and `before4` counts that one.  Both occur
exactly once in the ledger, so the value is 1 under either reading.

**The close.**  `close4` is `recordOf (.alreadySatisfied 978)` from the seam
module: the close `throw-if-author-refused!` writes for the repaired
consumer's answer on either ordering of the reply
(`repaired_agrees_on_both_replies`), and on the deployed Agency's extraction
(`either_half_suffices`).  Its `verdictOf` is non-injury by the kind, not by
the close: `closeVerdict .alreadySatisfied true = none`
(`control_agrees_by_kind_not_by_close`).  `classificationOf_eq_verdictOf`
ties this module's `classificationOf` to the seam's `verdictOf` in general:
whenever the kind's verdict is `some k`, `classificationOf` with `k` is
`verdictOf`.  `fourth_click_after` then takes `k` from `verdictOf close4`
and not from a literal.

**The control.**  `classify` reaches `:non-injury` for kind
`:already-satisfied` only through `producer-qualified-already-satisfied?`
(`meta_terminal_injury.clj` 59–73): the kind is not in
`explicit-non-injury-kinds` (10–14: abstained, operator-cancelled,
declared-no-work, diagnostic-only).  The qualification reads the grounded
commit: a non-blank repo and a sha matching `git-re`, 40–64 hex.  The
runner's `author-refusal-classification` accepts 7–40 hex from the reply or
the card (`\b[0-9a-f]{7,40}\b`, 3281–3284), so a short sha grounds a close the
terminal then refuses to qualify, and the default injury branch opens a
transition.  `GroundedCommit` carries the two things the qualification
reads; `qualifiedKindVerdict` is `kindVerdict` with the qualification
applied; `verdictOfQualified` is `verdictOf` with it.  The three `:detail`
fields and `[:run-output :outcome]` agree whenever `throw-if-author-refused!`
wrote the close, so the sha's length is the one live way to fail.
`runner_terminal_length_gap` names the lengths the runner accepts and the
terminal refuses: exactly 7 to 39.  `control_short_sha_opens_transition` is
the control: the seam's `shortOnlyReply` grounds the short form, the close is
`alreadySatisfied` with that kind, the qualified verdict is injury, the
after-state is raw 10, effective 1, and click 5 is blocked.

**Numeral key**: the fresh injury the control would open ↦ 7002; the full
sha ↦ 978 (40 hex), the short form ↦ 977 (8 hex), as in the seam module. -/

open DarkTower.WarMachine.AlreadySatisfiedArtifactRefSeam
  (Close FailureKind Consumed recordOf verdictOf kindVerdict failurePresent
    repairedClassifier currentClassifier firstArtifactRef preferredArtifactRef
    store3 storeResolvingShort card3 full3 witnessReply controlReply witnessReplyFull
    shortOnlyReply)

/-- The readback after the third click (16:14:48Z, generation 9): 47 entries,
31 transitions, 16 observations, raw 9, effective 1 with entry 47's injury
(`injury/2aef7e0c…` ↦ 2001), the operation once, budget 176 of 178.  It is
the control's shape with the fresh id 2001 for the placeholder 7001. -/
def after3Observed : ClickLedgerPrediction :=
  ⟨47, 31, 16, 9, 1, [2001], 1, 176, 178⟩

theorem after3Observed_is_control_shape :
    after3Observed = afterClick before 2001 (classificationOf .buildFailed true .injury) := by
  decide

/-- The readback at 18:01:02Z, after entry 48 retired entry 47.  The
operation counted is `987e211a…`. -/
def before4 : ClickLedgerPrediction :=
  ⟨48, 31, 17, 9, 0, [], 1, 176, 178⟩

/-- Entry 48's effect on the shape: one observation row, the one effective
injury retired, the history untouched (the retirement in the medic form is
`AlreadySatisfiedArtifactRefSeam.entry47_correction_qualifies`). -/
theorem medic_operation_48_effect :
    before4 = { after3Observed with entries := 48, observations := 17,
                                    effectiveActive := 0, effectiveIds := [] } := rfl

/-! ### The gate -/

theorem gate_before4 : gateState before4 = .noActiveInjury := rfl

/-- The fourth click's gate finds no effective injury and ordinary selection runs. -/
theorem fourth_click_reaches_ordinary_selection :
    reaches (gateState before4) .ordinarySelection = true := by decide

/-- The click after the third met an active injury on `after3Observed`; the
medic operation is what reopened the door. -/
theorem after3_was_blocked_before4_is_not :
    gateState after3Observed = .activeInjury ∧
      reaches (gateState after3Observed) .ordinarySelection = false ∧
      reaches (gateState before4) .ordinarySelection = true :=
  ⟨rfl, SelfHealRoute.noFallback, by decide⟩

/-! ### The close -/

/-- The fourth click's close as the terminal reads it: outcome
`alreadySatisfied`, failure kind `alreadySatisfied`. -/
def close4 : Close := recordOf (.alreadySatisfied 978)

/-- The close is what the repaired consumer writes on either ordering of the
reply, and what the deployed Agency's extraction feeds either consumer. -/
theorem close4_from_repaired_seam :
    repairedClassifier store3 card3 (firstArtifactRef witnessReply) =
        some (.alreadySatisfied 978) ∧
      repairedClassifier store3 card3 (firstArtifactRef controlReply) =
        some (.alreadySatisfied 978) ∧
      currentClassifier store3 card3 (preferredArtifactRef full3 witnessReplyFull) =
        some (.alreadySatisfied 978) ∧
      close4 = ⟨.alreadySatisfied, .alreadySatisfied⟩ :=
  ⟨AlreadySatisfiedArtifactRefSeam.repaired_agrees_on_both_replies.1,
   AlreadySatisfiedArtifactRefSeam.repaired_agrees_on_both_replies.2.1,
   AlreadySatisfiedArtifactRefSeam.either_half_suffices.2.1, rfl⟩

/-- The close does not decide (a failure kind is present); the kind decides,
non-injury. -/
theorem close4_decided_by_kind :
    closeVerdict (image close4.outcome) (failurePresent close4.failure) = none ∧
      kindVerdict close4.failure = some .nonInjury ∧
      verdictOf close4 = some .nonInjury := by decide

/-- `classificationOf` is `verdictOf` whenever the kind's verdict is the
supplied one: the tie between this module's classifier and the seam's. -/
theorem classificationOf_eq_verdictOf (c : Close) (k : Verdict)
    (h : kindVerdict c.failure = some k) :
    some (classificationOf c.outcome (failurePresent c.failure) k) = verdictOf c := by
  unfold classificationOf verdictOf
  cases closeVerdict (image c.outcome) (failurePresent c.failure) <;> simp [h]

/-- The predicted after-state: 49 entries (31 transitions, 18 observations),
raw 9, effective 0, ids empty, the operation once, budget 177 of 178. -/
def after4 : ClickLedgerPrediction :=
  ⟨49, 31, 18, 9, 0, [], 1, 177, 178⟩

/-- The whole predicted after-state, for the predicted close, with the kind's
verdict taken from the seam's `verdictOf close4`. -/
theorem fourth_click_after (k : Verdict) (hk : verdictOf close4 = some k) :
    afterClick before4 7002 (classificationOf close4.outcome (failurePresent close4.failure) k) =
      after4 := by
  have : k = .nonInjury := by
    have h := close4_decided_by_kind.2.2
    rw [hk] at h; exact Option.some.inj h
  subst this; decide

/-- The same, stated as the packet asked: the close `.alreadySatisfied` with a
failure present, and `k` the verdict of `recordOf (.alreadySatisfied s)`. -/
theorem fourth_click_after_packet_form (s : Nat) (k : Verdict)
    (hk : verdictOf (recordOf (.alreadySatisfied s)) = some k) :
    afterClick before4 7002 (classificationOf .alreadySatisfied true k) = after4 := by
  have : k = .nonInjury := by
    have h : verdictOf (recordOf (.alreadySatisfied s)) = some .nonInjury := rfl
    rw [hk] at h; exact Option.some.inj h
  subst this; decide

/-- The after-state leaves the effective set and the transitions as they were
and adds one observation; the ledger gains one observation and no transition. -/
theorem fourth_click_observation_only :
    after4.effectiveActive = before4.effectiveActive ∧ after4.effectiveIds = before4.effectiveIds ∧
      after4.transitions = before4.transitions ∧ after4.observations = before4.observations + 1 := by
  decide

/-- Click 5 is not blocked. -/
theorem fifth_click_not_blocked :
    gateState after4 = .noActiveInjury ∧ reaches (gateState after4) .ordinarySelection = true :=
  ⟨rfl, by decide⟩

/-! ### The control: a grounded sha the terminal does not qualify -/

/-- What `producer-qualified-already-satisfied?` reads of the grounded commit:
whether `:repo` is non-blank, and the sha's hex length (`git-re` is
`[0-9a-f]{40,64}`, matched whole). -/
structure GroundedCommit where
  repoNonBlank : Bool
  shaHexLength : Nat
  deriving DecidableEq, Repr

/-- The terminal's acceptance of a sha: 40 to 64 hex digits. -/
def terminalAcceptsSha (n : Nat) : Bool := 40 ≤ n && n ≤ 64

/-- The runner's acceptance (`author-refusal-classification`,
`\b[0-9a-f]{7,40}\b`): 7 to 40. -/
def runnerAcceptsSha (n : Nat) : Bool := 7 ≤ n && n ≤ 40

/-- The lengths the runner grounds and the terminal refuses: exactly 7 to 39. -/
theorem runner_terminal_length_gap (n : Nat) :
    (runnerAcceptsSha n = true ∧ terminalAcceptsSha n = false) ↔ (7 ≤ n ∧ n ≤ 39) := by
  simp [runnerAcceptsSha, terminalAcceptsSha]; omega

def producerQualified (g : GroundedCommit) : Bool :=
  g.repoNonBlank && terminalAcceptsSha g.shaHexLength

/-- `kindVerdict` with the qualification applied: `:already-satisfied` is a
non-injury only when the grounded commit qualifies, else the default injury
branch; the other kinds as before. -/
def qualifiedKindVerdict (g : GroundedCommit) : FailureKind → Option Verdict
  | .alreadySatisfied => some (if producerQualified g then .nonInjury else .injury)
  | k => kindVerdict k

/-- `verdictOf` with the qualification applied. -/
def verdictOfQualified (g : GroundedCommit) (c : Close) : Option Verdict :=
  match closeVerdict (image c.outcome) (failurePresent c.failure) with
  | some v => some v
  | none => qualifiedKindVerdict g c.failure

/-- A qualifying grounded commit changes nothing: the qualified reading is the
seam's. -/
theorem qualified_agrees_with_seam (g : GroundedCommit) (hg : producerQualified g = true)
    (c : Close) : verdictOfQualified g c = verdictOf c := by
  unfold verdictOfQualified verdictOf
  cases closeVerdict (image c.outcome) (failurePresent c.failure) with
  | some v => rfl
  | none =>
    simp only
    cases c.failure <;> simp [qualifiedKindVerdict, kindVerdict, hg]

/-- The full sha in `futon5a`: qualifies. -/
def fullGrounded : GroundedCommit := ⟨true, 40⟩

/-- The short form `09a7cb8d`: the runner grounds it, the terminal does not
qualify it. -/
def shortGrounded : GroundedCommit := ⟨true, 8⟩

theorem fourth_click_qualified :
    producerQualified fullGrounded = true ∧
      verdictOfQualified fullGrounded close4 = some .nonInjury := by decide

/-- The control: the author names only the short sha; the deployed Agency
extracts it (no full sha to prefer), the repaired classifier grounds it, the
close is `alreadySatisfied` with that kind, the terminal refuses to qualify
the 8-hex sha, the default injury branch opens a transition (49 entries, 32
transitions, raw 10, effective 1), and click 5 meets an active injury. -/
theorem control_short_sha_opens_transition :
    preferredArtifactRef full3 shortOnlyReply = some (.sha 977) ∧
      repairedClassifier storeResolvingShort card3 (preferredArtifactRef full3 shortOnlyReply) =
        some (.alreadySatisfied 977) ∧
      recordOf (.alreadySatisfied 977) = close4 ∧
      producerQualified shortGrounded = false ∧
      verdictOfQualified shortGrounded close4 = some .injury ∧
      afterClick before4 7002 (classificationOf .alreadySatisfied true .injury) =
        ⟨49, 32, 17, 10, 1, [7002], 1, 177, 178⟩ ∧
      gateState (afterClick before4 7002 (classificationOf .alreadySatisfied true .injury)) =
        .activeInjury ∧
      reaches .activeInjury .ordinarySelection = false := by
  refine ⟨by decide, by decide, rfl, rfl, by decide, by decide, rfl, SelfHealRoute.noFallback⟩

/-- The seam's unqualified `verdictOf` and the qualified reading differ on
the short sha: the control is visible only with the qualification. -/
theorem short_sha_control_needs_qualification :
    verdictOf close4 = some .nonInjury ∧
      verdictOfQualified shortGrounded close4 = some .injury := by decide

/-- A blank repo fails the qualification too, with a full sha. -/
theorem blank_repo_not_qualified :
    verdictOfQualified ⟨false, 40⟩ close4 = some .injury := by decide

/-- The prediction and the control differ on the terminal. -/
theorem fourth_prediction_differs_from_control :
    after4 ≠ afterClick before4 7002 (classificationOf .alreadySatisfied true .injury) := by
  decide

/-- The `:invalid-author-refusal` close, click 3's, under the qualified
reading: still an injury (the kind's verdict, unchanged by `g`). -/
theorem click3_close_still_injury (g : GroundedCommit) :
    verdictOfQualified g (recordOf .invalidAuthorRefusal) = some .injury := by
  unfold verdictOfQualified
  simp [recordOf, qualifiedKindVerdict, kindVerdict, failurePresent, closeVerdict, image]

#print axioms after3Observed_is_control_shape
#print axioms medic_operation_48_effect
#print axioms gate_before4
#print axioms fourth_click_reaches_ordinary_selection
#print axioms after3_was_blocked_before4_is_not
#print axioms close4_from_repaired_seam
#print axioms close4_decided_by_kind
#print axioms classificationOf_eq_verdictOf
#print axioms fourth_click_after
#print axioms fourth_click_after_packet_form
#print axioms fourth_click_observation_only
#print axioms fifth_click_not_blocked
#print axioms runner_terminal_length_gap
#print axioms qualified_agrees_with_seam
#print axioms fourth_click_qualified
#print axioms control_short_sha_opens_transition
#print axioms short_sha_control_needs_qualification
#print axioms blank_repo_not_qualified
#print axioms fourth_prediction_differs_from_control
#print axioms click3_close_still_injury

end DarkTower.WarMachine.ReadingEraClickLedgerPrediction
