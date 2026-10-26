import DarkTower.WarMachine.ReadingEraClickPrediction
import DarkTower.WarMachine.MedicLedgerBridge

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

end DarkTower.WarMachine.ReadingEraClickLedgerPrediction
