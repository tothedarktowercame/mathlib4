import Mathlib.Tactic

/-!
# The predicted record of the first click after the reading-era repairs

Source: `~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` (claude-9,
2026-10-26) and the packet
`~/notes/wm-next/outer-selection/packets/reading-era-click-prediction-packet.md`.

Joe, 2026-10-20: a click that is not predicted in Lean before it runs only
transcribes what happened.  This module writes the prediction for the first
ordinary click on the canonical route after the reading-era defect list, as a
named record `predictedRecord` proved to satisfy `Predicted`.  The click then
either satisfies `Predicted` (the demonstration) or fails a named clause (the
single finding for that click).

`ClickRecord` has one field group per defect line that a single click's files
can show.  Every field's docstring names the file and the key the reviewer
reads to fill it.  The files, with the abbreviations used below:

* RR: `futon2/data/wm-runs/tick-run-record-<run>.edn`, the run record.
* SEL: `<attempt>/002-selection.edn`; its `[:payload :judgment]` carries the
  same `:outer-task-selection` receipt as RR when a target was chosen, and
  `[:payload :sorry]` when none was.
* TO: `<attempt>/retained/token-outcome.edn`.
* REQ: `<run record path>.requirements.edn`, written by `wm_run_alert.py`.
* CS: the click state, `GET /api/alpha/wm/click/<click-id>` on futon3c.

Lines with no single-click observable, so no field:

* R5 is not a defect under the ruled Q2.
* R9 (a map-valued patch var accepted as callable) is refused by
  `full_loop_runtime.clj` `resolve-reviewed-patch`, which runs only on the
  self-heal repair path over an authored patch answer and records in the
  repair ledger; an ordinary click loads no patch var, so none of its files
  can show the clause.
* R14 was test drift (no clause).  R15 and R16 need no clause: the model's
  `comparisonKey : Nat` is total, so a non-exact G has no image.
* The runner's `:runner/source` also lists `:unregistered` and `:unavailable`
  namespaces (4 and 30 on m150-002); those are fail-open by design in
  `refuse-on-runner-source-drift!` and not a clause, so they are not fields.

Values forced by the state on 2026-10-26, used in `predictedRecord`:

* All 27 authored completion checks are prose (R8a), so both pattern-domain
  rows are `:completion-check-not-executable` and no row carries a Boolean.
* The Q6 predecessor is run `2026-10-24-25e24e8b…` (m150-002), after this
  morning's quarantine of the 33 test-origin runs.  Its terminal carrier in
  `run-stream.edn` was sealed before the R18 digest fix (`0cf37bdfb`,
  06:22Z) under the other print binding, and the value-digest test keeps it as
  a failing control, so `previous-run/predecessor` reads it as
  `:not-recomputable :previous-terminal-carrier-tampered`, and
  `decide-exclusion` carries that reason into the Q6 carrier.  Even if the
  seal verified, the predecessor's outcome is `:invalid` (raw
  `:build-failed`), not `:refused`, so Q6 would be `:not-triggered`.  Either
  way the first click cannot exclude.
* Loaded namespace hashes equal the disk hashes (drift `[]` at 08:48Z), so
  there is no `:stale-outer-selection-composition` refusal (R10).
* The chosen target has one menu entry on the m150-002 field (one entry per
  target, four targets), so the policy stages are one constructed, one
  scored, one posterior key.

Values not forced, where `predictedRecord` carries the expected value and the
clause states the relation the click must satisfy: the unmet-reading count
(101 on m150-002), the frontier census counts (109 eligible, 4 ranked, 105
unranked on the Q8a fixture), the preparation batch (3 attempted, 0 refused,
98 pending), and the requirements verdict (`checked false`: Q9 and Q10 answer
`:not-the-reading-family-route` on the canonical route, as on every run of
this route; the clause requires only that the check ran).
-/

namespace DarkTower.WarMachine.ReadingEraClickPrediction

/-! ## Field vocabularies -/

/-- R1/R2.  SEL `[:payload :judgment :reading-preparation]` (C4b).  `:status
:not-run` is `notRun`; `:status :ran` is `ran` with the counts of
`:attempted`, `:refused` and `:pending` (all vectors of target ids; `:refused`
is the subset of `:attempted` that did not publish). -/
inductive Preparation where
  | notRun
  | ran (attempted refused pending : Nat)
  deriving DecidableEq, Repr

/-- R3.  RR `[:outer-task-selection :q8-frontier :schema]`: `outerV1` when it
is `:wm/q8-outer-frontier-v1` (Q8a); `stub` when the key is absent (the era's
`{:status :certified :carrier {:q2 :q4 :q8}}`). -/
inductive FrontierSchema where
  | stub
  | outerV1
  deriving DecidableEq, Repr

/-- R3.  RR `[:outer-task-selection :q8-frontier :status]`. -/
inductive FrontierStatus where
  | certified
  | decidedFailure
  | notRecomputable
  deriving DecidableEq, Repr

/-- R6.  RR `[:outer-task-selection :policy :status]`; for `:refused`, whether
`:reason` is the producer's own reason and whether `:details` is present. -/
inductive PolicyOutcome where
  | selected
  | refused (reasonCarried detailsCarried : Bool)
  deriving DecidableEq, Repr

/-- R8.  TO `[:pattern-comparison :status]`: `absent` when the key is missing
(pre-wiring), else `:refused` or `:compared`. -/
inductive ComparisonStatus where
  | absent
  | refused
  | compared
  deriving DecidableEq, Repr

/-- R10.  RR `[:runner/source :runner/source-check]`. -/
inductive SourceCheck where
  | current
  | drift
  | unavailable
  deriving DecidableEq, Repr

/-- R11.  REQ: `notChecked` when the file is absent; `checked b` with `b` the
file's `:conforms`. -/
inductive RequirementsRecord where
  | notChecked
  | checked (conforms : Bool)
  deriving DecidableEq, Repr

/-- R11.  CS `[:child]`: absent is `noChild`; `[:child :completion :status]`
`"pending"` is `pending`; `"complete"` with `[:child :completion :verdict
:status]` `:passed` or `:failed` is `completeWithVerdict`, with `:not-checked`
is `completeNotChecked`. -/
inductive ChildBinding where
  | noChild
  | pending
  | completeWithVerdict
  | completeNotChecked
  deriving DecidableEq, Repr

/-- R13.  RR `[:outer-task-selection :policy :selection-draw]`: `{:status
:sealed :seed :u}` is `sealed`; `{:absent :no-seed}` is `absent`; the key
missing while `[:outer-task-selection :policy :selected-outer-cascade-policy
:canonical-selection :draw :u]` is present is `outputOnly` (the era's shape). -/
inductive DrawRecord where
  | absent
  | sealed
  | outputOnly
  deriving DecidableEq, Repr

/-- R17.  RR `[:decision :selection-certificate :q6 :status]`: key absent is
`absent`; `:not-triggered`, `:not-recomputable`, `:excluded` as named;
`refused` when `[:outer-task-selection :policy :status]` is `:refused` with
kind `:repeat-choice-after-refusal`. -/
inductive Q6Carrier where
  | absent
  | notTriggered
  | notRecomputable
  | excluded
  | refused
  deriving DecidableEq, Repr

/-- R18.  RR `[:q6 :predecessor :status]` and `:reason`: `:present` is
`present`; `:absent` is `absent`; `:not-recomputable` with reason
`:previous-terminal-carrier-tampered` is `legacySeal` when the previous run's
closed event in `run-stream.edn` predates the R18 merge (`0cf37bdfb`,
2026-10-26T06:22Z) and `tampered` otherwise; any other `:not-recomputable`
reason is `notRecomputableOther`. -/
inductive PredecessorRead where
  | present
  | absent
  | legacySeal
  | tampered
  | notRecomputableOther
  deriving DecidableEq, Repr

/-! ## The record -/

/-- The observable fields of one ordinary click on the canonical route. -/
structure ClickRecord where
  /-- R1.  RR `[:outer-task-selection :policy-field :families]`: the number of
  families whose `:failures` carry `:no-current-target-reading`. -/
  unmetReadings : Nat
  /-- R1/R2.  SEL `[:payload :judgment :reading-preparation]`; `none` when the
  key is absent. -/
  preparation : Option Preparation
  /-- R3.  See `FrontierSchema`. -/
  frontierSchema : FrontierSchema
  /-- R3.  See `FrontierStatus`. -/
  frontierStatus : FrontierStatus
  /-- R3.  RR `[:outer-task-selection :q8-frontier :census :eligible]` count;
  for the stub, the count of `[:outer-task-selection :support]`. -/
  frontierEligible : Nat
  /-- R3.  RR `[:outer-task-selection :q8-frontier :entries]` count; for the
  stub, the count of `[:outer-task-selection :q8-frontier :carrier :q4]`. -/
  frontierRanked : Nat
  /-- R3.  RR `[:outer-task-selection :q8-frontier :unranked]` count (0 for the
  stub, which has no such section). -/
  frontierUnranked : Nat
  /-- R12.  RR `[:outer-task-selection :q8-frontier :unranked]`: the number of
  rows whose `:reason` is in `[:census-verdict :ranked-kinds]`; `none` when the
  carrier has no `:unranked` section or no `:ranked-kinds` (the stub, or a
  `:census-verdict {:status :pass}`). -/
  unrankedHeadlinesInRankedKinds : Option Nat
  /-- R4.  RR `[:decision :selection-certificate :policy-stages <chosen>]`:
  `(constructed, scored, posterior)` key counts; `none` when the key is absent. -/
  policyStages : Option (Nat × Nat × Nat)
  /-- R4.  RR `[:decision :selection-certificate :stage-provenance]`: the number
  of pins present (`:menu-pin`, `:frontier-pin`, `:q4-pin`); 0 when absent. -/
  stageProvenancePins : Nat
  /-- R6.  See `PolicyOutcome`. -/
  policy : PolicyOutcome
  /-- R7.  RR `[:decision :selection-certificate :pattern-prediction-input
  :status]` is `:present`. -/
  predictionInputPresent : Bool
  /-- R7.  TO `[:prediction :status]` is `:frozen`. -/
  predictionFrozen : Bool
  /-- R8.  TO `[:prediction :wanted]`: the number of tokens whose second element
  is `:pattern-done`. -/
  patternPredictions : Nat
  /-- R8/R8a.  TO `[:pattern-observations :rows]` count; `none` when
  `:pattern-observations` is absent. -/
  patternRows : Option Nat
  /-- R8.  See `ComparisonStatus`. -/
  patternComparison : ComparisonStatus
  /-- R8a.  TO `[:pattern-observations :rows]`: rows whose `:observed` is a
  Boolean. -/
  patternRowsBoolean : Nat
  /-- R8a.  TO `[:pattern-observations :rows]`: rows whose `:observed` is
  `{:status :missing :reason :completion-check-not-executable}`. -/
  patternRowsNotExecutable : Nat
  /-- R8.  TO `[:tokens]` (the mission comparison): rows for a `:pattern-done`
  token whose `:observed` is a Boolean, i.e. a pattern prediction scored
  against a mission measurement. -/
  patternTokensScoredAgainstMission : Nat
  /-- R10.  See `SourceCheck`. -/
  sourceCheck : SourceCheck
  /-- R10.  RR `[:runner/source :namespaces]`: entries with `:status :stale`. -/
  staleNamespaces : Nat
  /-- R11.  See `RequirementsRecord`. -/
  requirements : RequirementsRecord
  /-- R11.  See `ChildBinding`. -/
  selfHealChild : ChildBinding
  /-- R13.  RR `[:outer-task-selection :q8-frontier :selection-verdict :reason]`
  is `:tied-minimum`, equivalently `[:outer-task-selection :policy
  :selected-outer-cascade-policy :canonical-selection :draw :candidates]` has
  more than one digest. -/
  tie : Bool
  /-- R13.  See `DrawRecord`. -/
  selectionDraw : DrawRecord
  /-- R17.  See `Q6Carrier`. -/
  q6Carrier : Q6Carrier
  /-- R18.  See `PredecessorRead`. -/
  predecessor : PredecessorRead
  deriving DecidableEq, Repr

/-! ## The clauses -/

/-- The defect lines with a single-click observable. -/
inductive Clause where
  | r1 | r2 | r3 | r4 | r6 | r7 | r8 | r8a | r10 | r11 | r12 | r13 | r17 | r18
  deriving DecidableEq, Repr

def Clause.all : List Clause :=
  [.r1, .r2, .r3, .r4, .r6, .r7, .r8, .r8a, .r10, .r11, .r12, .r13, .r17, .r18]

/-- The per-click budget of the bounded preparation batch
(`full_loop_runtime.clj`, `(min 3 (max 1 (count needs)))`). -/
def preparationBudget : Nat := 3

/-- R1.  With unmet reading needs the batch ran, attempted at least one, spent
at most the budget, and deferred only once the budget was spent
(a refusal spends a slot; `:refused` is
a subset of `:attempted` in the C4a projection, so `attempted` is the spent
count). -/
def r1Holds (r : ClickRecord) : Bool :=
  r.unmetReadings == 0 ||
    match r.preparation with
    | some (.ran attempted _ pending) =>
        0 < attempted && attempted ≤ preparationBudget &&
          (pending == 0 || attempted == preparationBudget)
    | _ => false

/-- R2.  The preparation outcome is present and typed; absence is not a value. -/
def r2Holds (r : ClickRecord) : Bool := r.preparation.isSome

/-- R3.  The Q8 carrier is the Q8a outer frontier, it is recomputable, and its
ranked and unranked tasks together are the eligible census. -/
def r3Holds (r : ClickRecord) : Bool :=
  r.frontierSchema == .outerV1 && r.frontierStatus != .notRecomputable &&
    r.frontierRanked + r.frontierUnranked == r.frontierEligible

/-- R4.  The chosen target's policy stages are present with provenance, and
posterior ⊆ scored ⊆ constructed with a non-empty posterior (counts). -/
def r4Holds (r : ClickRecord) : Bool :=
  match r.policyStages with
  | some (c, s, p) => 0 < p && p ≤ s && s ≤ c && 0 < r.stageProvenancePins
  | none => false

/-- R6.  A policy refusal carries the producer's reason and its cause
(`SeamRefusal.lean`, `Carries`); a selection has nothing to carry. -/
def r6Holds (r : ClickRecord) : Bool :=
  match r.policy with
  | .selected => true
  | .refused reason details => reason && details

/-- R7.  The prediction input is part of the sealed admission and the
prediction is frozen before comparison (`AdmissionInputs.lean`). -/
def r7Holds (r : ClickRecord) : Bool := r.predictionInputPresent && r.predictionFrozen

/-- R8.  Pattern predictions are compared in their own domain, one supplied row
per pattern prediction, and none is scored against a mission measurement
(`AdmissionInputs.lean`, `Measurable`). -/
def r8Holds (r : ClickRecord) : Bool :=
  r.patternComparison == .compared && r.patternRows == some r.patternPredictions &&
    r.patternTokensScoredAgainstMission == 0

/-- R8a.  Today every authored completion check is prose, so no row carries a
Boolean and every row is `:completion-check-not-executable`
(`PatternObservationAdmission.lean`, `prose_row_not_admitted`).  A Boolean row
on this click would mean a locator-form check was authored without the
compiler change the list records as still open. -/
def r8aHolds (r : ClickRecord) : Bool :=
  r.patternRowsBoolean == 0 && r.patternRows == some r.patternRowsNotExecutable

/-- R10.  The loaded composition is current: the record binds loaded hashes equal
to the disk hashes and no namespace is stale (`ClickRecordBinding.lean`). -/
def r10Holds (r : ClickRecord) : Bool :=
  r.sourceCheck == .current && r.staleNamespaces == 0

/-- R11.  The requirements check ran on the record (not checked is not passed),
and any self-heal child's completion carries a verdict into the parent
(`ClickRecordBinding.lean`, `parentVerdict`). -/
def r11Holds (r : ClickRecord) : Bool :=
  r.requirements != .notChecked &&
    r.selfHealChild != .pending && r.selfHealChild != .completeNotChecked

/-- R12.  No unranked task's headline reason is a kind a ranked task also
carries, and the carrier says so (`FrontierCoverage.Discriminating`). -/
def r12Holds (r : ClickRecord) : Bool := r.unrankedHeadlinesInRankedKinds == some 0

/-- R13.  A tie is broken only by a sealed draw (`SelectionDraw.lean`). -/
def r13Holds (r : ClickRecord) : Bool := !r.tie || r.selectionDraw == .sealed

/-- R17.  The canonical route produces a Q6 carrier, and the first repaired run
cannot exclude: its predecessor wrote no canonical input digest. -/
def r17Holds (r : ClickRecord) : Bool :=
  r.q6Carrier != .absent && r.q6Carrier != .excluded && r.q6Carrier != .refused

/-- R18.  A seal made by the fixed digest verifies; a predecessor read as
tampered is only the legacy seal, and that read is carried into the Q6
carrier unchanged. -/
def r18Holds (r : ClickRecord) : Bool :=
  r.predecessor != .tampered &&
    (r.predecessor != .legacySeal || r.q6Carrier == .notRecomputable)

def Clause.holds (c : Clause) (r : ClickRecord) : Bool :=
  match c with
  | .r1 => r1Holds r | .r2 => r2Holds r | .r3 => r3Holds r | .r4 => r4Holds r | .r6 => r6Holds r
  | .r7 => r7Holds r | .r8 => r8Holds r | .r8a => r8aHolds r | .r10 => r10Holds r | .r11 => r11Holds r
  | .r12 => r12Holds r | .r13 => r13Holds r | .r17 => r17Holds r | .r18 => r18Holds r

/-- The clauses a record fails, in list order. -/
def failing (r : ClickRecord) : List Clause := Clause.all.filter (fun c => !c.holds r)

def predicted (r : ClickRecord) : Bool := Clause.all.all (fun c => c.holds r)

/-- The prediction: every clause holds of the record. -/
def Predicted (r : ClickRecord) : Prop := predicted r = true

instance (r : ClickRecord) : Decidable (Predicted r) := by
  unfold Predicted
  infer_instance

theorem predicted_iff_no_failing (r : ClickRecord) : Predicted r ↔ failing r = [] := by
  unfold Predicted predicted failing
  simp [List.all_eq_true, List.filter_eq_nil_iff]

/-! ## The prediction -/

/-- The record the first click is predicted to write.  Forced values are
explained in the module docstring; the counts are the expected values. -/
def predictedRecord : ClickRecord where
  unmetReadings := 101
  preparation := some (.ran 3 0 98)
  frontierSchema := .outerV1
  frontierStatus := .decidedFailure
  frontierEligible := 109
  frontierRanked := 4
  frontierUnranked := 105
  unrankedHeadlinesInRankedKinds := some 0
  policyStages := some (1, 1, 1)
  stageProvenancePins := 3
  policy := .selected
  predictionInputPresent := true
  predictionFrozen := true
  patternPredictions := 2
  patternRows := some 2
  patternComparison := .compared
  patternRowsBoolean := 0
  patternRowsNotExecutable := 2
  patternTokensScoredAgainstMission := 0
  sourceCheck := .current
  staleNamespaces := 0
  requirements := .checked false
  selfHealChild := .noChild
  tie := true
  selectionDraw := .sealed
  q6Carrier := .notRecomputable
  predecessor := .legacySeal

theorem predicted_holds : Predicted predictedRecord := by decide

theorem predicted_fails_nothing : failing predictedRecord = [] := by decide

/-! ## Control: attempt-002 of machinery-150 (run `2026-10-24-25e24e8b…`)

Read from the files named in the field docstrings on 2026-10-26.

* 101 of 109 families fail `:no-current-target-reading`; SEL has no
  `:reading-preparation` key (R1, R2).
* `[:outer-task-selection :q8-frontier]` is `{:status :certified :carrier
  {:q2 :q4 :q8}}` with no schema, four `:q4` rows, 109 support ids, no
  `:unranked` section (R3, R12).
* `[:decision :selection-certificate]` has no `:policy-stages`,
  `:stage-provenance` or `:q6` (R4, R17).
* `[:outer-task-selection :policy :status]` is `:selected` (R6).
* `:pattern-prediction-input :status` is `:present`; TO `[:prediction :status]`
  is `:frozen` (R7).
* TO `[:prediction :wanted]` has two `:pattern-done` tokens; `:tokens` scores
  both as `:observation-missing` against the six mission-hole measurements;
  no `:pattern-observations` or `:pattern-comparison` key (R8, R8a).
* `[:runner/source :runner/source-check]` is `:current`, no stale namespace
  (R10).
* No `.requirements.edn` beside the run record; the click was itself the
  self-heal child and its own state binds no child (R11).
* The canonical draw has two candidates at G `-3.9560226735640867`
  (wiring, bindings) and its `:u` lives only in the output; no
  `:selection-draw` key (R13).
* `[:q6 :predecessor :status]` is `:present` (the run before it, outcome
  `:already-satisfied`) (R18). -/
def attempt002Record : ClickRecord where
  unmetReadings := 101
  preparation := none
  frontierSchema := .stub
  frontierStatus := .certified
  frontierEligible := 109
  frontierRanked := 4
  frontierUnranked := 0
  unrankedHeadlinesInRankedKinds := none
  policyStages := none
  stageProvenancePins := 0
  policy := .selected
  predictionInputPresent := true
  predictionFrozen := true
  patternPredictions := 2
  patternRows := none
  patternComparison := .absent
  patternRowsBoolean := 0
  patternRowsNotExecutable := 0
  patternTokensScoredAgainstMission := 0
  sourceCheck := .current
  staleNamespaces := 0
  requirements := .notChecked
  selfHealChild := .noChild
  tie := true
  selectionDraw := .outputOnly
  q6Carrier := .absent
  predecessor := .present

theorem attempt002_not_predicted : ¬ Predicted attempt002Record := by decide

/-- The clauses attempt-002 fails: no preparation (R1, R2), the stub frontier
(R3, R12), no policy stages (R4), no pattern-domain comparison (R8, R8a), no
requirements check (R11), a tie broken by an unsealed draw (R13), no Q6
carrier (R17).  It passes R6, R7, R10 and R18. -/
theorem attempt002_failing_clauses :
    failing attempt002Record =
      [.r1, .r2, .r3, .r4, .r8, .r8a, .r11, .r12, .r13, .r17] := by decide

/-! ## Controls on the prediction's own edges -/

/-- A click whose predecessor terminal was sealed after the fix and still reads
as tampered is a finding, not the legacy seal. -/
theorem fresh_seal_read_tampered_not_predicted :
    ¬ Predicted { predictedRecord with predecessor := .tampered } := by decide

/-- The legacy-seal read must reach the Q6 carrier unchanged; a carrier that
says `:not-triggered` beside a tampered predecessor read would be a consumer
renaming a producer's refusal (R6's shape at the Q6 seam). -/
theorem legacy_seal_with_not_triggered_carrier_not_predicted :
    ¬ Predicted { predictedRecord with q6Carrier := .notTriggered } := by decide

/-- A Boolean pattern row on this click contradicts the authored checks being
prose; it would be a finding. -/
theorem boolean_row_not_predicted :
    ¬ Predicted { predictedRecord with patternRowsBoolean := 1,
                                       patternRowsNotExecutable := 1 } := by decide

/-- A tie with the draw absent (no seed) is the refusal R13 installed. -/
theorem unsealed_tie_not_predicted :
    ¬ Predicted { predictedRecord with selectionDraw := .absent } := by decide

/-- Without a tie the draw is not needed. -/
theorem untied_click_needs_no_draw :
    Predicted { predictedRecord with tie := false, selectionDraw := .absent } := by decide

/-- A preparation batch that attempted two with needs left over stopped short
of its budget (the `m150OneAttemptedOneRefused` shape). -/
theorem short_batch_not_predicted :
    ¬ Predicted { predictedRecord with preparation := some (.ran 2 1 99) } := by decide

/-- The batch may spend its budget on refusals. -/
theorem refusals_spend_the_budget :
    Predicted { predictedRecord with preparation := some (.ran 3 3 98) } := by decide

/-- A frontier whose ranked and unranked tasks do not exhaust the census is
rejected by the recorded frontier-coverage check. -/
theorem uncovered_frontier_not_predicted :
    ¬ Predicted { predictedRecord with frontierUnranked := 104 } := by decide

/-- A requirements file whose verdicts do not all hold is still a checked
record; the clause is about checking, not conformance. -/
theorem conforming_requirements_also_predicted :
    Predicted { predictedRecord with requirements := .checked true } := by decide

theorem unchecked_requirements_not_predicted :
    ¬ Predicted { predictedRecord with requirements := .notChecked } := by decide

/-- A self-heal child that completed without a verdict is the m150 parent
shape; a bound child with a verdict is admitted. -/
theorem child_without_verdict_not_predicted :
    ¬ Predicted { predictedRecord with selfHealChild := .completeNotChecked } := by decide

theorem child_with_verdict_predicted :
    Predicted { predictedRecord with selfHealChild := .completeWithVerdict } := by decide

/-- The predicted record differs from attempt-002 exactly on the repaired
lines: it is not a transcription of the control. -/
theorem prediction_is_not_the_control : predictedRecord ≠ attempt002Record := by decide

#print axioms predicted_holds
#print axioms attempt002_not_predicted
#print axioms attempt002_failing_clauses
#print axioms predicted_iff_no_failing


/-! ## The first click as observed (run `2026-10-26-8be8ff03…`, 09:48Z)

Read from the files named in the field docstrings by claude-9
(`~/notes/wm-next/outer-selection/first-click-2026-10-26/observed.lean`).
It matched `predictedRecord` on every clause but R11.  The counts differ from
the expected values (102 unmet, 110 eligible, 3 ranked, 3 pattern predictions,
no tie) without failing a clause, as the module docstring allowed.  R11 failed
because of the click script, not the machine (R19): `wm_click.sh` gave up on
the 107 s admission POST and never ran the requirements checker, so REQ was
absent and `requirements` reads `notChecked`.  R19 was repaired in
`1d81bfb3d`; R21a/b/c brought the hold to about 1.5 s. -/
def firstClickRecord : ClickRecord where
  unmetReadings := 102
  preparation := some (.ran 3 0 100)
  frontierSchema := .outerV1
  frontierStatus := .decidedFailure
  frontierEligible := 110
  frontierRanked := 3
  frontierUnranked := 107
  unrankedHeadlinesInRankedKinds := some 0
  policyStages := some (1, 1, 1)
  stageProvenancePins := 3
  policy := .selected
  predictionInputPresent := true
  predictionFrozen := true
  patternPredictions := 3
  patternRows := some 3
  patternComparison := .compared
  patternRowsBoolean := 0
  patternRowsNotExecutable := 3
  patternTokensScoredAgainstMission := 0
  sourceCheck := .current
  staleNamespaces := 0
  requirements := .notChecked
  selfHealChild := .noChild
  tie := false
  selectionDraw := .sealed
  q6Carrier := .notRecomputable
  predecessor := .legacySeal

/-- The first click's single finding: the requirements check did not run
(R19, the click script). -/
theorem firstClick_failing : failing firstClickRecord = [.r11] := by decide

/-! ## The prediction for the second click

The second click is the first whose Q6 predecessor is a run sealed by the
fixed digest (R18), and the first after a click that published readings.
Values forced by the state on 2026-10-26 (claude-9, checked live
13:30Z–13:36Z; probe `second-click-2026-10-26/readings-probe.clj`):

* `unmetReadings` 99: the first click's preparation published three readings
  (`M-G-over-cascades` 08:57:27Z, `M-daily-scan` 08:59:51Z,
  `M-daily-scan-multi-axis-queue` 09:02:26Z), all `:current-candidate` in
  `storage/wm-target-readings`; the first click read 102 unmet.
* `preparation` `ran 3 0 97`: budget 3; 100 needs now, 97 pending after the
  batch.  The next three in pending order are `M-distributed-frontiermath`,
  `M-war-machine-aif-last-mile`, `M-essays-edit-cycle`.
* Frontier: the route is unchanged, the census is 110 as on the first click,
  and the three scored families of the first click are still the scored ones
  (self-improvement-loop −3.944, stack-geometry −2.004,
  recommendation-bindings −3.956), so 3 ranked and 107 unranked.  The ranked
  count is unforced upward: the three newly read targets may build scoring
  families (their families on the first click failed only on
  `:no-current-target-reading`, but seed-not-in-graph, isolated-seed and
  void-pattern-citation are seen on other read targets).  A record with 4–6
  ranked and the unranked count reduced to match fails no clause.
* Pattern domain: 3 predictions, 3 rows, all prose, as on the first click for
  `M-recommendation-bindings`; unforced if another target wins.  R8b's one
  locator clause (`req_f7374bcce` occurrence 0) belongs to the
  `M-war-machine-wiring` reading, which is unread (pending), so it cannot be
  on this click's rows.
* `sourceCheck` current, no stale namespace: drift `{:drift [] :registered
  112}` at 13:36Z, to be re-probed before the click.
* `requirements` `checked false`: the script now writes REQ after the POST
  recovery (R19 repaired); the verdict is as on the first click (Q1 and Q5
  hold, Q7 violated, the rest unverifiable, `:conforms false`).  This is the
  field that turns R11 from failing to holding.
* `tie` false: three scored rows with distinct G and no new row predicted; the
  draw is sealed regardless (R13).
* `predecessor` present: `previous-run/predecessor` at 13:33Z reads
  `{:status :present :previous-run/id "2026-10-26-8be8ff03-…"}`; the first
  click's terminal was sealed by the server after R18 and the seal verifies.
* `q6Carrier` notTriggered: `decide-exclusion` (`previous_run.clj`) finds the
  predecessor present and its outcome `:invalid` (raw `:grounded-progress`,
  R22 in DEFECTS) not `:refused`, so `{:status :not-triggered :reason
  :previous-outcome-not-refused}`.

The predicted choice (not a field): the same policy as the first click,
`M-recommendation-bindings/policy-7e8a0806fea29fa47914`, canonical G
−3.9560226735640867, because nothing excludes it and the three scored G are
unchanged.  A lower G from a newly read family would move it. -/
def predictedRecord2 : ClickRecord where
  unmetReadings := 99
  preparation := some (.ran 3 0 97)
  frontierSchema := .outerV1
  frontierStatus := .decidedFailure
  frontierEligible := 110
  frontierRanked := 3
  frontierUnranked := 107
  unrankedHeadlinesInRankedKinds := some 0
  policyStages := some (1, 1, 1)
  stageProvenancePins := 3
  policy := .selected
  predictionInputPresent := true
  predictionFrozen := true
  patternPredictions := 3
  patternRows := some 3
  patternComparison := .compared
  patternRowsBoolean := 0
  patternRowsNotExecutable := 3
  patternTokensScoredAgainstMission := 0
  sourceCheck := .current
  staleNamespaces := 0
  requirements := .checked false
  selfHealChild := .noChild
  tie := false
  selectionDraw := .sealed
  q6Carrier := .notTriggered
  predecessor := .present

theorem predicted2_holds : Predicted predictedRecord2 := by decide

/-- What the second click is predicted to show that the first did not: the
read set grew by the batch, the requirements check ran, and the Q6 predecessor
was read through a verifying seal and found not to trigger.  Every other
field is the first click's. -/
theorem second_click_changes :
    predictedRecord2 =
      { firstClickRecord with
          unmetReadings := 99
          preparation := some (.ran 3 0 97)
          requirements := .checked false
          q6Carrier := .notTriggered
          predecessor := .present } := rfl

/-- The unforced upward edge: newly read targets building scoring families
fails no clause. -/
theorem more_ranked_families_also_predicted :
    Predicted { predictedRecord2 with frontierRanked := 6, frontierUnranked := 104 } := by
  decide

#print axioms firstClick_failing
#print axioms predicted2_holds
#print axioms second_click_changes

/-! ## The prediction for the third click

The second click (`wm-click-b56496c7…`, 13:43Z) produced no record: `route!`
found entry 45 open in the durable injury ledger and refused before ordinary
selection (R23).  No field of `ClickRecord` reads that ledger, so
`predictedRecord2` could neither hold nor fail.  Entry 45 was retired at
15:18Z by a medic operation (`263dcf88…`), the close-image law and the medic
replay value landed (`CloseOutcomeImage`, `HistoricalMisclassificationCorrection`),
and the ledger gate and terminal effect are predicted beside this record in
`ReadingEraClickLedgerPrediction`.  The record itself is unchanged from the
second click's prediction.  The five fields `second_click_changes` names keep
their click-2 values, as checked live by claude-9 (15:21Z–15:27Z):

* `unmetReadings` 99: no reading has been published since click 1's three
  (newest `M-daily-scan-multi-axis-queue` 09:02:26Z; a `find -newermt
  2026-10-26T09:03:00Z` over `storage/wm-target-readings` is empty); click 2
  refused before preparation ran, so it published none.
* `preparation` `ran 3 0 97`: 100 needs, budget 3.
* `requirements` `checked false`: R19 repaired; the verdict as on click 1.
* `q6Carrier` `notTriggered`: the predecessor is still run
  `2026-10-26-8be8ff03…` (click 2 wrote no stream event; its requested run id
  `c26b309e` is absent from `run-stream.edn`).  Its sealed terminal carrier
  reads `:outcome :invalid :raw :grounded-progress` (live
  `previous-run/predecessor`, 15:25Z).  The R22 map at futon2 `aa8bf5ed5`
  (`lean-outcomes` now sends `:grounded-progress` to `:changed`) applies to
  closes sealed after it; the stream is left as written.  `decide-exclusion`
  (`previous_run.clj`) sees an outcome that is not `:refused` either way and
  answers `{:status :not-triggered :reason :previous-outcome-not-refused}`.
* `predecessor` `present`: as above.

Every other field as in `predictedRecord2`, with the same unforced edges
(`more_ranked_families_also_predicted` still covers 4–6 ranked).  Drift
`{:drift [] :registered 112}` at 15:23Z; the three futon2 src commits since
the click-2 probe (`aa8bf5ed5`, `5d8b19443`, `ad0c99054`) were each reloaded
into :7070 after review. -/
def predictedRecord3 : ClickRecord := predictedRecord2

theorem predicted3_holds : Predicted predictedRecord3 := by decide

/-- The third click is predicted to show the 27 fields of the second click's
prediction; what it shows that the second could not is outside the fields
(`ReadingEraClickLedgerPrediction`). -/
theorem third_click_record_unchanged : predictedRecord3 = predictedRecord2 := rfl

#print axioms predicted3_holds
#print axioms third_click_record_unchanged

/-! ## The prediction for the fourth click

The third click (`wm-click-9468efd5…`, run `2026-10-26-f444287e…`) reached
ordinary selection, chose the same policy as click 1, and the author answered
in the rule-7 grammar that the want already holds at base head `09a7cb8d…`.
The Agency's artifact-ref was the mission path, the classifier closed
`:build-failed :invalid-author-refusal`, and the terminal opened ledger entry
47 (R24, `AlreadySatisfiedArtifactRefSeam`).  Since then both halves of the
seam were repaired and reloaded (futon3c `6b1bb1358`, futon2 `097fd9f4c`) and
entry 47 was retired by entry 48 (medic operation `987e211a…`, 17:53Z).  The
close and the ledger are predicted in `ReadingEraClickLedgerPrediction`; this
is the record half.  Values forced by the state (claude-9, checked live
17:58Z–18:05Z; probes under `fourth-click-2026-10-26/`):

* `unmetReadings` 96: click 3's preparation published three readings
  (`M-distributed-frontiermath` 15:53:05Z, `M-war-machine-aif-last-mile`
  15:59:52Z, `M-essays-edit-cycle` 16:02:05Z), all `:current-candidate`
  beside click 1's three; click 3 read 99.
* `preparation` `ran 3 0 94`: 97 needs now, budget 3.
* Frontier 109 eligible, 3 ranked, 106 unranked: click 3's census was 109
  (click 2's prediction said 110; the census is unforced).  The ranked count
  is unforced upward as before (`more_ranked_families_also_predicted`).
* `sourceCheck` current, no stale namespace: drift `{:drift [] :registered
  112}` at 17:58Z; futon2 src at `097fd9f4c`, no src commit since.
* `predecessor` present: click 3's run, its closed event the last line of
  `run-stream.edn`.
* `q6Carrier` notTriggered: that event's `:q6 :outcome` is `{:status
  :present :outcome :invalid :raw :build-failed}`; `decide-exclusion`
  (`previous_run.clj` 216–217) answers `:not-triggered
  :previous-outcome-not-refused` for any outcome that is not `:refused`.
* `requirements` `checked false`, as click 3.
* The pattern domain: the predicted close is `:already-satisfied` at
  `:author-wait`, which builds nothing, so there is no after-revision cascade:
  TO `[:pattern-observations]` is `{:status :refused :kind
  :after-revision-missing}` and `[:pattern-comparison :status]` `:refused`,
  as click 3 showed.  So `patternRows` is `none`, `patternComparison`
  `refused`, `patternRowsNotExecutable` 0.

R8 and R8a are written for a close that builds (one supplied row per pattern
prediction, every row prose).  They fail on this record for that reason, and
the prediction says so rather than weakening the clauses:
`fourth_click_failing` names exactly those two, and
`rows_absent_fails_exactly_r8_r8a` says that is what any rowless record does
to this clause set, whatever its other fields.  `fourth_click_otherwise_predicted`
is the form `observed3.lean` used: with the rows a building close would
write, nothing fails.  The branch not predicted: if the author builds again
(click 1's shape), the close is `:grounded-progress`, the rows exist, and the
record is `predictedRecord4Building`, which differs from `predictedRecord3`
only on the two forced reading counts and the unforced census.  Either branch
is a non-injury at the terminal.

The predicted choice (not a field): the same policy and G as clicks 1 and 3,
unless a newly read family scores lower. -/
def predictedRecord4 : ClickRecord :=
  { predictedRecord3 with
      unmetReadings := 96
      preparation := some (.ran 3 0 94)
      frontierEligible := 109
      frontierRanked := 3
      frontierUnranked := 106
      patternRows := none
      patternComparison := .refused
      patternRowsNotExecutable := 0 }

/-- The fourth click is predicted to fail exactly the two pattern-domain
clauses, because the already-satisfied close builds nothing. -/
theorem fourth_click_failing : failing predictedRecord4 = [.r8, .r8a] := by decide

/-- The rows a building close writes, for any record: one supplied prose row
per pattern prediction, no Boolean row, nothing scored against the mission. -/
def withRows (r : ClickRecord) : ClickRecord :=
  { r with patternRows := some r.patternPredictions
           patternComparison := .compared
           patternRowsNotExecutable := r.patternPredictions
           patternRowsBoolean := 0
           patternTokensScoredAgainstMission := 0 }

/-- The failing clauses outside an excluded set. -/
def failingOutside (excl : List Clause) (r : ClickRecord) : List Clause :=
  (failing r).filter (fun c => !excl.contains c)

/-- No clause but R8 and R8a reads the pattern-domain fields. -/
theorem holds_withRows (r : ClickRecord) (c : Clause) (h8 : c ≠ .r8) (h8a : c ≠ .r8a) :
    c.holds (withRows r) = c.holds r := by
  cases c <;> first | exact absurd rfl h8 | exact absurd rfl h8a | rfl

/-- The reason, in general: a record without pattern rows fails R8 and R8a,
and outside those two it fails exactly what it would fail with the rows a
building close writes.  So `fourth_click_failing` is the prediction for every
field but the two the close leaves empty. -/
theorem rows_absent_fails_exactly_r8_r8a (r : ClickRecord) (h : r.patternRows = none) :
    Clause.r8 ∈ failing r ∧ Clause.r8a ∈ failing r ∧
      failingOutside [.r8, .r8a] r = failingOutside [.r8, .r8a] (withRows r) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [failing, Clause.all, List.mem_filter, Clause.holds, r8Holds, h]
  · simp [failing, Clause.all, List.mem_filter, Clause.holds, r8aHolds, h]
  · unfold failingOutside failing
    simp only [List.filter_filter]
    apply List.filter_congr
    intro c _
    cases c <;> rfl

/-- `failingOutside` on the predicted record is empty: the exact list in
`fourth_click_failing` is the stronger statement, and this is its reading
over all other clauses. -/
theorem fourth_click_predicted_outside_rows :
    failingOutside [.r8, .r8a] predictedRecord4 = [] := by decide

/-- The form `observed3.lean` used: with the rows a building close writes,
every other clause holds. -/
theorem fourth_click_otherwise_predicted :
    failing { predictedRecord4 with patternRows := some 3, patternComparison := .compared,
                                     patternRowsNotExecutable := 3 } = [] := by decide

/-- The branch not predicted: the author builds again, the rows exist. -/
def predictedRecord4Building : ClickRecord :=
  { predictedRecord4 with patternRows := some 3, patternComparison := .compared,
                           patternRowsNotExecutable := 3 }

theorem predicted4Building_holds : Predicted predictedRecord4Building := by decide

/-- The building branch differs from the third click's prediction only on the
reading counts the batch forced and the unforced census: it is not
`predictedRecord3`, as the packet's shorthand had it. -/
theorem fourth_click_building_changes :
    predictedRecord4Building =
      { predictedRecord3 with
          unmetReadings := 96
          preparation := some (.ran 3 0 94)
          frontierEligible := 109
          frontierUnranked := 106 } := rfl

/-- What the fourth click is predicted to show that the third's prediction did
not: three more targets read, and the rowless pattern domain of a close that
builds nothing. -/
theorem fourth_click_changes :
    predictedRecord4 =
      { predictedRecord3 with
          unmetReadings := 96
          preparation := some (.ran 3 0 94)
          frontierEligible := 109
          frontierUnranked := 106
          patternRows := none
          patternComparison := .refused
          patternRowsNotExecutable := 0 } := rfl

/-- The unforced upward edge, on this record. -/
theorem fourth_click_more_ranked_also :
    failing { predictedRecord4 with frontierRanked := 6, frontierUnranked := 103 } =
      [.r8, .r8a] := by decide

/-- A Boolean row is still a finding on this click; its absence of rows is
not a licence. -/
theorem fourth_click_boolean_row_not_predicted :
    ¬ Predicted { predictedRecord4Building with
        patternRowsBoolean := 1
        patternRowsNotExecutable := 2 } := by decide

#print axioms fourth_click_failing
#print axioms holds_withRows
#print axioms rows_absent_fails_exactly_r8_r8a
#print axioms fourth_click_predicted_outside_rows
#print axioms fourth_click_otherwise_predicted
#print axioms predicted4Building_holds
#print axioms fourth_click_building_changes
#print axioms fourth_click_changes
#print axioms fourth_click_more_ranked_also
#print axioms fourth_click_boolean_row_not_predicted

end DarkTower.WarMachine.ReadingEraClickPrediction
