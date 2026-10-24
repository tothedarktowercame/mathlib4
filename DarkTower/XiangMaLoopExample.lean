import Mathlib
import DarkTower.TypedHole
import DarkTower.BV

/-!
# The 象+狗+馬 turn loop as a DarkTower object

This file states the live operator turn loop as a DarkTower-native apparatus
under `DarkTower/AIF-COMPLIANCE.md`, in the style of
`MetaCATokamakExample.lean`. The roles: 象 reads the operator's turn, 狗 is the
worker (the agent that does the turn's work), 馬 reports on what 狗 did, and the
operator's next turn is the outcome.

Source of truth: the inventory
`futon3c/holes/excursions/E-象-repl-cycle-inventory.md` (futon3c a97c01866),
not the four-phase picture in `E-象-repl-cycle.md`. The `Stage` enum follows the
inventory's §1 rows in running order, and the ports follow its §2 rows. Where
the inventory's line numbers had drifted, the docstrings cite the line the
function starts on in futon3c a97c01866.

One tick is one operator turn:

  `record ◁ render ◁ evaluate ◁ ((read ◁ ports ◁ alignment) ⅋ maObserve)`

Recurrence is external. Stage 8 (`nextTurn`) is the next operator turn: it is
stage 1 of the next tick, and the only explicit link back to this turn is the
`:reply_to` field it writes. It is a constructor of `Stage` (the inventory has
8 rows) but it is not an atom of `tick`; `nextTurn_not_in_tick` proves this.
Its feed into the next tick is the `outcomeJoin` port.

## What this file leaves out, and why

* **R9 conservation and abstain-fires.** This loop has no
  selection-with-scores stage yet. The render's BM25 ranking (stage 2) orders
  candidate patterns by a retrieval score; it is not an expected free energy,
  nothing normalises it into a policy, and nothing abstains on it. A
  conservation theorem over it would be vacuous, and under the
  statement-registry policy vacuous theorems are not stated. They are absent
  for that reason, not deferred as unfinished.
* **Belief / policy / precision `Fill`s** (checklist item 4) for the same
  reason: there is no belief update or policy over actions in the running
  loop to give a `holeType`.
* **CoolMemories and the Loop outcome join** are later packets. Here the join
  is only a port (`outcomeJoin`), graded as the inventory finds it.

## Satiety and partial feeds

`TypedHole.lean` offers five grades (`parse`, `payoff`, `canon`, `bundling`,
`role`) and no notion of a partially fed port. Following the tokamak and
`WMPipelineExample`, a fed port grades `canon` and a hungry one `payoff`. The
two partially fed ports (`xiangTags`, `outcomeJoin`) grade `payoff`, each with
a comment naming the partial feed: rounding them to fed would hide the gap.

Grounding:
* `futon3c/holes/excursions/E-象-repl-cycle-inventory.md` §1 (stages), §2
  (ports), §5 (where the running loop differs from the excursion);
* `DarkTower/AIF-COMPLIANCE.md` lines 135-144 (checklist);
* `DarkTower/MetaCATokamakExample.lean` (the idiom this file follows).
-/

namespace DarkTower

namespace XiangMaLoopExample

/-! ## Stages -/

/-- Stages of one operator turn, in running order (inventory §1). -/
inductive Stage where
  /-- 1. Record the operator turn, classical sentence split.
  `session-mode--analyze-start-turn` emacs/session-turn-analysis.el:1879
  (advice on `agent-chat--start-turn`); JVM `record-turn!`
  src/futon3c/xiang/turn_service.clj:820; segmentation `make-record`
  src/futon3c/xiang/turn_record.clj:425-445; 小象 draft `draft!`
  turn_service.clj:908. -/
  | record
  /-- 2. Prompt-line render: the proposed pattern set.
  `render!` src/futon3c/agency/prompt_line.clj:181; `write-proposed-patterns!`
  prompt_line.clj:150. Called from `prompt-facts-line`
  src/futon3c/transport/http.clj:5322 on every invoke whose body carries
  `:turn-record-id` (claude-repl.el:1067, codex-repl.el:3941, zai-repl.el:414).
  Each render appends one entry with its job id. -/
  | render
  /-- 3. Evaluate: 狗 works, replies, commits. This is 狗's stage.
  Reply capture `session-mode--note-reply-segment`
  emacs/session-turn-analysis.el:1662; turn end
  `session-mode--on-turn-finished` :1681; JVM `attach-happened!`
  turn_service.clj:935 (from transport/http.clj:12205 at turn finalisation);
  commit filter `filter-turn-commits` turn_service.clj:318; the turn-final
  evidence row `final-turn` src/futon3c/agency/turn_events.clj:47. -/
  | evaluate
  /-- 4. Read (象 proper). `dispatch!` turn_service.clj:1034, sent from
  `session-mode--dispatch-pending-turn` session-turn-analysis.el:1652 when
  the reply ENDS; `publish-analysis!` turn_service.clj:1373 →
  turn_store.clj:141; `settle-evidence!` turn_service.clj:472. -/
  | read
  /-- 5. Ports (HAPPENED / DIDN'T HAPPEN). `compute-ports!`
  turn_service.clj:710, scheduled by `settle-evidence!` (turn_service.clj:503);
  raises `{:event :ported}` (turn_service.clj:795). -/
  | ports
  /-- 6. Print (馬, part 1): the alignment reading. Listener on `:ported`
  registered by `start!` src/futon3c/xiang/ma_reading.clj:279; `align!`
  ma_reading.clj:246 writes `:alignment` (ma_reading.clj:260); wired live by
  src/futon3c/xiang/ma_reading_live.clj, required from transport/http.clj:86. -/
  | alignment
  /-- 7. Print (馬, part 2): observations and the agent card. Listener on
  turn-events `:post` src/futon3c/xiang/ma_observer.clj:54-59, running
  scripts/ma_observe.py once per session, only for agents in
  `~/code/data/minus40/ma-enabled.txt`. -/
  | maObserve
  /-- 8. Loop: the next operator turn. Stage 1 again; `:reply_to` resolved by
  `rt/resolve-targets` inside `record-turn!` (turn_service.clj:845-858).
  Not part of `tick`: it is the next tick's input. -/
  | nextTurn
  deriving DecidableEq, Fintype, Repr

/-! ## One tick

Order in the code:

* `record` runs at operator send and `render` at the start of the agent's
  invoke, so both precede `evaluate`.
* `read` does NOT precede `evaluate`. 象's reading is dispatched only at reply
  end (session-turn-analysis.el:1652, called from `on-turn-finished` :1681),
  so 象 reads the turn together with what 狗 did. The code runs it after
  `evaluate`, and so does `tick`.
* `ports` waits on settle (`settle-evidence!` schedules `compute-ports!`), and
  `alignment` waits on `:ported` and on `:ports_status` "computed"
  (ma_reading.clj:257), so `read ◁ ports ◁ alignment` is a `seq` chain.
* `maObserve` is a listener on the turn-final `:post` event
  (ma_observer.clj:54), which fires when `evaluate` finalises the turn. It
  does not wait for `read`, `ports` or `alignment`. The two 馬 outputs do not
  read each other: scripts/ma_observe.py reads no `:alignment` and no
  `.analysis.json`, and ma_reading.clj reads no `ma-observation` rows. So
  `maObserve` is held by `copar` against the whole `read ◁ ports ◁ alignment`
  chain. Placing it in `copar` with `alignment` alone would claim that it
  waits for `ports`, which the code does not do.
-/

/-- One operator turn as a BV process expression. -/
def tick : BV Stage :=
  BV.seq (BV.atom Stage.record)
    (BV.seq (BV.atom Stage.render)
      (BV.seq (BV.atom Stage.evaluate)
        (BV.copar
          (BV.seq (BV.atom Stage.read)
            (BV.seq (BV.atom Stage.ports) (BV.atom Stage.alignment)))
          (BV.atom Stage.maObserve))))

/-- The atoms of a BV expression, left to right. -/
def atoms : BV Stage → List Stage
  | BV.unit => []
  | BV.atom a => [a]
  | BV.dualAtom a => [a]
  | BV.seq S T => atoms S ++ atoms T
  | BV.copar S T => atoms S ++ atoms T
  | BV.par S T => atoms S ++ atoms T

/-- The tick runs stages 1-7, each once, in running order. -/
theorem tick_atoms :
    atoms tick = [Stage.record, Stage.render, Stage.evaluate, Stage.read,
      Stage.ports, Stage.alignment, Stage.maObserve] := rfl

/-- Recurrence is external: the next operator turn is not inside the tick. -/
theorem nextTurn_not_in_tick : Stage.nextTurn ∉ atoms tick := by
  decide

/-- Every other stage is inside the tick. -/
theorem stage_in_tick (s : Stage) (h : s ≠ Stage.nextTurn) : s ∈ atoms tick := by
  cases s <;> simp_all [tick_atoms]

/-- The 馬 observation leg is in `copar` with the 象 read chain, after
`evaluate`. -/
example : ∃ pre : BV Stage → BV Stage,
    tick = pre (BV.copar
      (BV.seq (BV.atom Stage.read)
        (BV.seq (BV.atom Stage.ports) (BV.atom Stage.alignment)))
      (BV.atom Stage.maObserve)) :=
  ⟨fun rest => BV.seq (BV.atom Stage.record)
    (BV.seq (BV.atom Stage.render) (BV.seq (BV.atom Stage.evaluate) rest)), rfl⟩

/-! ## Ports

One port per row of inventory §2, then 狗's output ports. 狗's ports are
requirements on the worker, checked after the turn by 馬; nothing in the tick
waits on them.
-/

/-- A per-pattern verdict: the vocabulary a verdict port would accept. -/
inductive PatternVerdict where
  | used
  | didntApply
  | missed
  deriving DecidableEq, Repr

/-- The apparatus ports: inventory §2 feeds, then 狗's outputs. -/
inductive Port where
  /-- Operator turn text: record `:source_text`. -/
  | operatorText
  /-- 象 tags of the turn: `.analysis.json` `:sentences`. -/
  | xiangTags
  /-- Proposed pattern set: record `:proposed_patterns`. -/
  | proposedPatterns
  /-- Agent reply: `:reply_text`. -/
  | agentReply
  /-- Commits: `:happened_summary` and trailer-credited `:commits`. -/
  | commits
  /-- 馬 card: evidence rows tagged `ma-observation`. -/
  | maCard
  /-- 馬 alignment reading: record `:alignment`. -/
  | maAlignment
  /-- Per-pattern verdict (`used` / `didn't-apply` / `missed`). -/
  | patternVerdict
  /-- Next-turn 象 tags as the outcome of this turn. -/
  | outcomeJoin
  /-- Memory write: the `e-xiang-turn-*` evidence row and scope edges. -/
  | memoryWrite
  /-- 狗 (a): names any injected memory or proposed pattern it used. -/
  | citesUsedMemory
  /-- 狗 (b): writes a durable finding to Minus40, or marks a candidate. -/
  | storesFinding
  /-- 狗 (c): proforma paragraph marks. -/
  | marksParagraphs
  /-- 狗 (d): commit trailers. -/
  | commitTrailers
  deriving DecidableEq, Fintype, Repr

/-- What fills each port. -/
def PortDirection : Port → Type
  | Port.operatorText => String
  | Port.xiangTags => List String
  | Port.proposedPatterns => List String
  | Port.agentReply => String
  | Port.commits => List String
  | Port.maCard => String
  | Port.maAlignment => List String
  | Port.patternVerdict => String × PatternVerdict
  | Port.outcomeJoin => List String
  | Port.memoryWrite => String
  | Port.citesUsedMemory => List String
  | Port.storesFinding => String
  | Port.marksParagraphs => List String
  | Port.commitTrailers => List String

/-- Satiety as fed today (inventory §2, "Fed today?"). -/
def satietyToday : Port → SatietyGrade
  | Port.operatorText => SatietyGrade.canon
  -- Partially fed: routine turns settle by the 小象 draft alone
  -- (`analysis_status "drafted"`) and bell turns are `declared` with no
  -- reading. No partial grade exists, so the port grades hungry.
  | Port.xiangTags => SatietyGrade.payoff
  -- Fed since 2026-10-19 (packet 1b); absent on earlier records.
  | Port.proposedPatterns => SatietyGrade.canon
  | Port.agentReply => SatietyGrade.canon
  | Port.commits => SatietyGrade.canon
  -- Fed for agents listed in ma-enabled.txt only.
  | Port.maCard => SatietyGrade.canon
  | Port.maAlignment => SatietyGrade.canon
  -- Not built: no per-pattern verdict vocabulary in src/, scripts/, emacs/;
  -- 馬's verdicts are per operator act.
  | Port.patternVerdict => SatietyGrade.payoff
  -- Partially fed: the join is positional (same session, `created_at` order)
  -- plus `:reply_to`; no field says "these tags are the outcome of turn n".
  | Port.outcomeJoin => SatietyGrade.payoff
  -- Fed for settled turns. The m40 fact store is not written; that gap is
  -- 狗's `storesFinding`, not this port.
  | Port.memoryWrite => SatietyGrade.canon
  -- Not fed: nothing asks 狗 to cite what it used, and nothing checks.
  | Port.citesUsedMemory => SatietyGrade.payoff
  -- Not fed: nothing in the loop writes the m40 fact store.
  | Port.storesFinding => SatietyGrade.payoff
  -- Fed: the CLAUDE.md proforma trial; stage 5 reads the marks.
  | Port.marksParagraphs => SatietyGrade.canon
  -- Fed: the prepare-commit-msg hook.
  | Port.commitTrailers => SatietyGrade.canon

/-- The apparatus interface for a given satiety assignment. -/
def apparatus (s : Port → SatietyGrade) : TypedHole where
  poly :=
    { A := Port
      B := PortDirection }
  satiety := s

/-- The apparatus as fed today. -/
def today : TypedHole := apparatus satietyToday

/-- A port is hungry when its satiety is the payoff grade (FirstFlights idiom). -/
def IsHungry (T : TypedHole) (a : T.poly.A) : Prop :=
  T.satiety a = SatietyGrade.payoff

/-- The apparatus is hungry when some port is. -/
def Hungry (s : Port → SatietyGrade) : Prop :=
  ∃ p : Port, IsHungry (apparatus s) p

instance (T : TypedHole) (a : T.poly.A) : Decidable (IsHungry T a) :=
  inferInstanceAs (Decidable (T.satiety a = SatietyGrade.payoff))

/-- The ports hungry today. -/
def hungryToday : List Port :=
  [Port.xiangTags, Port.patternVerdict, Port.outcomeJoin,
   Port.citesUsedMemory, Port.storesFinding]

/-- Exactly the listed ports are hungry today. A change to any grade in
`satietyToday` breaks this theorem. -/
theorem today_hungry_iff (p : Port) :
    IsHungry today p ↔ p ∈ hungryToday := by
  cases p <;> decide

/-! ## Starvation: the apparatus as fed today is hungry -/

/-- The per-pattern verdict port is hungry today: it is not built. -/
theorem today_patternVerdict_hungry : IsHungry today Port.patternVerdict := by
  decide

/-- 狗's port (a) is hungry today. -/
theorem today_citesUsedMemory_hungry : IsHungry today Port.citesUsedMemory := by
  decide

/-- 狗's port (b) is hungry today. -/
theorem today_storesFinding_hungry : IsHungry today Port.storesFinding := by
  decide

/-- The apparatus as fed today is hungry, witnessed by the verdict port. -/
theorem today_hungry : Hungry satietyToday :=
  ⟨Port.patternVerdict, today_patternVerdict_hungry⟩

/-! ## The built variant

`satietyBuilt` feeds the per-pattern verdict and 狗's ports (a) and (b). That
alone is not enough: the two partially fed ports stay hungry
(`threeOnly_still_hungry`). The built apparatus also completes them: 象 tags
on every turn (or an explicit declared-no-reading fill for bell turns), and an
explicit outcome join from turn n+1 to turn n.
-/

/-- Today's satiety with the verdict and 狗's (a), (b) fed, and nothing else
changed. -/
def satietyThreeOnly : Port → SatietyGrade
  | Port.patternVerdict => SatietyGrade.canon
  | Port.citesUsedMemory => SatietyGrade.canon
  | Port.storesFinding => SatietyGrade.canon
  | p => satietyToday p

/-- Feeding only the three named ports leaves the partial feeds hungry. -/
theorem threeOnly_still_hungry :
    IsHungry (apparatus satietyThreeOnly) Port.xiangTags ∧
    IsHungry (apparatus satietyThreeOnly) Port.outcomeJoin := by
  decide

/-- The built satiety: every port fed. -/
def satietyBuilt : Port → SatietyGrade := fun _ => SatietyGrade.canon

/-- The built apparatus is not hungry at any port. -/
theorem built_not_hungry_port (p : Port) : ¬ IsHungry (apparatus satietyBuilt) p := by
  simp [IsHungry, apparatus, satietyBuilt]

/-- The built apparatus is not hungry. -/
theorem built_not_hungry : ¬ Hungry satietyBuilt := by
  rintro ⟨p, hp⟩
  exact built_not_hungry_port p hp

/-! ## Negative control: severing one port alone

Start from the built apparatus and sever exactly one port. The bad case must
be caught: the apparatus is hungry, and the severed port is the witness.
-/

/-- Sever port `p` and leave every other port as it was. -/
def sever (s : Port → SatietyGrade) (p : Port) : Port → SatietyGrade :=
  fun q => if q = p then SatietyGrade.payoff else s q

/-- Severing any port of the built apparatus is caught at that port. -/
theorem sever_caught (p : Port) : IsHungry (apparatus (sever satietyBuilt p)) p := by
  simp [IsHungry, apparatus, sever]

/-- Severing a port touches no other port. -/
theorem sever_only (p q : Port) (h : q ≠ p) :
    ¬ IsHungry (apparatus (sever satietyBuilt p)) q := by
  simp [IsHungry, apparatus, sever, satietyBuilt, h]

/-- Each port hungry today, severed alone from the built apparatus, makes it
hungry. -/
theorem sever_patternVerdict_hungry :
    Hungry (sever satietyBuilt Port.patternVerdict) :=
  ⟨_, sever_caught Port.patternVerdict⟩

theorem sever_citesUsedMemory_hungry :
    Hungry (sever satietyBuilt Port.citesUsedMemory) :=
  ⟨_, sever_caught Port.citesUsedMemory⟩

theorem sever_storesFinding_hungry :
    Hungry (sever satietyBuilt Port.storesFinding) :=
  ⟨_, sever_caught Port.storesFinding⟩

theorem sever_xiangTags_hungry :
    Hungry (sever satietyBuilt Port.xiangTags) :=
  ⟨_, sever_caught Port.xiangTags⟩

theorem sever_outcomeJoin_hungry :
    Hungry (sever satietyBuilt Port.outcomeJoin) :=
  ⟨_, sever_caught Port.outcomeJoin⟩

/-- The severed apparatus is hungry ONLY at the severed port: the witness is
forced, so the control cannot pass on some other port's hunger. -/
theorem sever_patternVerdict_witness (q : Port)
    (h : IsHungry (apparatus (sever satietyBuilt Port.patternVerdict)) q) :
    q = Port.patternVerdict := by
  by_contra hq
  exact sever_only _ _ hq h

/-! ## Coverage: record fields and the stages that write them

Every field the inventory (§1, "Writes") names as written maps to the stage
that writes it. A field two stages write with different values is split into
one constructor per write (`:sentences` at send and `.analysis.json`
`:sentences` at read; `analysis_status` "requested" and "analyzed").
`writes_iff` says that the writer table and `fieldOrigin` agree in both
directions, so no stage writes a field outside the map.
-/

/-- The fields the running loop writes. -/
inductive RecordField where
  /-- Record `:sentences` (classical split, lexical cues). -/
  | sentences
  /-- Record `analysis_status "requested"`. -/
  | statusRequested
  /-- The `:quotes` sidecar. -/
  | quotes
  /-- The 小象 draft (`write-draft!`). -/
  | draft
  /-- Record `:proposed_patterns`. -/
  | proposedPatterns
  /-- Record `:reply_text`. -/
  | replyText
  /-- Record `:reply_at`. -/
  | replyAt
  /-- Record `:happened_summary`. -/
  | happenedSummary
  /-- Record `:commits` (trailer-credited). -/
  | commits
  /-- Record `:commits_excluded`. -/
  | commitsExcluded
  /-- `.analysis.json` `:sentences` (象's tags). -/
  | analysisSentences
  /-- Record `analysis_status "analyzed"`. -/
  | statusAnalyzed
  /-- The settled `e-xiang-turn-<id>` evidence row. -/
  | settledEvidence
  /-- `xiang/scope` hyperedges (minus40 scratch store). -/
  | scopeEdges
  /-- Record `:acts`. -/
  | acts
  /-- Record `:ports`. -/
  | ports
  /-- Record `:standings`. -/
  | standings
  /-- Record `:ports_status`. -/
  | portsStatus
  /-- Record `:alignment` (v1). -/
  | alignment
  /-- The `ma-observation` evidence row. -/
  | maObservation
  /-- The next record's `:reply_to`. -/
  | replyTo
  deriving DecidableEq, Fintype, Repr

/-- The stage that writes each field. Total: adding a field without a case
breaks the build. -/
def fieldOrigin : RecordField → Stage
  | RecordField.sentences => Stage.record
  | RecordField.statusRequested => Stage.record
  | RecordField.quotes => Stage.record
  | RecordField.draft => Stage.record
  | RecordField.proposedPatterns => Stage.render
  | RecordField.replyText => Stage.evaluate
  | RecordField.replyAt => Stage.evaluate
  | RecordField.happenedSummary => Stage.evaluate
  | RecordField.commits => Stage.evaluate
  | RecordField.commitsExcluded => Stage.evaluate
  | RecordField.analysisSentences => Stage.read
  | RecordField.statusAnalyzed => Stage.read
  | RecordField.settledEvidence => Stage.read
  | RecordField.scopeEdges => Stage.read
  | RecordField.acts => Stage.ports
  | RecordField.ports => Stage.ports
  | RecordField.standings => Stage.ports
  | RecordField.portsStatus => Stage.ports
  | RecordField.alignment => Stage.alignment
  | RecordField.maObservation => Stage.maObserve
  | RecordField.replyTo => Stage.nextTurn

/-- What each stage writes, as the inventory lists it. -/
def writes : Stage → List RecordField
  | Stage.record =>
      [RecordField.sentences, RecordField.statusRequested, RecordField.quotes,
       RecordField.draft]
  | Stage.render => [RecordField.proposedPatterns]
  | Stage.evaluate =>
      [RecordField.replyText, RecordField.replyAt, RecordField.happenedSummary,
       RecordField.commits, RecordField.commitsExcluded]
  | Stage.read =>
      [RecordField.analysisSentences, RecordField.statusAnalyzed,
       RecordField.settledEvidence, RecordField.scopeEdges]
  | Stage.ports =>
      [RecordField.acts, RecordField.ports, RecordField.standings,
       RecordField.portsStatus]
  | Stage.alignment => [RecordField.alignment]
  | Stage.maObserve => [RecordField.maObservation]
  | Stage.nextTurn => [RecordField.replyTo]

/-- COVERAGE: a stage writes a field exactly when the field maps to it. Every
field is written by its origin stage, and no stage writes a field mapped
elsewhere. -/
theorem writes_iff (s : Stage) (f : RecordField) :
    f ∈ writes s ↔ fieldOrigin f = s := by
  revert s f
  decide

/-- Every field has a writing stage. -/
theorem coverage_every_field_written (f : RecordField) :
    f ∈ writes (fieldOrigin f) :=
  (writes_iff _ f).2 rfl

/-- Every stage writes at least one field. -/
theorem every_stage_writes (s : Stage) : writes s ≠ [] := by
  cases s <;> simp [writes]

/-- Only `nextTurn` writes `:reply_to`: the one explicit link from turn n+1
back to turn n lies outside the tick. -/
theorem replyTo_outside_tick : fieldOrigin RecordField.replyTo ∉ atoms tick := by
  decide

/-- The fields packet 2 names each map to the stage the inventory gives. -/
example :
    fieldOrigin RecordField.sentences = Stage.record ∧
    fieldOrigin RecordField.proposedPatterns = Stage.render ∧
    fieldOrigin RecordField.replyText = Stage.evaluate ∧
    fieldOrigin RecordField.commits = Stage.evaluate ∧
    fieldOrigin RecordField.acts = Stage.ports ∧
    fieldOrigin RecordField.ports = Stage.ports ∧
    fieldOrigin RecordField.alignment = Stage.alignment ∧
    fieldOrigin RecordField.maObservation = Stage.maObserve ∧
    fieldOrigin RecordField.replyTo = Stage.nextTurn :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end XiangMaLoopExample

end DarkTower
