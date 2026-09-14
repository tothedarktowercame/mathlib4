import DarkTower.WarMachine.InboxZeroWitness
import Lean.Elab.Tactic.Omega

/-!
# Bounded compensating safety (T2'), distinct from atomic T2

Model-only. Versions count ALL intervening edits monotonically; a byte hash with
an ABA window does not implement that assumption. Detection and undo are separate
bounded stages. A failed undo is represented and does NOT satisfy survivable
safety. Removing this commit's effect preserves intervening edits in this model;
it does not claim arbitrary git revert/reset implements that operation.
-/
namespace DarkTower.WarMachine.InboxZeroCompensationWitness

structure Window where
  snapshot : Nat
  edits : Nat
  committedAt : Nat
  detectionDelay : Nat
  undoDelay : Nat
  deriving DecidableEq, Repr

def postVersion (w : Window) := w.snapshot + w.edits
def detects (w : Window) : Bool := decide (postVersion w ≠ w.snapshot)
def detectedAt (w : Window) := w.committedAt + w.detectionDelay
def undoneAt (w : Window) := detectedAt w + w.undoDelay

/-- T2'a: a visible intervening edit is detected by commit time + D.
The monotone-version construction is the detector-completeness assumption. -/
theorem detectionBound (w : Window) (D : Nat) (edit : 0 < w.edits)
    (bound : w.detectionDelay ≤ D) :
    detects w = true ∧ detectedAt w ≤ w.committedAt + D := by
  simp only [detects, decide_eq_true_eq, postVersion, detectedAt]
  constructor <;> omega

/-- End-to-end detection latency from the edit, rather than from commit.
C bounds edit-to-commit delay; omitting C would hide part of the window. -/
theorem detectionFromEdit (w : Window) (editTime C D : Nat)
    (edit : 0 < w.edits) (_order : editTime ≤ w.committedAt)
    (commitBound : w.committedAt ≤ editTime + C) (detectBound : w.detectionDelay ≤ D) :
    detects w = true ∧ detectedAt w ≤ editTime + C + D := by
  have h := detectionBound w D edit detectBound
  exact ⟨h.1, by omega⟩

inductive Undo where
  | restored | failed
  deriving DecidableEq, Repr
inductive Mode where
  | compensate | refuseWithoutExclusion
  deriving DecidableEq, Repr
inductive Reason where
  | original (record : InboxZeroWitness.RecordKind)
  | racedWithEdit | compensationFailed | atomicFeelCommitUnavailable
  deriving DecidableEq, Repr
structure Record where
  repo : String
  reason : Reason
  deriving DecidableEq, Repr
structure Output where
  repo : String
  state : InboxZeroWitness.RepoState
  commitIssued : Bool
  commitSurvives : Bool
  record : Option Record
  deriving DecidableEq, Repr

def originalRecord (r : InboxZeroWitness.Record) : Record :=
  ⟨r.repo, .original r.kind⟩

def lift (o : InboxZeroWitness.Output) : Output :=
  ⟨o.repo, o.state, o.committed, o.committed, o.record.map originalRecord⟩

def finish (i : InboxZeroWitness.Input) (w : Window) (undo : Undo) (mode : Mode) : Output :=
  let base := InboxZeroWitness.step i
  if base.committed then
    match mode with
    | .refuseWithoutExclusion =>
      ⟨i.repo, i.current, false, false, some ⟨i.repo, .atomicFeelCommitUnavailable⟩⟩
    | .compensate =>
      if detects w then
        match undo with
        | .restored => ⟨i.repo, i.current, true, false, some ⟨i.repo, .racedWithEdit⟩⟩
        | .failed => ⟨i.repo, i.current, true, true, some ⟨i.repo, .compensationFailed⟩⟩
      else lift base
  else lift base

/-- T2'b: successful compensation removes the commit and records the race. -/
theorem compensation (i : InboxZeroWitness.Input) (w : Window)
    (issued : (InboxZeroWitness.step i).committed = true) (race : detects w = true) :
    (finish i w .restored .compensate).commitSurvives = false ∧
    (finish i w .restored .compensate).record = some ⟨i.repo, .racedWithEdit⟩ := by
  simp [finish, issued, race]

/-- Optimistic commit can exist until BOTH detection and restoration finish. -/
def survivesAt (w : Window) (undo : Undo) (t : Nat) : Bool :=
  decide (w.committedAt ≤ t) &&
    !(detects w && decide (undo = .restored) && decide (undoneAt w ≤ t))

/-- T2'c: latency appears in the actual no-surviving-commit claim.
D bounds detection, U bounds restoration; D alone is NOT the survival bound. -/
theorem boundedSurvival (w : Window) (D U t : Nat) (edit : 0 < w.edits)
    (detectBound : w.detectionDelay ≤ D) (undoBound : w.undoDelay ≤ U)
    (afterWindow : w.committedAt + D + U ≤ t) :
    survivesAt w .restored t = false := by
  have hd := (detectionBound w D edit detectBound).1
  have hu : undoneAt w ≤ t := by unfold undoneAt detectedAt; omega
  simp [survivesAt, hd, hu]

theorem survivalFromEdit (w : Window) (editTime C D U t : Nat)
    (edit : 0 < w.edits) (_order : editTime ≤ w.committedAt)
    (commitBound : w.committedAt ≤ editTime + C)
    (detectBound : w.detectionDelay ≤ D) (undoBound : w.undoDelay ≤ U)
    (deadline : editTime + C + D + U ≤ t) :
    survivesAt w .restored t = false := by
  apply boundedSurvival w D U t edit detectBound undoBound
  omega

/-- The finite terminal output and temporal survival claim agree by the deadline. -/
theorem boundedCompensation (i : InboxZeroWitness.Input) (w : Window) (D U t : Nat)
    (issued : (InboxZeroWitness.step i).committed = true) (edit : 0 < w.edits)
    (detectBound : w.detectionDelay ≤ D) (undoBound : w.undoDelay ≤ U)
    (deadline : w.committedAt + D + U ≤ t) :
    survivesAt w .restored t = false ∧
    (finish i w .restored .compensate).commitSurvives = false ∧
    (finish i w .restored .compensate).record = some ⟨i.repo, .racedWithEdit⟩ := by
  exact ⟨boundedSurvival w D U t edit detectBound undoBound deadline,
    compensation i w issued (detectionBound w D edit detectBound).1⟩

/-- Compensation changes commit membership, not the surviving editor revision. -/
def restoredVersion (w : Window) := postVersion w
theorem editorChangesPreserved (w : Window) :
    restoredVersion w = w.snapshot + w.edits := rfl

/-- T1 composes even on undo failure: that failure is recorded, not hidden. -/
def covered (o : Output) : Prop :=
  o.state = .clean ∨ ∃ r, o.record = some r ∧ r.repo = o.repo

theorem typedTermination (i : InboxZeroWitness.Input) (w : Window) (u : Undo) (m : Mode) :
    covered (finish i w u m) := by
  rcases i with ⟨repo, observed, current, permission, result⟩
  cases current <;> cases permission <;> cases result <;> cases u <;> cases m <;>
    simp [finish, InboxZeroWitness.step, InboxZeroWitness.refuse, lift, originalRecord, covered] <;>
    split <;> simp_all

/-- T3 now speaks about surviving success or a typed blocker, including races. -/
theorem progress (i : InboxZeroWitness.Input) (age : Nat) (w : Window) (u : Undo) (m : Mode)
    (dirty : i.current = .dirty age) (ready : i.permission = .committable) :
    ((finish i w u m).commitSurvives = true ∧ (finish i w u m).state = .clean) ∨
      ∃ r, (finish i w u m).record = some r ∧ r.repo = i.repo := by
  cases h : i.commitResult <;> cases u <;> cases m <;>
    simp [finish, InboxZeroWitness.step, dirty, ready, h, InboxZeroWitness.refuse, lift, originalRecord] <;>
    split <;> simp_all

theorem flagsNonincreasing (i : InboxZeroWitness.Input) (w : Window) (u : Undo) (m : Mode) :
    InboxZeroWitness.flag (finish i w u m).state ≤ InboxZeroWitness.flag i.current := by
  rcases i with ⟨repo, observed, current, permission, result⟩
  cases current <;> cases permission <;> cases result <;> cases u <;> cases m <;>
    simp [finish, InboxZeroWitness.step, InboxZeroWitness.refuse, lift, InboxZeroWitness.flag] <;> split <;> simp_all

/-- The original no-commit-before-exclusion refusal remains available. -/
theorem strictRefusal (i : InboxZeroWitness.Input) (w : Window) (u : Undo) :
    (finish i w u .refuseWithoutExclusion).commitIssued = false := by
  cases h : (InboxZeroWitness.step i).committed <;> simp [finish, h, lift]

/-- T4 per repo: no commit or new record on clean input. Window events are
only inputs to a commit attempt; this is not a claim about unrelated new dirt. -/
theorem zeroFixedPoint (i : InboxZeroWitness.Input) (w : Window) (u : Undo) (m : Mode)
    (clean : i.current = .clean) :
    finish i w u m = ⟨i.repo, .clean, false, false, none⟩ := by
  simp [finish, InboxZeroWitness.step, clean, lift]

structure Entry where
  input : InboxZeroWitness.Input
  window : Window
  undo : Undo
  mode : Mode

def cycle (xs : List Entry) := xs.map (fun e => finish e.input e.window e.undo e.mode)
def flags (xs : List Output) := (xs.map (fun o => InboxZeroWitness.flag o.state)).sum
def newRecords (xs : List Output) := xs.filterMap Output.record
def ledgerAfter (ledger : List Record) (xs : List Entry) := ledger ++ newRecords (cycle xs)
def report (xs : List Output) : InboxZeroWitness.Report :=
  if flags xs = 0 then .zeroWitnessed else .pending

theorem cycleTypedTermination (xs : List Entry) : ∀ o ∈ cycle xs, covered o := by
  intro o ho
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ho
  exact typedTermination e.input e.window e.undo e.mode

theorem cycleLength (xs : List Entry) : (cycle xs).length = xs.length := by simp [cycle]

theorem cycleFlagsNonincreasing (xs : List Entry) :
    flags (cycle xs) ≤ (xs.map (fun e => InboxZeroWitness.flag e.input.current)).sum := by
  induction xs with
  | nil => simp [flags, cycle]
  | cons e xs ih =>
    simpa [flags, cycle] using Nat.add_le_add (flagsNonincreasing e.input e.window e.undo e.mode) ih

theorem recordsPreserved (ledger : List Record) (xs : List Entry) :
    ledger <+: ledgerAfter ledger xs := List.prefix_append _ _

theorem recordAppended (e : Entry) (xs : List Entry) (ledger : List Record)
    (member : e ∈ xs) (r : Record)
    (recorded : (finish e.input e.window e.undo e.mode).record = some r) :
    r ∈ ledgerAfter ledger xs := by
  simp only [ledgerAfter, List.mem_append]
  right
  exact List.mem_filterMap.mpr ⟨finish e.input e.window e.undo e.mode,
    List.mem_map.mpr ⟨e, member, rfl⟩, recorded⟩

theorem cycleZero (xs : List Entry) (h : ∀ e ∈ xs, e.input.current = .clean) :
    (cycle xs).map Output.state = xs.map (fun e => e.input.current) ∧
    (cycle xs).all (fun o => !o.commitIssued) = true ∧
    newRecords (cycle xs) = [] ∧ report (cycle xs) = .zeroWitnessed := by
  have each : ∀ e ∈ xs, finish e.input e.window e.undo e.mode =
      ⟨e.input.repo, .clean, false, false, none⟩ := by
    intro e he
    exact zeroFixedPoint e.input e.window e.undo e.mode (h e he)
  have meter : flags (cycle xs) = 0 := by
    have zeroInput : (xs.map (fun e => InboxZeroWitness.flag e.input.current)).sum = 0 := by
      induction xs with
      | nil => rfl
      | cons e xs ih =>
        have ht : ∀ j ∈ xs, j.input.current = .clean := fun j hj => h j (by simp [hj])
        have et : ∀ j ∈ xs, finish j.input j.window j.undo j.mode =
            ⟨j.input.repo, .clean, false, false, none⟩ := fun j hj => each j (by simp [hj])
        simpa [h e (by simp), InboxZeroWitness.flag] using ih ht et
    have bound := cycleFlagsNonincreasing xs
    omega
  refine ⟨?_, ?_, ?_, by simp [report, meter]⟩
  · simp only [cycle, List.map_map]
    apply List.map_congr_left
    intro e he
    simp [each e he, h e he]
  · simp only [cycle, List.all_map, List.all_eq_true]
    intro e he
    simp [each e he]
  · induction xs with
    | nil => rfl
    | cons e xs ih =>
      have ht : ∀ j ∈ xs, j.input.current = .clean := fun j hj => h j (by simp [hj])
      have et : ∀ j ∈ xs, finish j.input j.window j.undo j.mode =
          ⟨j.input.repo, .clean, false, false, none⟩ := fun j hj => each j (by simp [hj])
      have mt : flags (cycle xs) = 0 := by simpa [cycle, flags, each e (by simp), InboxZeroWitness.flag] using meter
      simpa [cycle, newRecords, each e (by simp)] using ih ht et mt

/-- Edit-after-snapshot commissioning SHAPE, not a pinned runtime readback. -/
def editAfterSnapshot : Window := ⟨10, 1, 5, 2, 3⟩
theorem fixtureDetects : detects editAfterSnapshot = true := by decide
theorem fixtureTransientCommit : survivesAt editAfterSnapshot .restored 6 = true := by decide
theorem fixtureGoneAtBound : survivesAt editAfterSnapshot .restored (5 + 2 + 3) = false := by decide
theorem failedUndoCanSurvive : survivesAt editAfterSnapshot .failed 100 = true := by decide

#print axioms recordAppended
#print axioms survivalFromEdit
#print axioms detectionFromEdit
#print axioms boundedCompensation
#print axioms cycleTypedTermination
#print axioms cycleLength
#print axioms cycleFlagsNonincreasing
#print axioms recordsPreserved
#print axioms cycleZero
#print axioms detectionBound
#print axioms compensation
#print axioms boundedSurvival
#print axioms editorChangesPreserved
#print axioms typedTermination
#print axioms progress
#print axioms flagsNonincreasing
#print axioms strictRefusal
#print axioms zeroFixedPoint
#print axioms fixtureDetects
#print axioms fixtureTransientCommit
#print axioms fixtureGoneAtBound
#print axioms failedUndoCanSurvive
end DarkTower.WarMachine.InboxZeroCompensationWitness
