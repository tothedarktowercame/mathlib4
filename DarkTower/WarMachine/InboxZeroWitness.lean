import Mathlib.Data.List.Basic

/-!
# Inbox zero: finite loop laws, not production correspondence

OBSERVE supplies a finite list. FEEL supplies the state at execution time, not
an earlier observation. Commitment is ATOMIC with this guard in the model: a
production implementation must establish that assumption, including the
check/use race. No fairness, eventual zero, git success or Clojure correspondence
is proved. A permanently blocked repo may remain flagged forever. No-new-dirt
means states are not replaced by new observations during the cycle.
-/
namespace DarkTower.WarMachine.InboxZeroWitness
inductive RepoState where
  | clean | dirty (age : Nat) | inFlight
  deriving DecidableEq, Repr
inductive Reason where
  | inFlight | policyDenied | commitFailed
  deriving DecidableEq, Repr
inductive Permission where
  | committable | blocked (reason : Reason)
  deriving DecidableEq, Repr
inductive CommitResult where
  | success | refused (reason : Reason)
  deriving DecidableEq, Repr
structure Input where
  repo : String
  observed : RepoState
  current : RepoState
  permission : Permission
  commitResult : CommitResult
  deriving DecidableEq, Repr
inductive RecordKind where
  | flag (age : Nat) | refusal (reason : Reason)
  deriving DecidableEq, Repr
structure Record where
  repo : String
  kind : RecordKind
  deriving DecidableEq, Repr
structure Output where
  repo : String
  state : RepoState
  committed : Bool
  record : Option Record
  deriving DecidableEq, Repr

def refuse (i : Input) (r : Reason) : Output :=
  ⟨i.repo, i.current, false, some ⟨i.repo, .refusal r⟩⟩
def step (i : Input) : Output :=
  match i.current with
  | .clean => ⟨i.repo, .clean, false, none⟩
  | .inFlight => refuse i .inFlight
  | .dirty _ => match i.permission with
    | .blocked r => refuse i r
    | .committable => match i.commitResult with
      | .success => ⟨i.repo, .clean, true, none⟩
      | .refused r => refuse i r

def results (inputs : List Input) := inputs.map step
def covered (o : Output) : Prop :=
  o.state = .clean ∨ ∃ r, o.record = some r ∧ r.repo = o.repo

/-- T1: every non-clean result carries a typed, repo-bound record. -/
theorem typedTermination (i : Input) : covered (step i) := by
  rcases i with ⟨repo, observed, current, permission, commitResult⟩
  cases current <;> cases permission <;> cases commitResult <;>
    simp [covered, step, refuse]
theorem cycleLength (inputs : List Input) : (results inputs).length = inputs.length := by
  simp [results]
theorem cycleTypedTermination (inputs : List Input) : ∀ o ∈ results inputs, covered o := by
  intro o ho
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ho
  exact typedTermination i

/-- T2: the atomic FEEL/commit guard controls the effect, not stale observation. -/
theorem inFlightNeverCommitted (i : Input) (h : i.current = .inFlight) :
    (step i).committed = false := by simp [step, h, refuse]

/-- T3: idle, committable dirt commits or names a refusal reason. -/
theorem progress (i : Input) (age : Nat) (h : i.current = .dirty age)
    (p : i.permission = .committable) :
    ((step i).committed = true ∧ (step i).state = .clean) ∨
      ∃ r, (step i).record = some ⟨i.repo, .refusal r⟩ := by
  cases c : i.commitResult <;> simp [step, h, p, c, refuse]

/-- Outstanding repo count, not cumulative ledger length. -/
def flag : RepoState → Nat | .clean => 0 | _ => 1
def inputFlags (xs : List Input) := (xs.map (fun i => flag i.current)).sum
def outputFlags (xs : List Output) := (xs.map (fun o => flag o.state)).sum

theorem stepFlagsNonincreasing (i : Input) : flag (step i).state ≤ flag i.current := by
  rcases i with ⟨repo, observed, current, permission, commitResult⟩
  cases current <;> cases permission <;> cases commitResult <;> simp [step, refuse, flag]
theorem flagsNonincreasing (xs : List Input) : outputFlags (results xs) ≤ inputFlags xs := by
  induction xs with
  | nil => simp [results, outputFlags, inputFlags]
  | cons i xs ih =>
    simpa [results, outputFlags, inputFlags] using Nat.add_le_add (stepFlagsNonincreasing i) ih

/-- The only state change between cycles; no newly observed dirt is inserted. -/
def nextInputs (xs : List Input) : List Input :=
  xs.map (fun i => { i with observed := i.current, current := (step i).state })
theorem noNewDirtFlags (xs : List Input) : inputFlags (nextInputs xs) = outputFlags (results xs) := by
  simp [inputFlags, nextInputs, outputFlags, results, List.map_map, Function.comp_def]
def repeatCycles : Nat → List Input → List Input
  | 0, xs => xs
  | n + 1, xs => repeatCycles n (nextInputs xs)
theorem repeatedFlagsNonincreasing (n : Nat) (xs : List Input) :
    inputFlags (repeatCycles n xs) ≤ inputFlags xs := by
  induction n generalizing xs with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    exact Nat.le_trans (ih (nextInputs xs)) (by rw [noNewDirtFlags]; exact flagsNonincreasing xs)

def records (xs : List Output) := xs.filterMap Output.record
def ledgerAfter (ledger : List Record) (xs : List Input) := ledger ++ records (results xs)
theorem refusalsAppended (ledger : List Record) (xs : List Input) :
    ledger <+: ledgerAfter ledger xs := by exact List.prefix_append _ _
theorem refusalRecorded (i : Input) (xs : List Input) (ledger : List Record)
    (h : i ∈ xs) (r : Record) (hr : (step i).record = some r) :
    r ∈ ledgerAfter ledger xs := by
  simp only [ledgerAfter, List.mem_append]
  right
  exact List.mem_filterMap.mpr ⟨step i, List.mem_map.mpr ⟨i, h, rfl⟩, hr⟩

inductive Report where
  | zeroWitnessed | pending
  deriving DecidableEq, Repr
def report (xs : List Output) : Report :=
  if outputFlags xs = 0 then .zeroWitnessed else .pending
def commitCount (xs : List Output) := (xs.filter (fun o => o.committed)).length

/-- T4: the repo-state projection is fixed; no commit, only a zero meter report. -/
theorem zeroFixedPoint (xs : List Input) (h : ∀ i ∈ xs, i.current = .clean) :
    (results xs).map Output.state = xs.map Input.current ∧
    commitCount (results xs) = 0 ∧ report (results xs) = .zeroWitnessed := by
  have each : ∀ i ∈ xs, step i = ⟨i.repo, .clean, false, none⟩ := by
    intro i hi
    simp [step, h i hi]
  have states : (results xs).map Output.state = xs.map Input.current := by
    simp only [results, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp [each i hi, h i hi]
  have counts : commitCount (results xs) = 0 ∧ outputFlags (results xs) = 0 := by
    clear states
    induction xs with
    | nil => simp [commitCount, outputFlags, results]
    | cons i xs ih =>
      have hh : ∀ j ∈ xs, j.current = .clean := fun j hj => h j (by simp [hj])
      have ee : ∀ j ∈ xs, step j = ⟨j.repo, .clean, false, none⟩ := fun j hj => each j (by simp [hj])
      have tail := ih hh ee
      simpa [results, commitCount, outputFlags, each i (by simp), flag] using tail
  exact ⟨states, counts.1, by simp [report, counts.2]⟩

theorem zeroAppendsNoRecords (xs : List Input) (h : ∀ i ∈ xs, i.current = .clean) :
    records (results xs) = [] := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    have hc := h i (by simp)
    have ht : ∀ j ∈ xs, j.current = .clean := fun j hj => h j (by simp [hj])
    simpa [records, results, step, hc] using ih ht

/-- A typed record set: uniqueness is an input condition, not a name-merging rule. -/
structure CycleInput where
  repos : List Input
  uniqueRepos : (repos.map Input.repo).Nodup

structure CycleOutput where
  repos : List Output
  ledger : List Record
  meter : Report

def cycle (input : CycleInput) (ledger : List Record) : CycleOutput :=
  let output := results input.repos
  ⟨output, ledger ++ records output, report output⟩

/- Induced defective outputs: witnesses against weakened loops, not the laws. -/
def dirtyInput : Input := ⟨"repo", .dirty 5, .dirty 5, .committable, .success⟩
def busyInput : Input := { dirtyInput with current := .inFlight }
def cleanInput : Input := { dirtyInput with current := .clean }
def silent : Output := ⟨"repo", .dirty 5, false, none⟩
def staleCommit : Output := ⟨"repo", .clean, true, none⟩
def newDirt : Output := ⟨"repo", .dirty 0, false, some ⟨"repo", .flag 0⟩⟩
theorem silentBreaksT1 : ¬ covered silent := by simp [covered, silent]
theorem staleObservationRefused : (step busyInput).committed = false := by decide
theorem newDirtBreaksMonotonicity : ¬ (flag newDirt.state ≤ flag cleanInput.current) := by decide
theorem zeroCommitBreaksT4 : commitCount [staleCommit] ≠ 0 := by decide

/-- MODEL EXAMPLE ONLY. This is not the 12-repository production readback. -/
def exampleInputs : List Input :=
  [dirtyInput,
   ⟨"blocked", .dirty 8, .dirty 8, .committable, .refused .commitFailed⟩,
   ⟨"clean", .clean, .clean, .committable, .success⟩]
theorem exampleProgress : inputFlags exampleInputs = 2 ∧
    outputFlags (results exampleInputs) = 1 ∧
    commitCount (results exampleInputs) = 1 ∧
    records (results exampleInputs) = [⟨"blocked", .refusal .commitFailed⟩] := by decide

#print axioms noNewDirtFlags
#print axioms repeatedFlagsNonincreasing
#print axioms zeroAppendsNoRecords
#print axioms exampleProgress
#print axioms stepFlagsNonincreasing
#print axioms typedTermination
#print axioms cycleLength
#print axioms cycleTypedTermination
#print axioms inFlightNeverCommitted
#print axioms progress
#print axioms flagsNonincreasing
#print axioms refusalsAppended
#print axioms refusalRecorded
#print axioms zeroFixedPoint
#print axioms silentBreaksT1
#print axioms staleObservationRefused
#print axioms newDirtBreaksMonotonicity
#print axioms zeroCommitBreaksT4
end DarkTower.WarMachine.InboxZeroWitness
