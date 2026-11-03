import DarkTower.WarMachine.CloseOutcomeImage

/-!
# An operator abort at a breakpoint is a decision, not an injury (R31)

Source: `~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` R31 (claude-2,
2026-11-03) and the restoration trail
`futon2/holes/labs/wm-contract/PLAN-outer-selection-restoration-claude2-2026-11-01.md`
rows 00:42Z and 00:45Z.  Lean first; the Clojure conforms in a separate packet
(R31-b).  Additions only, beside `CloseOutcomeImage` (whose `CloseOutcome`,
`image`, `closeVerdict` and `Verdict` this module reuses).

**What happened.**  Run `2026-11-03-561c5ec3-6510-42a3-930b-331ef089feb4`
stopped at the armed `[:after :selection-world]` breakpoint with a retained
value.  The operator released it with `(debugger/continue! run :abort
:nothing-to-fix)` at 00:41:37Z.  The tick run record closed
`:failure {:kind :untyped-failure :stage :selection-world}`, the completion
`:end-status :build-failed`, and the terminal sink `:meta-terminal-injury-ingest`
appended entry 156 (`injury/d7cd119eb38f3e48b54211372e64f4e07d562f73`,
`:state :open`, `:attempt 1`) to the live ledger.  Nothing in the machine failed;
the operator ended the run on purpose.  The next ordinary click's self-heal
preflight reads that open injury and routes to dedicated self-heal.

**The code as read (2026-11-03, futon2 main).**  `run-phase!`'s `:abort` branch
(`full_loop_runner.clj` ~493-508) emits the phase-end event with
`:debugger/restart :abort`, discharges the throwable and rethrows it unchanged.
When the stop was a retained value, that throwable is the breakpoint signal
itself (`ex-info "War Machine phase breakpoint" {:kind :wm/phase-breakpoint
…}`), which carries neither `:failure-kind` nor `:outcome`.  The close takes
`failure-kind-from` (~6643): explicit kind at any depth, else transport kind,
else `:untyped-failure`.  `meta_terminal_injury.clj` `classify` (~270-330)
then takes the default injury branch because `:untyped-failure` is not in
`explicit-non-injury-kinds`.  The frame-by-frame path from the rethrow to the
close (the record's `:error` reads "invalid checkpoint cell", the selection
checkpoint refusing the partial cell on the way out) is the R31-a discovery
packet's job and is not asserted here.

**What this module settles.**

1. The abort branch's rethrow is a function of what it was given.  A throwable
   that already carries a failure kind or outcome (a typed refusal, a typed
   machine failure) is rethrown as it is: `run_debugger_test.clj` pins this
   (`abort-preserves-the-detached-failure`, the `identical?` typed-refusal
   abort, `recorded-abstention`).  The bare breakpoint signal, which carries
   no kind, is rethrown typed `:debugger/aborted` with the operator's
   disposition and the close outcome `:cancelled`.
2. `:debugger/aborted` is a non-injury kind: the operator's restart choice is a
   decision.  `:untyped-failure` stays an injury (the heavy machine-failure
   contract is not widened).
3. The ledger opens an entry only on an injury verdict, so an operator abort
   never opens one.

**Clojure correspondence (R31-b, not here).**  (a) the `:abort` branch of
`run-phase!` rethrows `(ex-info … {:failure-kind :debugger/aborted :outcome
:cancelled :debugger/disposition d :failure-stage phase} throwable)` when
`explicit-failure-kind` of the throwable is nil, else the throwable itself;
(b) `explicit-non-injury-kinds` gains `:debugger/aborted ↦ :operator-aborted-run`
and the `observation-class` case names it; (c) entry 156 is closed by the
medic replay path once (b) exists, or by Joe's word; it is not the test's or
this module's business.
-/

namespace DarkTower.WarMachine.DebuggerAbortVerdict

open DarkTower.WarMachine.CloseOutcomeImage (CloseOutcome image closeVerdict Verdict)

/-- The failure kinds this module needs: the close's default, the two typed
kinds met on or near the abort path, the operator's typed abort, and no kind. -/
inductive Kind where
  | none
  | untypedFailure
  | invalidCheckpointCell
  | abstained
  | debuggerAborted
  deriving DecidableEq, Repr

def failurePresent : Kind → Bool
  | .none => false
  | _ => true

/-- The debugger's dispositions (`debugger/continue!` third argument). -/
inductive Disposition where
  | nothingToFix
  | failed
  deriving DecidableEq, Repr

/-- What the `:abort` branch is given: the bare breakpoint signal (a retained
value, no failure kind, no outcome), or a throwable that already carries a
kind. -/
inductive Stopped where
  | breakpointSignal
  | typed (k : Kind)
  deriving DecidableEq, Repr

/-- The deployed branch rethrows unchanged; the close's `failure-kind-from`
reads the bare signal as `:untyped-failure`. -/
def currentAbortKind : Stopped → Kind
  | .breakpointSignal => .untypedFailure
  | .typed k => k

/-- The repaired branch: only the bare signal is typed, as `:debugger/aborted`. -/
def repairedAbortKind : Stopped → Kind
  | .breakpointSignal => .debuggerAborted
  | .typed k => k

/-- The close outcome each branch gives the bare signal: today the completion
reads `:end-status :build-failed`; repaired, the cohort's own `:cancelled`. -/
def currentAbortOutcome : CloseOutcome := .buildFailed
def repairedAbortOutcome : CloseOutcome := .cancelled

/-- `meta_terminal_injury.clj` `explicit-non-injury-kinds` today, restricted
to this module's kinds: `:abstained` is a non-injury, the rest take the default
injury branch, no kind leaves the close to decide. -/
def currentKindVerdict : Kind → Option Verdict
  | .none => Option.none
  | .abstained => some .nonInjury
  | .untypedFailure => some .injury
  | .invalidCheckpointCell => some .injury
  | .debuggerAborted => some .injury

/-- The repaired table adds `debuggerAborted ↦ nonInjury` and nothing else. -/
def repairedKindVerdict : Kind → Option Verdict
  | .none => Option.none
  | .abstained => some .nonInjury
  | .untypedFailure => some .injury
  | .invalidCheckpointCell => some .injury
  | .debuggerAborted => some .nonInjury

/-- A close as the terminal reads it: outcome and failure kind. -/
structure Close where
  outcome : CloseOutcome
  kind : Kind
  deriving DecidableEq, Repr

/-- The terminal reading under a kind table: the close decides when it does
(`CloseOutcomeImage.closeVerdict`), otherwise the kind. -/
def verdictOf (kv : Kind → Option Verdict) (c : Close) : Option Verdict :=
  match closeVerdict (image c.outcome) (failurePresent c.kind) with
  | some v => some v
  | Option.none => kv c.kind

/-- The ledger appends an entry exactly on an injury verdict. -/
def ledgerOpens : Option Verdict → Bool
  | some .injury => true
  | _ => false

/-- Run 561c5ec3's close as each branch and table produce it. -/
def currentClose : Close := ⟨currentAbortOutcome, currentAbortKind .breakpointSignal⟩
def repairedClose : Close := ⟨repairedAbortOutcome, repairedAbortKind .breakpointSignal⟩

/-! ## Theorems -/

/-- Clause 1: the repaired branch changes nothing for a throwable that already
carries a kind.  This is what the three abort pins in `run_debugger_test.clj`
hold. -/
theorem abort_preserves_typed (k : Kind) :
    repairedAbortKind (.typed k) = currentAbortKind (.typed k) := rfl

/-- The two branches differ exactly on the bare signal. -/
theorem branches_differ_only_on_signal (s : Stopped) :
    repairedAbortKind s ≠ currentAbortKind s ↔ s = .breakpointSignal := by
  cases s with
  | breakpointSignal => simp [repairedAbortKind, currentAbortKind]
  | typed k => simp [repairedAbortKind, currentAbortKind]

/-- The witness: entry 156.  The deployed branch and table read the abort of
run 561c5ec3 as an injury and the ledger opens. -/
theorem run561c5ec3_current_injury :
    verdictOf currentKindVerdict currentClose = some .injury ∧
      ledgerOpens (verdictOf currentKindVerdict currentClose) = true := by
  decide

/-- The law: the same abort, repaired, is a non-injury and the ledger stays
closed. -/
theorem run561c5ec3_law_nonInjury :
    verdictOf repairedKindVerdict repairedClose = some .nonInjury ∧
      ledgerOpens (verdictOf repairedKindVerdict repairedClose) = false := by
  decide

/-- Clause 2 and 3: whatever close outcome rides with it, an operator abort is
never an injury under the repaired table, so the ledger never opens on one. -/
theorem operator_abort_never_injury (o : CloseOutcome) :
    verdictOf repairedKindVerdict ⟨o, .debuggerAborted⟩ = some .nonInjury ∧
      ledgerOpens (verdictOf repairedKindVerdict ⟨o, .debuggerAborted⟩) = false := by
  cases o <;> decide

/-- The repair alone, without the branch: typing the table but still closing
the bare signal as `:untyped-failure` leaves entry 156 an injury.  Both halves
are needed. -/
theorem table_alone_not_enough :
    verdictOf repairedKindVerdict currentClose = some .injury := by decide

/-- The branch alone, without the table: a `:debugger/aborted` kind the table
does not know takes the default injury branch. -/
theorem branch_alone_not_enough :
    verdictOf currentKindVerdict repairedClose = some .injury := by decide

/-- Control: the escape hatch does not widen.  An untyped failure is still an
injury under the repaired table, with either close outcome. -/
theorem untyped_still_injury :
    verdictOf repairedKindVerdict ⟨.buildFailed, .untypedFailure⟩ = some .injury ∧
      verdictOf repairedKindVerdict ⟨.cancelled, .untypedFailure⟩ = some .injury := by
  decide

/-- Control: a typed checkpoint refusal is still an injury under both tables. -/
theorem invalidCheckpointCell_still_injury :
    verdictOf currentKindVerdict ⟨.buildFailed, .invalidCheckpointCell⟩ = some .injury ∧
      verdictOf repairedKindVerdict ⟨.buildFailed, .invalidCheckpointCell⟩ = some .injury := by
  decide

/-- An aborted typed abstention reads the same under both branches and both
tables: a non-injury, as before. -/
theorem aborted_abstention_unchanged :
    verdictOf currentKindVerdict ⟨.abstained, currentAbortKind (.typed .abstained)⟩ =
        some .nonInjury ∧
      verdictOf repairedKindVerdict ⟨.abstained, repairedAbortKind (.typed .abstained)⟩ =
        some .nonInjury := by
  decide

/-- The repaired table extends the current one: whatever was a non-injury
stays one. -/
theorem repaired_kind_extends_current (k : Kind)
    (h : currentKindVerdict k = some .nonInjury) : repairedKindVerdict k = some .nonInjury := by
  cases k <;> simp_all [currentKindVerdict, repairedKindVerdict]

/-- The repaired table adds exactly one non-injury kind. -/
theorem repaired_adds_only_debuggerAborted (k : Kind)
    (h : repairedKindVerdict k ≠ currentKindVerdict k) : k = .debuggerAborted := by
  cases k <;> simp_all [currentKindVerdict, repairedKindVerdict]

#print axioms abort_preserves_typed
#print axioms branches_differ_only_on_signal
#print axioms run561c5ec3_current_injury
#print axioms run561c5ec3_law_nonInjury
#print axioms operator_abort_never_injury
#print axioms table_alone_not_enough
#print axioms branch_alone_not_enough
#print axioms untyped_still_injury
#print axioms invalidCheckpointCell_still_injury
#print axioms aborted_abstention_unchanged
#print axioms repaired_kind_extends_current
#print axioms repaired_adds_only_debuggerAborted

end DarkTower.WarMachine.DebuggerAbortVerdict
