import Mathlib.Tactic

/-!
# R20 interoceptive tripwires

This module states the record-level role implemented by `check!`,
`evaluate-wire`, `enabled?`, and `observe!` in
`futon2/src/futon2/aif/tripwire.clj`, read at Futon2 commit
`0f9587532031beb50a21091cc41cd10f4a16ff63`. A wire evaluates one observation
to zero or more violation witnesses. `check` admits exactly the zero-witness
case; `observe` scans enabled wires in retained registry order and reports the
first witness.

The concrete T11 model covers only `:unknown-job-state`: its seven accepted
states transcribe `known-job-states`. T11's independent
`:unparseable-job-time` witness is deliberately omitted.

This module leaves out the other twelve evaluators, report construction and
persistence, `*halt-on-witness?*`, deferral, `repair-covered-witness?`,
cross-run observation assembly, disabled-ID option parsing, and the runtime
catch around a throwing evaluator. It neither proves that an evaluator states
the right invariant nor that an observation is complete.

"Registry order" here is whatever order the runtime iterates `wire-registry`
in. That registry is a thirteen-entry Clojure map, which is a hash map: at the
commit above its iteration order is T13, T12, T5, T1, T9, T4, T2, T7, T3, T11,
T10, T8, T6, not T1 to T13 as written. The theorems hold for any order; which
wire reports when two are violated is fixed by that iteration order.
-/

namespace DarkTower.WarMachine.R20InteroceptiveTripwire

/-- One generic wire. `wireId` stands for `:trip/wire-id`; `enabled` combines
the registry `:enabled?` flag with absence from `:tripwire/disabled-wire-ids`;
`evaluate` stands for the function selected by `wire-evaluators`. -/
structure Wire (Observation Witness : Type) where
  wireId : Nat
  enabled : Bool
  evaluate : Observation → List Witness

/-- The ordered runtime `wire-registry` iteration presented to `observe!`. -/
abbrev Registry (Observation Witness : Type) := List (Wire Observation Witness)

/-- The pure decision part of `check!`: a pass retains the wire ID; a refusal
retains `:trip/wire-id` and the exact non-empty `:trip/witnesses`. Runtime
`:status :needs-joe` and report fields belong to the omitted effectful layer. -/
inductive CheckResult (Witness : Type) where
  | passed (wireId : Nat)
  | refused (wireId : Nat) (witnesses : List Witness)
  deriving DecidableEq, Repr

/-- One `observe!` trip: the reporting wire ID and its first yielded witness. -/
structure Trip (Witness : Type) where
  wireId : Nat
  witness : Witness
  deriving DecidableEq, Repr

/-- Transcription of the decision made by `check!` after `evaluate-wire`. -/
def check (wire : Wire Observation Witness) (observation : Observation) : CheckResult Witness :=
  match wire.evaluate observation with
  | [] => .passed wire.wireId
  | witnesses => .refused wire.wireId witnesses

/-- Ordered observation: disabled wires are skipped, empty enabled wires fall
through, and the first witness from the first violated enabled wire wins. -/
def observe : Registry Observation Witness → Observation → Option (Trip Witness)
  | [], _ => none
  | wire :: rest, observation =>
      if wire.enabled then
        match wire.evaluate observation with
        | [] => observe rest observation
        | witness :: _ => some { wireId := wire.wireId, witness := witness }
      else observe rest observation

theorem check_passed_iff (wire : Wire Observation Witness) (observation : Observation) :
    check wire observation = .passed wire.wireId ↔ wire.evaluate observation = [] := by
  cases evaluated : wire.evaluate observation <;> simp [check, evaluated]

theorem check_refused_exact (wire : Wire Observation Witness) (observation : Observation)
    (wireId : Nat) (witnesses : List Witness)
    (refused : check wire observation = .refused wireId witnesses) :
    wireId = wire.wireId ∧ witnesses = wire.evaluate observation ∧ witnesses ≠ [] := by
  cases evaluated : wire.evaluate observation with
  | nil => simp [check, evaluated] at refused
  | cons witness rest =>
      simp [check, evaluated] at refused
      obtain ⟨rfl, rfl⟩ := refused
      exact ⟨rfl, rfl, by simp⟩

theorem observe_none_iff (registry : Registry Observation Witness)
    (observation : Observation) :
    observe registry observation = none ↔
      ∀ wire ∈ registry, wire.enabled = true → wire.evaluate observation = [] := by
  induction registry with
  | nil => simp [observe]
  | cons wire rest ih =>
      by_cases enabled : wire.enabled = true
      · cases evaluated : wire.evaluate observation with
        | nil => simp [observe, enabled, evaluated, ih]
        | cons witness tail => simp [observe, enabled, evaluated]
      · have disabled : wire.enabled = false := Bool.eq_false_of_not_eq_true enabled
        simp [observe, disabled, ih]

/-- Soundness and priority: a reported witness comes from an enabled wire at
one registry position, and every enabled wire before that position was clear. -/
theorem observe_some_has_enabled_first_source
    (registry : Registry Observation Witness) (observation : Observation)
    (trip : Trip Witness) (reported : observe registry observation = some trip) :
    ∃ before wire after,
      registry = before ++ wire :: after ∧
      wire.enabled = true ∧
      trip.wireId = wire.wireId ∧
      trip.witness ∈ wire.evaluate observation ∧
      (∀ prior ∈ before, prior.enabled = true → prior.evaluate observation = []) := by
  induction registry with
  | nil => simp [observe] at reported
  | cons wire rest ih =>
      by_cases enabled : wire.enabled = true
      · cases evaluated : wire.evaluate observation with
        | nil =>
            simp [observe, enabled, evaluated] at reported
            obtain ⟨before, source, after, rfl, sourceEnabled, sourceId, witnessMem, priorClear⟩ :=
              ih reported
            exact ⟨wire :: before, source, after, by simp, sourceEnabled, sourceId,
              witnessMem, by
                intro prior retained priorEnabled
                simp only [List.mem_cons] at retained
                rcases retained with rfl | retained
                · exact evaluated
                · exact priorClear prior retained priorEnabled⟩
        | cons witness tail =>
            simp [observe, enabled, evaluated] at reported
            subst trip
            exact ⟨[], wire, rest, by simp, enabled, rfl, by simp [evaluated], by simp⟩
      · have disabled : wire.enabled = false := Bool.eq_false_of_not_eq_true enabled
        simp [observe, disabled] at reported
        obtain ⟨before, source, after, rfl, sourceEnabled, sourceId, witnessMem, priorClear⟩ :=
          ih reported
        exact ⟨wire :: before, source, after, by simp, sourceEnabled, sourceId,
          witnessMem, by
            intro prior retained priorEnabled
            simp only [List.mem_cons] at retained
            rcases retained with rfl | retained
            · exact False.elim (enabled priorEnabled)
            · exact priorClear prior retained priorEnabled⟩

/-- Toggle one wire off. This is the semantic cost of disabling it: its
witnesses disappear from observation for every input, possibly exposing a
later wire that was previously masked. -/
def disable (wire : Wire Observation Witness) : Wire Observation Witness :=
  { wire with enabled := false }

theorem disabling_removes_wire (before after : Registry Observation Witness)
    (wire : Wire Observation Witness) (observation : Observation) :
    observe (before ++ disable wire :: after) observation =
      observe (before ++ after) observation := by
  induction before with
  | nil => simp [observe, disable]
  | cons prior rest ih =>
      simp only [List.cons_append]
      by_cases enabled : prior.enabled = true
      · cases evaluated : prior.evaluate observation <;>
          simp [observe, enabled, evaluated, ih]
      · have disabled : prior.enabled = false := Bool.eq_false_of_not_eq_true enabled
        simp [observe, disabled, ih]

inductive JobState where
  | queued | pending | running | done | failed | cancelled | timedOut
  | other (code : Nat)
  deriving DecidableEq, Repr

/-- One T11 Agency job. `jobId` and `state` stand for runtime `:job-id` and
`:state`. -/
structure Job where
  jobId : Nat
  state : JobState
  deriving DecidableEq, Repr

/-- T11's `:unknown-job-state` witness, retaining runtime `:job-id` and the
unrecognized `:state`. -/
structure UnknownJobState where
  jobId : Nat
  state : JobState
  deriving DecidableEq, Repr

/-- The seven members of runtime `known-job-states`: queued, pending, running,
done, failed, cancelled, and timed-out. -/
def knownJobState : JobState → Bool
  | .queued | .pending | .running | .done | .failed | .cancelled | .timedOut => true
  | .other _ => false

/-- T11's unknown-state evaluator. Timestamp witnesses are out of scope. -/
def t11 : List Job → List UnknownJobState
  | [] => []
  | job :: rest =>
      if knownJobState job.state then t11 rest
      else { jobId := job.jobId, state := job.state } :: t11 rest

theorem t11_no_witness_iff (jobs : List Job) :
    t11 jobs = [] ↔ ∀ job ∈ jobs, knownJobState job.state = true := by
  induction jobs with
  | nil => simp [t11]
  | cons job rest ih =>
      cases known : knownJobState job.state <;> simp [t11, known, ih]

def t11Wire (enabled : Bool) : Wire (List Job) UnknownJobState :=
  { wireId := 11, enabled := enabled, evaluate := t11 }

def cleanJobs : List Job :=
  [{ jobId := 1, state := .queued }, { jobId := 2, state := .done }]

def badJobs : List Job :=
  [{ jobId := 1, state := .running }, { jobId := 2, state := .other 99 }]

theorem cleanJobs_pass : check (t11Wire true) cleanJobs = .passed 11 := by
  decide

theorem badJobs_refuse_and_carry_job :
    check (t11Wire true) badJobs =
      .refused 11 [{ jobId := 2, state := .other 99 }] := by
  decide

theorem disabled_t11_is_not_observed :
    observe [t11Wire false] badJobs = none := by
  decide

def firstViolated : Wire Nat Nat :=
  { wireId := 1, enabled := true, evaluate := fun _ => [101] }
def secondViolated : Wire Nat Nat :=
  { wireId := 2, enabled := true, evaluate := fun _ => [202] }

theorem registry_order_reports_first :
    observe [firstViolated, secondViolated] 0 = some { wireId := 1, witness := 101 } := by
  decide

theorem registry_order_does_not_report_second :
    observe [firstViolated, secondViolated] 0 ≠ some { wireId := 2, witness := 202 } := by
  decide

end DarkTower.WarMachine.R20InteroceptiveTripwire
