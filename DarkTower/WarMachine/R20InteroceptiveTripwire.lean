import Mathlib.Tactic

/-!
# R20 interoceptive tripwires

## The role

`p4ng/sec-catalog.tex`, "Interoceptive Tripwires (R20)", gives R20 its role:
an enabled wire is calibrated against known incidents before it is armed; a
trip receives the fail-safe response "freeze, record, park, summon", which may
degrade only toward durable recording and never toward blocking the run; and
every closed incident is covered by a retro-tripping wire or retained on an
explicit blind-spot map. Because no sensorium is complete, the record reports
exact coverage rather than claiming completeness. `Calibrated`,
`IncidentsAccountedFor`, `ConformingResponse`, and `R20Conformant` below state
the corresponding satisfaction criteria.

The paper also reads a wire as a near-infinite-precision prior over machine
trajectories. `wirePriorMass` and `tripSurprisal` state its limiting ideal:
violating trajectories have zero prior mass and therefore infinite surprisal.
This is a role statement, not an empirical calibration of a wire's precision.

## What the implementation checks

The first section transcribes the record-level mechanics implemented by `check!`,
`evaluate-wire`, `enabled?`, and `observe!` in
`futon2/src/futon2/aif/tripwire.clj`, read at Futon2 commit
`0f9587532031beb50a21091cc41cd10f4a16ff63`. A wire evaluates one observation
to zero or more violation witnesses. `check` admits exactly the zero-witness
case; `observe` scans enabled wires in retained registry order and reports the
first witness.

The concrete T11 model covers only `:unknown-job-state`: its seven accepted
states transcribe `known-job-states`. T11's independent
`:unparseable-job-time` witness is deliberately omitted.

At that commit the runtime retains a trip observation, wire ID, witness, action
and durable report path; `:park-and-summon` attempts a typed repair finding,
park and bell, degrading to stop-line and then record on failure. It does not
retain an authoritative known-incident corpus with wire assignments, a
calibration receipt, an explicit blind-spot map, an exact coverage number, or
one response record whose booleans establish every paper-mandated step. Thus
the implementation cannot yet be tested for `R20Conformant` from its retained
records.

On blocking, the default path agrees with the paper: since Futon2 `a03ae7b05`
(2026-09-19) `observe!` records a witness and the run continues, and the
default action is `:record`, the lowest rung. `FUTON_WM_TRIPWIRE_HALT=1` is an
opt-in setting under which a trip throws and stops the run; a response made
under it has `blockedRun = true` and is not a `ConformingResponse`.

This module leaves out the other twelve evaluators, deferral,
`repair-covered-witness?`, cross-run observation assembly, disabled-ID option
parsing, and the runtime catch around a throwing evaluator. It neither proves
that an evaluator states the right invariant nor that an observation is
complete. The R20-to-R7/R14 precision-update role is a separate statement.

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

/-! ## The paper's prior/surprisal reading -/

/-- A closed or reconstructed incident used to calibrate the sensorium.
`incidentId` stands for its durable identity; `observation` is the machine
observation retained for it; `assignedWireId` is the wire the calibration
corpus says must retro-trip. No authoritative runtime record carrying this
three-way join exists at Futon2 `0f9587532031beb50a21091cc41cd10f4a16ff63`. -/
structure Incident (Observation : Type) where
  incidentId : Nat
  observation : Observation
  assignedWireId : Option Nat

/-- The support of a wire's trajectory prior, as an indicator: 0 on an
observation where the evaluator finds a violation, 1 on a clear one. It is not
a normalised distribution, and `tripSurprisal` below is defined beside it, not
derived from it as a negative logarithm; the derived statement, for any prior
supported on the wire's clear observations, belongs with the precision
statement that connects R20 to R7. -/
def wirePriorMass (wire : Wire Observation Witness) (observation : Observation) : ℚ :=
  if wire.evaluate observation = [] then 1 else 0

/-- The limiting surprisal corresponding to `wirePriorMass`: a trip is top in
the extended reals, while a clear observation has zero surprisal. -/
noncomputable def tripSurprisal (wire : Wire Observation Witness)
    (observation : Observation) : EReal :=
  if wire.evaluate observation = [] then 0 else ⊤

/-- A wire retro-trips when it yields at least one witness for the retained
observation of a known incident. -/
def RetroTrips (wire : Wire Observation Witness) (incident : Incident Observation) : Prop :=
  wire.evaluate incident.observation ≠ []

theorem retroTrip_has_zero_prior_and_infinite_surprisal
    (wire : Wire Observation Witness) (incident : Incident Observation)
    (trips : RetroTrips wire incident) :
    wirePriorMass wire incident.observation = 0 ∧
    tripSurprisal wire incident.observation = ⊤ := by
  change wire.evaluate incident.observation ≠ [] at trips
  simp [wirePriorMass, tripSurprisal, trips]

/-! ## Calibration against known incidents -/

/-- Every enabled wire has at least one assigned incident, and it retro-trips
on every corpus incident assigned to it. -/
def Calibrated (registry : Registry Observation Witness)
    (corpus : List (Incident Observation)) : Prop :=
  ∀ wire ∈ registry, wire.enabled = true →
    (∃ incident ∈ corpus, incident.assignedWireId = some wire.wireId) ∧
    (∀ incident ∈ corpus, incident.assignedWireId = some wire.wireId →
      RetroTrips wire incident)

/-- An armed wire with an assigned known incident that it fails to detect. -/
def Dud (wire : Wire Observation Witness) (incident : Incident Observation) : Prop :=
  wire.enabled = true ∧
  incident.assignedWireId = some wire.wireId ∧
  ¬ RetroTrips wire incident

theorem calibrated_has_no_dud (registry : Registry Observation Witness)
    (corpus : List (Incident Observation)) (calibrated : Calibrated registry corpus)
    (wire : Wire Observation Witness) (wireIn : wire ∈ registry)
    (incident : Incident Observation) (incidentIn : incident ∈ corpus) :
    ¬ Dud wire incident := by
  intro dud
  exact dud.2.2 ((calibrated wire wireIn dud.1).2 incident incidentIn dud.2.1)

/-- An always-silent wire. It satisfies the earlier evaluator theorems—`check`
always passes and `observe` reports nothing—but is a dud when armed against an
assigned incident. -/
def alwaysSilentWire : Wire Nat Nat :=
  { wireId := 20, enabled := true, evaluate := fun _ => [] }

def silentIncident : Incident Nat :=
  { incidentId := 1, observation := 99, assignedWireId := some 20 }

theorem alwaysSilent_check_passes :
    check alwaysSilentWire silentIncident.observation = .passed 20 := by
  decide

theorem alwaysSilent_is_a_dud : Dud alwaysSilentWire silentIncident := by
  simp [Dud, RetroTrips, alwaysSilentWire, silentIncident]

/-! ## Closed-incident accounting and measured coverage -/

/-- An incident is covered when an enabled registry wire is the incident's
assigned wire and retro-trips on its observation. -/
def CoveredByWire : Registry Observation Witness → Incident Observation → Prop
  | [], _ => False
  | wire :: rest, incident =>
      (wire.enabled = true ∧ incident.assignedWireId = some wire.wireId ∧
        RetroTrips wire incident) ∨ CoveredByWire rest incident

/-- The incident's durable identity occurs on the explicit blind-spot map. -/
def OnBlindSpotMap (blindSpots : List Nat) (incident : Incident Observation) : Prop :=
  incident.incidentId ∈ blindSpots

/-- Every closed incident is either detected by an enabled calibrated wire or
retained explicitly as a blind spot. -/
def IncidentsAccountedFor (registry : Registry Observation Witness)
    (blindSpots : List Nat) (closed : List (Incident Observation)) : Prop :=
  ∀ incident ∈ closed,
    CoveredByWire registry incident ∨ OnBlindSpotMap blindSpots incident

noncomputable instance coveredByWireDecidable (registry : Registry Observation Witness)
    (incident : Incident Observation) : Decidable (CoveredByWire registry incident) := by
  exact Classical.propDecidable _

/-- Exact rational sensor coverage: wire-covered closed incidents divided by
all closed incidents. The empty corpus reports zero rather than asserting
vacuous completeness. -/
noncomputable def coverageNumber (registry : Registry Observation Witness)
    (closed : List (Incident Observation)) : ℚ :=
  match closed with
  | [] => 0
  | _ => ((closed.filter fun incident => decide (CoveredByWire registry incident)).length : ℚ) /
         (closed.length : ℚ)

theorem accounted_uncovered_is_on_blind_spot_map
    (registry : Registry Observation Witness) (blindSpots : List Nat)
    (closed : List (Incident Observation))
    (accounted : IncidentsAccountedFor registry blindSpots closed)
    (incident : Incident Observation) (incidentIn : incident ∈ closed)
    (uncovered : ¬ CoveredByWire registry incident) :
    OnBlindSpotMap blindSpots incident := by
  rcases accounted incident incidentIn with covered | mapped
  · exact False.elim (uncovered covered)
  · exact mapped

theorem coverageNumber_eq_one_iff_all_covered
    (registry : Registry Observation Witness)
    (closed : List (Incident Observation)) (nonempty : closed ≠ []) :
    coverageNumber registry closed = 1 ↔
      ∀ incident ∈ closed, CoveredByWire registry incident := by
  cases closed with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      simp only [coverageNumber]
      rw [div_eq_one_iff_eq]
      · norm_cast
        constructor
        · intro sameLength incident retained
          have allTrue := List.length_filter_eq_length_iff.mp sameLength
          have decided := allTrue incident retained
          simpa using decided
        · intro allCovered
          apply List.length_filter_eq_length_iff.mpr
          intro incident retained
          simp [allCovered incident retained]
      · have positiveDenominator : (0 : ℚ) < (tail.length : ℚ) + 1 := by
          positivity
        exact ne_of_gt (by simpa using positiveDenominator)

def uncoveredIncident : Incident Nat :=
  { incidentId := 2, observation := 7, assignedWireId := none }

theorem unaccounted_closed_incident_fails :
    ¬ IncidentsAccountedFor ([] : Registry Nat Nat) [] [uncoveredIncident] := by
  simp [IncidentsAccountedFor, CoveredByWire, OnBlindSpotMap, uncoveredIncident]

theorem mapped_incident_is_accounted :
    IncidentsAccountedFor ([] : Registry Nat Nat) [2] [uncoveredIncident] := by
  simp [IncidentsAccountedFor, CoveredByWire, OnBlindSpotMap, uncoveredIncident]

theorem mapped_incident_lowers_coverage :
    coverageNumber ([] : Registry Nat Nat) [uncoveredIncident] < 1 := by
  norm_num [coverageNumber, CoveredByWire, uncoveredIncident]

/-! ## Fail-safe response and whole-record conformance -/

/-- The retained response to one trip. The fields state whether the frozen
state was durably recorded, a typed stop-line was opened, an investigation was
parked, the outer reviewer was summoned, and the run was blocked. The runtime
currently retains pieces of these actions in separate report, repair, park and
Agency records, not one authoritative response record. -/
structure ResponseRecord where
  recorded : Bool
  stopLineOpened : Bool
  parked : Bool
  summoned : Bool
  blockedRun : Bool
  deriving DecidableEq, Repr

/-- Four rungs: the full response, then without the summon, then without the
park, then the record alone. The paper fixes two things about the ladder: it
"only ever degrades toward recording", and never toward blocking the run. The
order in which the other steps are dropped is not in the paper; it is the order
the runtime's `:park-and-summon` action degrades in (to stop-line, then to
record). `ConformingResponse` below is the paper's part. -/
inductive ResponseRung where
  | freezeRecordParkSummon
  | recordStopLinePark
  | recordStopLine
  | recordOnly
  deriving DecidableEq, Repr

def responseAtRung : ResponseRung → ResponseRecord
  | .freezeRecordParkSummon => ⟨true, true, true, true, false⟩
  | .recordStopLinePark => ⟨true, true, true, false, false⟩
  | .recordStopLine => ⟨true, true, false, false, false⟩
  | .recordOnly => ⟨true, false, false, false, false⟩

/-- A response lies on the paper's fail-safe ladder. -/
def OnResponseLadder (response : ResponseRecord) : Prop :=
  ∃ rung, response = responseAtRung rung

/-- The paper's minimum response invariant: preserve the durable record and
never block the run. -/
def ConformingResponse (response : ResponseRecord) : Prop :=
  response.recorded = true ∧ response.blockedRun = false

theorem every_response_rung_conforms (rung : ResponseRung) :
    ConformingResponse (responseAtRung rung) := by
  cases rung <;> simp [ConformingResponse, responseAtRung]

theorem response_without_record_not_on_ladder (response : ResponseRecord)
    (missing : response.recorded = false) : ¬ OnResponseLadder response := by
  rintro ⟨rung, rfl⟩
  cases rung <;> simp [responseAtRung] at missing

theorem blocking_response_not_on_ladder (response : ResponseRecord)
    (blocks : response.blockedRun = true) : ¬ OnResponseLadder response := by
  rintro ⟨rung, rfl⟩
  cases rung <;> simp [responseAtRung] at blocks

def droppedRecordResponse : ResponseRecord :=
  ⟨false, true, true, true, false⟩

def blockingResponse : ResponseRecord :=
  ⟨true, true, true, true, true⟩

theorem dropped_record_response_is_nonconforming :
    ¬ ConformingResponse droppedRecordResponse := by
  simp [ConformingResponse, droppedRecordResponse]

theorem blocking_response_is_nonconforming :
    ¬ ConformingResponse blockingResponse := by
  simp [ConformingResponse, blockingResponse]

/-- One trip and the response retained for it. -/
structure RespondedTrip (Observation : Type) where
  incident : Incident Observation
  response : ResponseRecord

/-- A complete R20 record conforms to the paper when the enabled registry is
calibrated, every closed incident is wire-covered or explicitly mapped, and
every retained trip received a non-blocking, record-preserving response. -/
def R20Conformant (registry : Registry Observation Witness)
    (calibrationCorpus closed : List (Incident Observation))
    (blindSpots : List Nat) (trips : List (RespondedTrip Observation)) : Prop :=
  Calibrated registry calibrationCorpus ∧
  IncidentsAccountedFor registry blindSpots closed ∧
  ∀ trip ∈ trips, ConformingResponse trip.response

end DarkTower.WarMachine.R20InteroceptiveTripwire
