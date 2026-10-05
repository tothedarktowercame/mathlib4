import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# R10 scheduled observer entrypoint

## The role

`p4ng/sec-catalog.tex`, "Scheduled Observer Entrypoint (R10, the No-Op
Trap)", gives R10 its role: "liveness is a property of state change, not of
the scheduler firing". A scheduler whose ticks cache or no-op writes a green
"it ran" row at every firing while nothing changes. The paper's move is to
"gate 'live' on evidence that a tick changed observable state ... not merely
that it fired", and "when the loop can only no-op, disable the schedule rather
than let it paint green".

The second half of this module states that role (`LiveTick`,
`HonestLiveness`, `MustDisable`) and what a run record must satisfy to conform
to it (`R10Conformant`). The statements come from the paper's paragraph, not
from the implementation.

## What the implementation checks instead

The first half (`ScheduledRoute`) transcribes the route check made by
`futon2/src/futon2/aif/scheduled_route_evidence.clj/verify-route!` and projected
by `futon2/src/futon2/aif/wm/apparatus_certificates.clj/r10-certificate`, read at
Futon2 commit `0f9587532031beb50a21091cc41cd10f4a16ff63`: exactly one retained
launch joins the commission and dispatch, and its ordered tick entries and R8
rows cover the declared plan with the required launch, index and predecessor
identities. That says the ticks belong to the schedule. It is not the role:
`scheduledRoute_does_not_imply_live_tick` exhibits an accepted route whose
ticks are all no-ops.

At that commit neither `verify-route!` nor `r10-certificate` checks state
change, liveness labels or the disable rule, and the retained R10 records have
no field for observable state before or after a tick, for a per-tick liveness
label, or for whether the schedule is enabled. So no run record can yet be
tested for `R10Conformant`; supplying those fields is what conformance of the
implementation requires.

`ScheduledRoute` does not prove that a scheduler fired in the world, that the
record is complete or independently owned, or that R8 arithmetic is correct.
The runtime verifier itself refuses `:independently-retained-production`
authority, so this module does not close `Holes.wmRunsOnce`. The route
transcription leaves out runtime schema tags, SHA/source pins,
run/model/revision joins, observation payload validation, candidate-support
coverage, and detailed prediction/occurrence input agreement.
-/

namespace DarkTower.WarMachine.R10ScheduledEntrypoint

/-- A retained launch-history row. The fields stand for runtime `:launch/id`,
`:commission/id`, and `:dispatch/id`. -/
structure Launch where
  launchId : Nat
  commissionId : Nat
  dispatchId : Nat
  deriving DecidableEq, Repr

/-- A retained tick-entry row. The fields stand for runtime `:tick/id`,
`:launch/id`, `:tick/index`, and the prediction row's
`:predecessor/tick-id` (`none` for the initial tick). -/
structure TickEntry where
  tickId : Nat
  launchId : Nat
  tickIndex : Nat
  predecessorTickId : Option Nat
  deriving DecidableEq, Repr

/-- The bounded R10 carrier. `commissionId` and `dispatchId` stand for the
joined commission and successful dispatch; `launch` is the resolved
`:run-launch`; `launchHistory` is `:launch-history`; `tickPlan` is
`:tick/plan`; `tickEntries` are `:tick-entries`; and `r8TickIds` are the
ordered `:tick/id` values of `:r8-occurrences`. -/
structure RouteRecord where
  commissionId : Nat
  dispatchId : Nat
  launch : Launch
  launchHistory : List Launch
  tickPlan : List Nat
  tickEntries : List TickEntry
  r8TickIds : List Nat
  deriving DecidableEq, Repr

/-- The tick entries forced by a launch and an ordered plan. The list position
is the runtime `:tick/index`; every non-initial predecessor is the preceding
plan entry. -/
def expectedTickEntries (launchId : Nat) (plan : List Nat) : List TickEntry :=
  plan.mapIdx fun index tickId =>
    { tickId := tickId
      launchId := launchId
      tickIndex := index
      predecessorTickId := if index = 0 then none else plan[index - 1]? }

/-- Executable R10 predicate, clause-for-clause at the retained structural
boundary: one matching launch, unique plan entries, exact ordered tick rows,
and exact ordered R8 coverage. -/
def checkRoute (record : RouteRecord) : Bool :=
  (record.launch.commissionId == record.commissionId) &&
  (record.launch.dispatchId == record.dispatchId) &&
  (record.launchHistory.filter
      (fun launch => (launch.commissionId == record.commissionId) &&
                     (launch.dispatchId == record.dispatchId)) == [record.launch]) &&
  decide record.tickPlan.Nodup &&
  (record.tickEntries == expectedTickEntries record.launch.launchId record.tickPlan) &&
  (record.r8TickIds == record.tickPlan)

/-- R10's record-level role, stated as propositions and independently of the
checker. In the order of `verify-route!`: the launch joins the commission and
dispatch; the launch history holds exactly one launch for that commission and
dispatch, and it is this launch; no tick identity repeats in the plan; the
tick entries are the ones the launch and plan force; the R8 rows cover the plan
in order. -/
def ScheduledRoute (record : RouteRecord) : Prop :=
  record.launch.commissionId = record.commissionId ∧
  record.launch.dispatchId = record.dispatchId ∧
  record.launchHistory.filter
      (fun launch => (launch.commissionId == record.commissionId) &&
                     (launch.dispatchId == record.dispatchId)) = [record.launch] ∧
  record.tickPlan.Nodup ∧
  record.tickEntries = expectedTickEntries record.launch.launchId record.tickPlan ∧
  record.r8TickIds = record.tickPlan

/-- The executable checker decides the stated role: it accepts exactly the
records that satisfy every clause of `ScheduledRoute`. A checker that dropped
or weakened a clause would not satisfy this. -/
theorem checkRoute_eq_true_iff (record : RouteRecord) :
    checkRoute record = true ↔ ScheduledRoute record := by
  simp [checkRoute, ScheduledRoute, and_assoc]

/-- A consequence that needs the launch-history clause and the tick-entry
clause together: in an accepted record, every tick entry carries the identity
of every launch the history holds for this commission and dispatch. There is
no tick launched by anything else, and no second launch a tick could belong
to. -/
theorem accepted_ticks_use_unique_joined_launch (record : RouteRecord)
    (accepted : ScheduledRoute record)
    (launch : Launch) (retained : launch ∈ record.launchHistory)
    (joinsCommission : launch.commissionId = record.commissionId)
    (joinsDispatch : launch.dispatchId = record.dispatchId)
    (tick : TickEntry) (tickRetained : tick ∈ record.tickEntries) :
    tick.launchId = launch.launchId := by
  obtain ⟨_, _, unique, _, entries, _⟩ := accepted
  have isTheLaunch : launch = record.launch := by
    have member : launch ∈ record.launchHistory.filter
        (fun launch => (launch.commissionId == record.commissionId) &&
                       (launch.dispatchId == record.dispatchId)) := by
      simp [List.mem_filter, retained, joinsCommission, joinsDispatch]
    rw [unique] at member
    simpa using member
  rw [entries] at tickRetained
  obtain ⟨index, _, rfl⟩ := List.mem_mapIdx.mp tickRetained
  simp [isTheLaunch]

def goodLaunch : Launch :=
  { launchId := 7, commissionId := 20, dispatchId := 30 }

/-- Positive two-tick witness. -/
def positiveRecord : RouteRecord :=
  { commissionId := 20
    dispatchId := 30
    launch := goodLaunch
    launchHistory := [goodLaunch]
    tickPlan := [10, 11]
    tickEntries := expectedTickEntries 7 [10, 11]
    r8TickIds := [10, 11] }

theorem positiveRecord_is_scheduled : ScheduledRoute positiveRecord :=
  (checkRoute_eq_true_iff positiveRecord).mp (by decide)

/-- Control 1: two launches match the same commission and dispatch. -/
def duplicateLaunchRecord : RouteRecord :=
  { positiveRecord with
    launchHistory := [goodLaunch,
      { launchId := 8, commissionId := 20, dispatchId := 30 }] }

theorem duplicateLaunchRecord_is_rejected :
    ¬ ScheduledRoute duplicateLaunchRecord := by
  rw [← checkRoute_eq_true_iff]
  decide

/-- Control 2: the tick row names a launch other than the uniquely retained
launch. -/
def wrongTickLaunchRecord : RouteRecord :=
  { positiveRecord with
    tickEntries :=
      [{ tickId := 10, launchId := 8, tickIndex := 0,
         predecessorTickId := none },
       { tickId := 11, launchId := 7, tickIndex := 1,
         predecessorTickId := some 10 }] }

theorem wrongTickLaunchRecord_is_rejected :
    ¬ ScheduledRoute wrongTickLaunchRecord := by
  rw [← checkRoute_eq_true_iff]
  decide

/-- Control 3: the second tick predicts from a tick other than the immediately
preceding plan entry. -/
def stalePredecessorRecord : RouteRecord :=
  { positiveRecord with
    tickEntries :=
      [{ tickId := 10, launchId := 7, tickIndex := 0,
         predecessorTickId := none },
       { tickId := 11, launchId := 7, tickIndex := 1,
         predecessorTickId := some 99 }] }

theorem stalePredecessorRecord_is_rejected :
    ¬ ScheduledRoute stalePredecessorRecord := by
  rw [← checkRoute_eq_true_iff]
  decide

/-! ## The paper's state-change account of liveness -/

/-- One fired tick together with the observations needed to judge its
liveness. `beforeState` and `afterState` stand for the paper's observable
state before and after the tick; there is no corresponding retained R10 field
at Futon2 `0f9587532031beb50a21091cc41cd10f4a16ff63`. `reportedLive` stands
for the green/live label whose honesty the paper requires; there is likewise
no such per-tick liveness-label field in `verify-route!`'s record. Membership
in a list of `TickOutcome`s means that the tick fired. -/
structure TickOutcome (State : Type) where
  beforeState : State
  afterState : State
  reportedLive : Bool
  deriving Repr

/-- The observable state changed across this tick. -/
def ChangedState {State : Type} [DecidableEq State]
    (tick : TickOutcome State) : Prop :=
  tick.beforeState ≠ tick.afterState

/-- The paper's definition of a live tick: observable state changed, rather
than merely the scheduler firing. -/
def LiveTick {State : Type} [DecidableEq State]
    (tick : TickOutcome State) : Prop :=
  ChangedState tick

/-- A run's liveness labels are honest exactly when every tick it labels live
actually changed observable state. The converse is intentionally not
required: the paper bars a false green row but does not say that every changed
tick must be labelled live. -/
def HonestLiveness {State : Type} [DecidableEq State]
    (ticks : List (TickOutcome State)) : Prop :=
  ∀ tick ∈ ticks, tick.reportedLive = true → ChangedState tick

/-- A canonical fired no-op tick. -/
def noOpTick (state : State) : TickOutcome State :=
  { beforeState := state, afterState := state, reportedLive := false }

/-- Scheduler firing carries no information about liveness: for every number
of firings there is a run of exactly that length in which no tick is live. -/
theorem firing_carries_no_liveness_information (State : Type)
    [DecidableEq State] (state : State) (n : Nat) :
    ∃ ticks : List (TickOutcome State),
      ticks.length = n ∧ ∀ tick ∈ ticks, ¬ LiveTick tick := by
  refine ⟨List.replicate n (noOpTick state), ?_, ?_⟩
  · simp
  · intro tick retained
    have : tick = noOpTick state := List.eq_of_mem_replicate retained
    subst tick
    simp [LiveTick, ChangedState, noOpTick]

/-- If no fired tick changed state, then the run contains no live tick,
regardless of how many ticks fired. -/
theorem no_changed_state_has_no_live_tick {State : Type} [DecidableEq State]
    (ticks : List (TickOutcome State))
    (unchanged : ∀ tick ∈ ticks, ¬ ChangedState tick) :
    ∀ tick ∈ ticks, ¬ LiveTick tick := by
  intro tick retained
  exact unchanged tick retained

/-- On an honestly labelled run with no state change, every label must be
not-live. This is the no-false-green half of the paper's rule. -/
theorem honest_no_change_forces_not_live_labels {State : Type}
    [DecidableEq State] (ticks : List (TickOutcome State))
    (honest : HonestLiveness ticks)
    (unchanged : ∀ tick ∈ ticks, ¬ ChangedState tick) :
    ∀ tick ∈ ticks, tick.reportedLive = false := by
  intro tick retained
  cases h : tick.reportedLive with
  | false => rfl
  | true => exact False.elim (unchanged tick retained (honest tick retained h))

/-- Two no-op outcomes corresponding to `positiveRecord`'s two scheduled
ticks. They make the route/liveness gap concrete without adding liveness
fields to the route carrier. -/
def positiveRouteNoOps : List (TickOutcome Nat) :=
  [noOpTick 0, noOpTick 0]

/-- `ScheduledRoute` does not imply a live tick. The accepted two-tick route
has a same-length outcome record in which every fired tick is a no-op. -/
theorem scheduledRoute_does_not_imply_live_tick :
    ScheduledRoute positiveRecord ∧
    positiveRouteNoOps.length = positiveRecord.tickPlan.length ∧
    (∀ tick ∈ positiveRouteNoOps, ¬ LiveTick tick) := by
  refine ⟨positiveRecord_is_scheduled, ?_, ?_⟩
  · decide
  · intro tick retained
    simp [positiveRouteNoOps, noOpTick] at retained
    subst tick
    simp [LiveTick, ChangedState]

/-- Control: a green/live label on an unchanged tick is dishonest. -/
def falseGreenTick : TickOutcome Nat :=
  { beforeState := 4, afterState := 4, reportedLive := true }

theorem falseGreen_is_rejected : ¬ HonestLiveness [falseGreenTick] := by
  intro honest
  have changed := honest falseGreenTick (by simp) rfl
  exact changed rfl

/-- Positive control: a changed tick labelled live satisfies the criterion. -/
def honestGreenTick : TickOutcome Nat :=
  { beforeState := 4, afterState := 5, reportedLive := true }

theorem honestGreen_is_accepted : HonestLiveness [honestGreenTick] := by
  intro tick retained _
  simp only [List.mem_singleton] at retained
  subst tick
  simp [ChangedState, honestGreenTick]

/-- A changed tick labelled not-live is permitted. The paper forbids false
green labels; it does not require every real change to receive a green label. -/
def missedLiveTick : TickOutcome Nat :=
  { beforeState := 4, afterState := 5, reportedLive := false }

theorem missedLive_is_permitted : HonestLiveness [missedLiveTick] := by
  intro tick retained labelled
  simp [missedLiveTick] at retained
  subst tick
  simp at labelled

/-- The paper's disable rule with its unspecified window exposed as `k`.
`MustDisable k ticks` means `k` is a positive, available suffix and every tick
in that suffix failed to change observable state. The paper fixes no value of
`k`; this module does not choose one. -/
def MustDisable {State : Type} [DecidableEq State]
    (k : Nat) (ticks : List (TickOutcome State)) : Prop :=
  0 < k ∧ k ≤ ticks.length ∧
    ∀ tick ∈ ticks.reverse.take k, ¬ ChangedState tick

/-- Any positive window within a wholly unchanged run meets the paper's
parameterised disable condition. -/
theorem no_change_requires_disable_for_every_available_window
    {State : Type} [DecidableEq State]
    (ticks : List (TickOutcome State))
    (unchanged : ∀ tick ∈ ticks, ¬ ChangedState tick)
    (k : Nat) (positive : 0 < k) (available : k ≤ ticks.length) :
    MustDisable k ticks := by
  refine ⟨positive, available, ?_⟩
  intro tick retained
  apply unchanged tick
  have inReverse : tick ∈ ticks.reverse := List.mem_of_mem_take retained
  simpa using inReverse

/-! ## Conformance of a run record to the role -/

instance honestLivenessDecidable {State : Type} [DecidableEq State]
    (ticks : List (TickOutcome State)) : Decidable (HonestLiveness ticks) := by
  unfold HonestLiveness ChangedState
  infer_instance

instance mustDisableDecidable {State : Type} [DecidableEq State]
    (k : Nat) (ticks : List (TickOutcome State)) : Decidable (MustDisable k ticks) := by
  unfold MustDisable ChangedState
  infer_instance

/-- What a scheduled run must retain to be judged against the role: the
outcome of each fired tick, oldest first, and whether the schedule is still
enabled after the last of them. No such record exists at Futon2
`0f9587532031beb50a21091cc41cd10f4a16ff63`. -/
structure RunRecord (State : Type) where
  ticks : List (TickOutcome State)
  scheduleEnabled : Bool

/-- A run record conforms to R10, for a disable window `k`, when no tick is
labelled live without a state change, and the schedule is not left enabled
after `k` consecutive ticks that changed nothing. The paper fixes no `k`. -/
def R10Conformant {State : Type} [DecidableEq State]
    (k : Nat) (run : RunRecord State) : Prop :=
  HonestLiveness run.ticks ∧
  (MustDisable k run.ticks → run.scheduleEnabled = false)

instance r10ConformantDecidable {State : Type} [DecidableEq State]
    (k : Nat) (run : RunRecord State) : Decidable (R10Conformant k run) := by
  unfold R10Conformant
  infer_instance

/-- A conforming run in which nothing changed, long enough to fill the window,
has its schedule disabled, whatever the number of firings. -/
theorem conformant_inert_run_is_disabled {State : Type} [DecidableEq State]
    (k : Nat) (run : RunRecord State) (conformant : R10Conformant k run)
    (unchanged : ∀ tick ∈ run.ticks, ¬ ChangedState tick)
    (positive : 0 < k) (available : k ≤ run.ticks.length) :
    run.scheduleEnabled = false :=
  conformant.2
    (no_change_requires_disable_for_every_available_window run.ticks unchanged
      k positive available)

/-- Control: three no-op ticks, none labelled live, schedule still enabled.
The labels are honest, and the run does not conform: the disable rule is a
requirement of its own, not a consequence of honest labels. -/
def inertButEnabledRun : RunRecord Nat :=
  { ticks := [noOpTick 0, noOpTick 0, noOpTick 0], scheduleEnabled := true }

theorem inertButEnabledRun_labels_are_honest :
    HonestLiveness inertButEnabledRun.ticks := by
  decide

theorem inertButEnabledRun_does_not_conform :
    ¬ R10Conformant 3 inertButEnabledRun := by
  decide

/-- Control: the same ticks with the schedule disabled conform. -/
theorem inertAndDisabledRun_conforms :
    R10Conformant 3 { inertButEnabledRun with scheduleEnabled := false } := by
  decide

/-- Control: a run whose last tick changed state may stay enabled. -/
theorem liveRun_may_stay_enabled :
    R10Conformant 3
      ({ ticks := [noOpTick 0, noOpTick 0, honestGreenTick],
         scheduleEnabled := true } : RunRecord Nat) := by
  decide

end DarkTower.WarMachine.R10ScheduledEntrypoint
