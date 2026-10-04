import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# R10 scheduled-entrypoint route records

This module transcribes the record-level role checked by
`futon2/src/futon2/aif/scheduled_route_evidence.clj/verify-route!` and projected
by `futon2/src/futon2/aif/wm/apparatus_certificates.clj/r10-certificate`, read at
Futon2 commit `0f9587532031beb50a21091cc41cd10f4a16ff63`.

An accepted record says that exactly one retained launch joins the commission
and dispatch, and that its ordered tick entries and R8 rows cover the declared
plan with the required launch, index and predecessor identities. It does not
prove that a scheduler fired in the world, that the record is complete or
independently owned, or that R8 arithmetic is correct. The runtime verifier
itself refuses `:independently-retained-production` authority, so this module
does not close `Holes.wmRunsOnce` or certify production scheduling.

The transcription leaves out runtime schema tags, SHA/source pins,
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

end DarkTower.WarMachine.R10ScheduledEntrypoint
