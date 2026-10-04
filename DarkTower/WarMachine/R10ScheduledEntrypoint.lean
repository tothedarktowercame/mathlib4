import Mathlib.Data.List.GetD

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
and exact ordered R8 coverage. `eraseDups` changes a plan exactly when that
plan repeats a tick identity. -/
def checkRoute (record : RouteRecord) : Bool :=
  (record.launch.commissionId == record.commissionId) &&
  (record.launch.dispatchId == record.dispatchId) &&
  (record.launchHistory.filter
      (fun launch => (launch.commissionId == record.commissionId) &&
                     (launch.dispatchId == record.dispatchId)) == [record.launch]) &&
  (record.tickPlan.eraseDups == record.tickPlan) &&
  (record.tickEntries == expectedTickEntries record.launch.launchId record.tickPlan) &&
  (record.r8TickIds == record.tickPlan)

/-- Propositional reading of the executable R10 route checker. -/
def ScheduledRoute (record : RouteRecord) : Prop :=
  checkRoute record = true

theorem checkRoute_eq_true_iff (record : RouteRecord) :
    checkRoute record = true ↔ ScheduledRoute record := by
  rfl

/-- Combining launch-history uniqueness with the tick-plan clause: an accepted
record's complete tick sequence is tied to the sole launch retained for this
commission and dispatch. -/
theorem accepted_ticks_use_unique_joined_launch (record : RouteRecord)
    (accepted : ScheduledRoute record) :
    record.launchHistory.filter
        (fun launch => (launch.commissionId == record.commissionId) &&
                       (launch.dispatchId == record.dispatchId)) = [record.launch] ∧
    record.tickEntries = expectedTickEntries record.launch.launchId record.tickPlan := by
  have clauses := accepted
  simp [ScheduledRoute, checkRoute] at clauses
  exact ⟨clauses.1.1.1.2, clauses.1.2⟩

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

theorem positiveRecord_is_scheduled : ScheduledRoute positiveRecord := by
  show checkRoute positiveRecord = true
  decide

/-- Control 1: two launches match the same commission and dispatch. -/
def duplicateLaunchRecord : RouteRecord :=
  { positiveRecord with
    launchHistory := [goodLaunch,
      { launchId := 8, commissionId := 20, dispatchId := 30 }] }

theorem duplicateLaunchRecord_is_rejected :
    checkRoute duplicateLaunchRecord = false := by
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
    checkRoute wrongTickLaunchRecord = false := by
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
    checkRoute stalePredecessorRecord = false := by
  decide

end DarkTower.WarMachine.R10ScheduledEntrypoint
