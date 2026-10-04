import Mathlib.Data.List.GetD

/-!
# R10 scheduled-entrypoint route records

This module transcribes the record-level role checked by
`futon2/src/futon2/aif/scheduled_route_evidence.clj/verify-route!` and projected
by `futon2/src/futon2/aif/wm/apparatus_certificates.clj/r10-certificate`, read at
Futon2 commit `0f9587532031beb50a21091cc41cd10f4a16ff63`.

An accepted record says that one retained scheduled launch precedes every
declared tick entry and that each tick entry precedes its corresponding R8
occurrence.  It does not prove that a scheduler fired in the world, that the
record is complete or independently owned, or that R8 arithmetic is correct.
The runtime verifier itself refuses `:independently-retained-production`
authority, so this module does not close `Holes.wmRunsOnce` or certify
production scheduling.
-/

namespace DarkTower.WarMachine.R10ScheduledEntrypoint

/-- The route-local fields retained for one planned tick.  `launchedBy` is the
launch identity copied onto the tick entry; the natural numbers are monotonic
positions in the bounded route record. -/
structure TickRoute (LaunchId TickId : Type*) where
  tickId : TickId
  launchedBy : LaunchId
  tickAt : Nat
  r8At : Nat
  deriving DecidableEq

/-- The bounded carrier needed to state R10's ordering role.  The production
record has further commission, dispatch, run, model, source-pin, observation,
candidate-support and predecessor-prediction fields; those joins are outside
this route-order predicate. -/
structure RouteRecord (LaunchId TickId : Type*) where
  scheduledLaunch : Option LaunchId
  scheduledLaunchAt : Nat
  tickPlan : List TickId
  ticks : List (TickRoute LaunchId TickId)
  deriving DecidableEq

/-- R10's record-level role: there is a retained scheduled launch, the tick
rows cover the declared plan in order, and that launch occurs before each tick
whose matching R8 occurrence occurs later. -/
def ScheduledRoute {LaunchId TickId : Type*}
    (record : RouteRecord LaunchId TickId) : Prop :=
  match record.scheduledLaunch with
  | none => False
  | some launchId =>
      record.ticks.map TickRoute.tickId = record.tickPlan ∧
      ∀ tick ∈ record.ticks,
        tick.launchedBy = launchId ∧
        record.scheduledLaunchAt < tick.tickAt ∧
        tick.tickAt < tick.r8At

/-- Content of an accepted route: every retained tick is causally bracketed
between the scheduled launch and its corresponding R8 occurrence. -/
theorem accepted_tick_is_between_launch_and_r8
    {LaunchId TickId : Type*} (record : RouteRecord LaunchId TickId)
    (accepted : ScheduledRoute record) (tick : TickRoute LaunchId TickId)
    (tickRetained : tick ∈ record.ticks) :
    record.scheduledLaunchAt < tick.tickAt ∧ tick.tickAt < tick.r8At := by
  cases launch : record.scheduledLaunch with
  | none => simp [ScheduledRoute, launch] at accepted
  | some launchId =>
      have accepted' := (show
        record.ticks.map TickRoute.tickId = record.tickPlan ∧
          ∀ tick ∈ record.ticks,
            tick.launchedBy = launchId ∧
            record.scheduledLaunchAt < tick.tickAt ∧ tick.tickAt < tick.r8At
        from by simpa [ScheduledRoute, launch] using accepted)
      have routes := accepted'.2 tick tickRetained
      exact routes.2

/-- A concrete retained route accepted by the R10 predicate. -/
def positiveRecord : RouteRecord Nat Nat :=
  { scheduledLaunch := some 7
    scheduledLaunchAt := 3
    tickPlan := [10, 11]
    ticks :=
      [{ tickId := 10, launchedBy := 7, tickAt := 4, r8At := 5 },
       { tickId := 11, launchedBy := 7, tickAt := 6, r8At := 8 }] }

theorem positiveRecord_is_scheduled : ScheduledRoute positiveRecord := by
  refine ⟨rfl, ?_⟩
  intro tick retained
  simp [positiveRecord] at retained
  rcases retained with rfl | rfl <;> decide

/-- Negative control: the same ordered tick and R8 occurrence cannot be
accepted when the route retains no scheduled launch before the tick. -/
def missingLaunchRecord : RouteRecord Nat Nat :=
  { scheduledLaunch := none
    scheduledLaunchAt := 3
    tickPlan := [10]
    ticks := [{ tickId := 10, launchedBy := 7, tickAt := 4, r8At := 5 }] }

theorem missingLaunchRecord_is_rejected :
    ¬ ScheduledRoute missingLaunchRecord := by
  simp [ScheduledRoute, missingLaunchRecord]

end DarkTower.WarMachine.R10ScheduledEntrypoint
