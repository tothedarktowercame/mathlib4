import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# A scheduled tick is live only if something changed

In plain terms: a loop that runs on a schedule is alive when its ticks change
something that can be observed. A tick that fires and changes nothing must not
be reported as live, and a loop that has stopped changing anything should have
its schedule switched off, not left to report success.

Source status. This rule is stated here as a design requirement. Its grounding
in the active-inference literature has not been done: the obvious candidate is
that a step which yields no new observation leaves every belief where it was,
so nothing is inferred and nothing is learned, but no passage has been read
and cited for it yet. Until that is done this module should be read as a
candidate specification.

`LiveTick` is state change. `HonestLiveness` says no tick is labelled live
without one; a changed tick labelled not-live is allowed. `R10Conformant k`
adds that the schedule is not left enabled after `k` consecutive ticks that
changed nothing; no value of `k` is fixed. The theorems say that the number of
firings carries no information about liveness, and that honest labels alone do
not satisfy the disable rule.

Nothing in the rebuilt decision code (futon2 `src/futon2/aif/wm/` and the
namespaces it requires, read at `0f9587532`) records the observable state
before and after a tick, a per-tick liveness label, or whether the schedule is
enabled. Code written for this must satisfy `R10Conformant`.
-/

namespace DarkTower.WarMachine.R10ScheduledEntrypoint

/-! ## Liveness as state change -/

/-- One fired tick together with the observations needed to judge its
liveness. `beforeState` and `afterState` are the observable state before and
after the tick; `reportedLive` is the label the run gave the tick. Membership
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

/-- A live tick: observable state changed, rather
than merely the scheduler firing. -/
def LiveTick {State : Type} [DecidableEq State]
    (tick : TickOutcome State) : Prop :=
  ChangedState tick

/-- A run's liveness labels are honest exactly when every tick it labels live
actually changed observable state. The converse is intentionally not
required: the rule bars a false live label but does not say that every changed
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
not-live. -/
theorem honest_no_change_forces_not_live_labels {State : Type}
    [DecidableEq State] (ticks : List (TickOutcome State))
    (honest : HonestLiveness ticks)
    (unchanged : ∀ tick ∈ ticks, ¬ ChangedState tick) :
    ∀ tick ∈ ticks, tick.reportedLive = false := by
  intro tick retained
  cases h : tick.reportedLive with
  | false => rfl
  | true => exact False.elim (unchanged tick retained (honest tick retained h))

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

/-- A changed tick labelled not-live is permitted. The rule forbids false
green labels; it does not require every real change to receive a green label. -/
def missedLiveTick : TickOutcome Nat :=
  { beforeState := 4, afterState := 5, reportedLive := false }

theorem missedLive_is_permitted : HonestLiveness [missedLiveTick] := by
  intro tick retained labelled
  simp [missedLiveTick] at retained
  subst tick
  simp at labelled

/-- The disable rule with its unspecified window exposed as `k`.
`MustDisable k ticks` means `k` is a positive, available suffix and every tick
in that suffix failed to change observable state. Nothing fixes a value of
`k`; this module does not choose one. -/
def MustDisable {State : Type} [DecidableEq State]
    (k : Nat) (ticks : List (TickOutcome State)) : Prop :=
  0 < k ∧ k ≤ ticks.length ∧
    ∀ tick ∈ ticks.reverse.take k, ¬ ChangedState tick

/-- Any positive window within a wholly unchanged run meets the
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
enabled after the last of them. -/
structure RunRecord (State : Type) where
  ticks : List (TickOutcome State)
  scheduleEnabled : Bool

/-- A run record conforms to R10, for a disable window `k`, when no tick is
labelled live without a state change, and the schedule is not left enabled
after `k` consecutive ticks that changed nothing. No `k` is fixed. -/
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
