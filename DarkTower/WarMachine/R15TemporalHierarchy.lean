import Mathlib.Tactic

/-!
# Counts of what worked, carried from one tick to the next

In plain terms: the agent keeps, for each policy, a count of the times that
policy worked. A count changes only when an outcome was actually
witnessed, it changes by exactly one, and the next decision is made with the
updated counts, not the old ones.

Source. Parr, Pezzulo and Friston (2022), p. 209: "habits can be acquired by
executing goal-directed policies and then caching information about which
policies are successful in which contexts. The cached information can be
incorporated as a prior value of policies". Friston et al. (2016) learn that
prior as Dirichlet concentration counts. `R15HabitPrior` turns these counts
into the prior and says where it enters selection.

This module is a specification. `advance` is the count update, and
`TwoTickFeedback` is what a record of two consecutive ticks must satisfy: the
outcome was witnessed, the counts after are exactly the update of the counts
before, and the second tick used the counts after. It proves that an accepted
record always changes the counts, changes no other policy's, and that no
unwitnessed outcome is ever accepted.

Two things here are not from the cited sources. The requirement that the
outcome be witnessed is this system's condition that a count respond to what
happened and not to the model's own forecast. The second count, of failures,
is carried in `BetaCounts.beta` and updated by a failure; the habit prior does
not read it.

Counts are kept per policy, as in the sources: Parr p. 209 caches "which
policies are successful", and Friston et al. (2016) :675-678 count how often
each policy was encountered. The key type is any type with decidable
equality; `R20HabitPrior` keys the counts by the menu's `Policy`. (Until
2026-10-22 the counts were keyed by an "action class", transcribed from the
earlier implementation's per-class slow state; no cited source keeps habit
counts by class, and Joe ruled the class layer out on 2026-10-22.)

Counts are natural numbers and an unlisted policy starts at (1, 1). A state is
a list of entries, and `TwoTickFeedback` compares lists, so two states holding
the same entries in different orders are different here. Restating the clauses
through `countsFor`, policy by policy, would remove that; it is not done.

Nothing in the rebuilt decision code (futon2 `src/futon2/aif/wm/` and the
namespaces it requires, read at `0f9587532`) computes or consumes these
counts. Code written for this must satisfy `TwoTickFeedback`.
-/

namespace DarkTower.WarMachine.R15TemporalHierarchy

/-- The two counts kept for one policy. -/
structure BetaCounts where
  /-- One plus the number of witnessed successes. -/
  alpha : Nat
  /-- One plus the number of witnessed failures. -/
  beta : Nat
  deriving DecidableEq, Repr

/-- The counts for finitely many policies, as policy/count pairs. -/
abbrev SlowState (Key : Type) := List (Key × BetaCounts)

/-- The counts of a policy with no witnessed outcome yet: (1, 1). -/
def freshCounts : BetaCounts := { alpha := 1, beta := 1 }

variable {Key : Type} [DecidableEq Key]

/-- The counts of one policy; an unlisted policy has the fresh counts. -/
def countsFor : SlowState Key → Key → BetaCounts
  | [], _ => freshCounts
  | (key, counts) :: rest, policy =>
      if key = policy then counts else countsFor rest policy

/-- Replace the counts of one policy, appending the policy if unlisted. -/
def setCounts : SlowState Key → Key → BetaCounts → SlowState Key
  | [], policy, counts => [(policy, counts)]
  | (key, prior) :: rest, policy, counts =>
      if key = policy then (key, counts) :: rest
      else (key, prior) :: setCounts rest policy counts

theorem countsFor_setCounts_same (state : SlowState Key) (policy : Key)
    (counts : BetaCounts) :
    countsFor (setCounts state policy counts) policy = counts := by
  induction state with
  | nil => simp [setCounts, countsFor]
  | cons entry rest ih =>
      rcases entry with ⟨key, prior⟩
      by_cases key = policy <;> simp [setCounts, countsFor, *]

theorem countsFor_setCounts_other (state : SlowState Key) (policy other : Key)
    (counts : BetaCounts) (different : other ≠ policy) :
    countsFor (setCounts state policy counts) other = countsFor state other := by
  induction state with
  | nil =>
      have reverse : policy ≠ other := Ne.symm different
      simp [setCounts, countsFor, reverse]
  | cons entry rest ih =>
      rcases entry with ⟨key, prior⟩
      by_cases target : key = policy
      · subst key
        have reverse : policy ≠ other := Ne.symm different
        simp [setCounts, countsFor, reverse]
      · by_cases observed : key = other
        · subst key
          simp [setCounts, countsFor, target]
        · simp [setCounts, countsFor, target, observed, ih]

/-- One outcome of the fast loop: the policy taken, whether the outcome was
witnessed, and whether it succeeded. -/
structure FastOutcome (Key : Type) where
  policy : Key
  witnessed : Bool
  succeeded : Bool
  deriving DecidableEq, Repr

/-- The one-emission Beta update used by `advance-slow-state`. -/
def updatedCounts (prior : BetaCounts) (succeeded : Bool) : BetaCounts :=
  if succeeded then { prior with alpha := prior.alpha + 1 }
  else { prior with beta := prior.beta + 1 }

/-- Fold one fast outcome into its policy's counts. Witness admission is kept in
`TwoTickFeedback`; the arithmetic function is total so rejected controls can
still state what their untrusted payload claimed. -/
def advance (before : SlowState Key) (outcome : FastOutcome Key) : SlowState Key :=
  setCounts before outcome.policy
    (updatedCounts (countsFor before outcome.policy) outcome.succeeded)

/-- The retained two-tick carrier. `before` and `after` stand for
`:slow-state-before` and `:slow-state-after`; `outcome` for the independently
witnessed fast result; and `nextConsumed` for
`:next-tick-consumed-slow-state`. -/
structure TwoTickRecord (Key : Type) where
  before : SlowState Key
  outcome : FastOutcome Key
  after : SlowState Key
  nextConsumed : SlowState Key
  deriving DecidableEq, Repr

/-- R15's role, stated without the checker: only a witnessed fast outcome may
update the slow state, the retained after-state is the exact update, and the
next fast tick consumes that updated slow state. -/
def TwoTickFeedback (record : TwoTickRecord Key) : Prop :=
  record.outcome.witnessed = true ∧
  record.after = advance record.before record.outcome ∧
  record.nextConsumed = record.after

/-- Executable checker for the retained two-tick correspondence. -/
def checkTwoTickFeedback (record : TwoTickRecord Key) : Bool :=
  record.outcome.witnessed &&
  decide (record.after = advance record.before record.outcome) &&
  decide (record.nextConsumed = record.after)

theorem checkTwoTickFeedback_eq_true_iff (record : TwoTickRecord Key) :
    checkTwoTickFeedback record = true ↔ TwoTickFeedback record := by
  simp [checkTwoTickFeedback, TwoTickFeedback, and_assoc]

theorem updatedCounts_ne (prior : BetaCounts) (succeeded : Bool) :
    updatedCounts prior succeeded ≠ prior := by
  intro unchanged
  cases succeeded
  · have counts := congrArg BetaCounts.beta unchanged
    simp [updatedCounts] at counts
  · have counts := congrArg BetaCounts.alpha unchanged
    simp [updatedCounts] at counts

theorem advance_ne_before (before : SlowState Key) (outcome : FastOutcome Key) :
    advance before outcome ≠ before := by
  intro unchanged
  have observed := congrArg (fun state => countsFor state outcome.policy) unchanged
  unfold advance at observed
  rw [countsFor_setCounts_same] at observed
  exact updatedCounts_ne (countsFor before outcome.policy) outcome.succeeded observed

/-- Every accepted record changes the slow state; the certificate's inequality
is derived from the one-count update rather than trusted as an extra flag. -/
theorem accepted_before_ne_after (record : TwoTickRecord Key)
    (accepted : TwoTickFeedback record) : record.before ≠ record.after := by
  rw [accepted.2.1]
  exact (advance_ne_before record.before record.outcome).symm

/-- Updating one policy leaves the Beta counts of every other policy unchanged. -/
theorem accepted_other_policy_unchanged (record : TwoTickRecord Key)
    (accepted : TwoTickFeedback record) (other : Key)
    (different : other ≠ record.outcome.policy) :
    countsFor record.after other = countsFor record.before other := by
  rw [accepted.2.1]
  exact countsFor_setCounts_other _ _ _ _ different

/-- Universally, no unwitnessed outcome is accepted, regardless of any of the
three supplied slow states. -/
theorem unwitnessed_never_accepted (record : TwoTickRecord Key)
    (unwitnessed : record.outcome.witnessed = false) :
    ¬ TwoTickFeedback record := by
  intro accepted
  have witnessed := accepted.1
  rw [unwitnessed] at witnessed
  exact Bool.noConfusion witnessed

/-! Examples with policies numbered 10 and 20. -/

def initialState : SlowState Nat := [(10, { alpha := 2, beta := 3 }), (20, { alpha := 4, beta := 5 })]
def successOutcome : FastOutcome Nat := { policy := 10, witnessed := true, succeeded := true }
def failureOutcome : FastOutcome Nat := { policy := 20, witnessed := true, succeeded := false }

/-- Positive witnessed-success record. -/
def successRecord : TwoTickRecord Nat :=
  { before := initialState
    outcome := successOutcome
    after := advance initialState successOutcome
    nextConsumed := advance initialState successOutcome }

theorem successRecord_is_feedback : TwoTickFeedback successRecord := by
  rw [← checkTwoTickFeedback_eq_true_iff]
  decide

/-- Positive witnessed-failure record. -/
def failureRecord : TwoTickRecord Nat :=
  { before := initialState
    outcome := failureOutcome
    after := advance initialState failureOutcome
    nextConsumed := advance initialState failureOutcome }

theorem failureRecord_is_feedback : TwoTickFeedback failureRecord := by
  rw [← checkTwoTickFeedback_eq_true_iff]
  decide

/-- Control A: arithmetic and consumption agree, but the outcome was not
witnessed. -/
def unwitnessedRecord : TwoTickRecord Nat :=
  let outcome := { successOutcome with witnessed := false }
  { before := initialState, outcome := outcome,
    after := advance initialState outcome, nextConsumed := advance initialState outcome }

theorem unwitnessedRecord_is_rejected : ¬ TwoTickFeedback unwitnessedRecord :=
  unwitnessed_never_accepted unwitnessedRecord (by decide)

/-- Control B: the update is correct, but the next tick consumed stale state. -/
def staleConsumptionRecord : TwoTickRecord Nat :=
  { successRecord with nextConsumed := initialState }

theorem staleConsumptionRecord_is_rejected : ¬ TwoTickFeedback staleConsumptionRecord := by
  intro accepted
  have consumed := accepted.2.2
  have changed := accepted_before_ne_after staleConsumptionRecord accepted
  change staleConsumptionRecord.before = staleConsumptionRecord.after at consumed
  exact changed consumed

/-- Control C: after-state changed, but by updating another policy rather than
the witnessed outcome's policy. Consumption faithfully carries that wrong state. -/
def wrongPolicyState : SlowState Nat :=
  setCounts initialState 20 (updatedCounts (countsFor initialState 20) true)

def wrongUpdateRecord : TwoTickRecord Nat :=
  { before := initialState, outcome := successOutcome,
    after := wrongPolicyState, nextConsumed := wrongPolicyState }

theorem wrongUpdateRecord_after_changed : wrongUpdateRecord.after ≠ wrongUpdateRecord.before := by
  decide

theorem wrongUpdateRecord_is_rejected : ¬ TwoTickFeedback wrongUpdateRecord := by
  intro accepted
  have arithmetic := accepted.2.1
  norm_num [wrongUpdateRecord, wrongPolicyState, advance, initialState, successOutcome,
    setCounts, countsFor, updatedCounts] at arithmetic

end DarkTower.WarMachine.R15TemporalHierarchy
