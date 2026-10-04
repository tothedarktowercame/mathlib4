import Mathlib.Tactic

/-!
# R15 two-tick temporal hierarchy

This module states the record-level two-tick feedback role implemented by
`futon2/src/futon2/aif/temporal_hierarchy.clj/advance-slow-state`, using
`futon2/src/futon2/aif/intrinsic_values.clj/next-update-record`, and projected
by `r15-certificate` in
`futon2/src/futon2/aif/wm/apparatus_certificates.clj`, read at Futon2 commit
`0f9587532031beb50a21091cc41cd10f4a16ff63`. It also states the central
transition checked, with substantially more identity/provenance machinery, by
`machine_slow_feedback_evidence.clj/validate-transition` and
`verify-feedback`.

Runtime `:alpha` and `:beta` are doubles. Here they are natural-number counts:
one witnessed success increments alpha once, and one witnessed failure
increments beta once. An absent action class has the runtime's fresh Beta(1,1)
prior. In the production call, `next-update-record` receives exactly one
emission and either one or zero follow-throughs, so its general defensive cap
reduces exactly to these two updates; it applies no decay, rolling window, or
count cap.

This module does not model `apply-slow-prior`, logarithmic cost/prior shaping,
regex move-class matching, or `slow-context-from-intrinsics` mode derivation.
It also leaves out schemas, hashes, revisions, run/tick identities, clocks,
source completeness, review/observer independence, application-ledger joins,
and the prospective-versus-production authority restrictions enforced by the
evidence verifiers. It proves correspondence of a supplied two-tick record;
it does not prove that the runtime event or its witness occurred.
-/

namespace DarkTower.WarMachine.R15TemporalHierarchy

/-- Beta counts corresponding to runtime per-class `:alpha` and `:beta`. -/
structure BetaCounts where
  /-- Runtime `:alpha`. -/
  alpha : Nat
  /-- Runtime `:beta`. -/
  beta : Nat
  deriving DecidableEq, Repr

/-- A finite runtime `:slow/intrinsics` map, represented as action-class/count
pairs. The natural key stands for `:fast/action-class`; the value stands for
that class's `:alpha` and `:beta`. -/
abbrev SlowState := List (Nat × BetaCounts)

/-- Runtime Beta(1,1) value returned by `intrinsic-values/fresh-entry`. -/
def freshCounts : BetaCounts := { alpha := 1, beta := 1 }

/-- Read one action class from runtime `:slow/intrinsics`, defaulting to the
fresh Beta(1,1) prior when the key is absent. -/
def countsFor : SlowState → Nat → BetaCounts
  | [], _ => freshCounts
  | (key, counts) :: rest, actionClass =>
      if key = actionClass then counts else countsFor rest actionClass

/-- Functional counterpart of associating one class entry into runtime
`:slow/intrinsics`. -/
def setCounts : SlowState → Nat → BetaCounts → SlowState
  | [], actionClass, counts => [(actionClass, counts)]
  | (key, prior) :: rest, actionClass, counts =>
      if key = actionClass then (key, counts) :: rest
      else (key, prior) :: setCounts rest actionClass counts

theorem countsFor_setCounts_same (state : SlowState) (actionClass : Nat)
    (counts : BetaCounts) :
    countsFor (setCounts state actionClass counts) actionClass = counts := by
  induction state with
  | nil => simp [setCounts, countsFor]
  | cons entry rest ih =>
      rcases entry with ⟨key, prior⟩
      by_cases key = actionClass <;> simp [setCounts, countsFor, *]

theorem countsFor_setCounts_other (state : SlowState) (actionClass other : Nat)
    (counts : BetaCounts) (different : other ≠ actionClass) :
    countsFor (setCounts state actionClass counts) other = countsFor state other := by
  induction state with
  | nil =>
      have reverse : actionClass ≠ other := Ne.symm different
      simp [setCounts, countsFor, reverse]
  | cons entry rest ih =>
      rcases entry with ⟨key, prior⟩
      by_cases target : key = actionClass
      · subst key
        have reverse : actionClass ≠ other := Ne.symm different
        simp [setCounts, countsFor, reverse]
      · by_cases observed : key = other
        · subst key
          simp [setCounts, countsFor, target]
        · simp [setCounts, countsFor, target, observed, ih]

/-- One runtime fast result. `actionClass`, `witnessed`, and `succeeded` stand
for `:fast/action-class`, `:fast/witnessed?`, and `:fast/succeeded?`. -/
structure FastOutcome where
  actionClass : Nat
  witnessed : Bool
  succeeded : Bool
  deriving DecidableEq, Repr

/-- The one-emission Beta update used by `advance-slow-state`. -/
def updatedCounts (prior : BetaCounts) (succeeded : Bool) : BetaCounts :=
  if succeeded then { prior with alpha := prior.alpha + 1 }
  else { prior with beta := prior.beta + 1 }

/-- Fold one fast outcome into its action class. Witness admission is kept in
`TwoTickFeedback`; the arithmetic function is total so rejected controls can
still state what their untrusted payload claimed. -/
def advance (before : SlowState) (outcome : FastOutcome) : SlowState :=
  setCounts before outcome.actionClass
    (updatedCounts (countsFor before outcome.actionClass) outcome.succeeded)

/-- The retained two-tick carrier. `before` and `after` stand for
`:slow-state-before` and `:slow-state-after`; `outcome` for the independently
witnessed fast result; and `nextConsumed` for
`:next-tick-consumed-slow-state`. -/
structure TwoTickRecord where
  before : SlowState
  outcome : FastOutcome
  after : SlowState
  nextConsumed : SlowState
  deriving DecidableEq, Repr

/-- R15's role, stated without the checker: only a witnessed fast outcome may
update the slow state, the retained after-state is the exact update, and the
next fast tick consumes that updated slow state. -/
def TwoTickFeedback (record : TwoTickRecord) : Prop :=
  record.outcome.witnessed = true ∧
  record.after = advance record.before record.outcome ∧
  record.nextConsumed = record.after

/-- Executable checker for the retained two-tick correspondence. -/
def checkTwoTickFeedback (record : TwoTickRecord) : Bool :=
  record.outcome.witnessed &&
  decide (record.after = advance record.before record.outcome) &&
  decide (record.nextConsumed = record.after)

theorem checkTwoTickFeedback_eq_true_iff (record : TwoTickRecord) :
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

theorem advance_ne_before (before : SlowState) (outcome : FastOutcome) :
    advance before outcome ≠ before := by
  intro unchanged
  have observed := congrArg (fun state => countsFor state outcome.actionClass) unchanged
  unfold advance at observed
  rw [countsFor_setCounts_same] at observed
  exact updatedCounts_ne (countsFor before outcome.actionClass) outcome.succeeded observed

/-- Every accepted record changes the slow state; the certificate's inequality
is derived from the one-count update rather than trusted as an extra flag. -/
theorem accepted_before_ne_after (record : TwoTickRecord)
    (accepted : TwoTickFeedback record) : record.before ≠ record.after := by
  rw [accepted.2.1]
  exact (advance_ne_before record.before record.outcome).symm

/-- Updating one class leaves the Beta counts of every other class unchanged. -/
theorem accepted_other_class_unchanged (record : TwoTickRecord)
    (accepted : TwoTickFeedback record) (other : Nat)
    (different : other ≠ record.outcome.actionClass) :
    countsFor record.after other = countsFor record.before other := by
  rw [accepted.2.1]
  exact countsFor_setCounts_other _ _ _ _ different

/-- Universally, no unwitnessed outcome is accepted, regardless of any of the
three supplied slow states. -/
theorem unwitnessed_never_accepted (record : TwoTickRecord)
    (unwitnessed : record.outcome.witnessed = false) :
    ¬ TwoTickFeedback record := by
  intro accepted
  have witnessed := accepted.1
  rw [unwitnessed] at witnessed
  exact Bool.noConfusion witnessed

def initialState : SlowState := [(10, { alpha := 2, beta := 3 }), (20, { alpha := 4, beta := 5 })]
def successOutcome : FastOutcome := { actionClass := 10, witnessed := true, succeeded := true }
def failureOutcome : FastOutcome := { actionClass := 20, witnessed := true, succeeded := false }

/-- Positive witnessed-success record. -/
def successRecord : TwoTickRecord :=
  { before := initialState
    outcome := successOutcome
    after := advance initialState successOutcome
    nextConsumed := advance initialState successOutcome }

theorem successRecord_is_feedback : TwoTickFeedback successRecord := by
  rw [← checkTwoTickFeedback_eq_true_iff]
  decide

/-- Positive witnessed-failure record. -/
def failureRecord : TwoTickRecord :=
  { before := initialState
    outcome := failureOutcome
    after := advance initialState failureOutcome
    nextConsumed := advance initialState failureOutcome }

theorem failureRecord_is_feedback : TwoTickFeedback failureRecord := by
  rw [← checkTwoTickFeedback_eq_true_iff]
  decide

/-- Control A: arithmetic and consumption agree, but the outcome was not
witnessed. -/
def unwitnessedRecord : TwoTickRecord :=
  let outcome := { successOutcome with witnessed := false }
  { before := initialState, outcome := outcome,
    after := advance initialState outcome, nextConsumed := advance initialState outcome }

theorem unwitnessedRecord_is_rejected : ¬ TwoTickFeedback unwitnessedRecord :=
  unwitnessed_never_accepted unwitnessedRecord (by decide)

/-- Control B: the update is correct, but the next tick consumed stale state. -/
def staleConsumptionRecord : TwoTickRecord :=
  { successRecord with nextConsumed := initialState }

theorem staleConsumptionRecord_is_rejected : ¬ TwoTickFeedback staleConsumptionRecord := by
  intro accepted
  have consumed := accepted.2.2
  have changed := accepted_before_ne_after staleConsumptionRecord accepted
  change staleConsumptionRecord.before = staleConsumptionRecord.after at consumed
  exact changed consumed

/-- Control C: after-state changed, but by updating another class rather than
the witnessed outcome's class. Consumption faithfully carries that wrong state. -/
def wrongClassState : SlowState :=
  setCounts initialState 20 (updatedCounts (countsFor initialState 20) true)

def wrongUpdateRecord : TwoTickRecord :=
  { before := initialState, outcome := successOutcome,
    after := wrongClassState, nextConsumed := wrongClassState }

theorem wrongUpdateRecord_after_changed : wrongUpdateRecord.after ≠ wrongUpdateRecord.before := by
  decide

theorem wrongUpdateRecord_is_rejected : ¬ TwoTickFeedback wrongUpdateRecord := by
  intro accepted
  have arithmetic := accepted.2.1
  norm_num [wrongUpdateRecord, wrongClassState, advance, initialState, successOutcome,
    setCounts, countsFor, updatedCounts] at arithmetic

end DarkTower.WarMachine.R15TemporalHierarchy
