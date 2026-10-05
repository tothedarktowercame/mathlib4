import Mathlib.Tactic

/-!
# R15 hierarchy and temporal depth

The paper gives R15 three roles: strategic selection fixes the tactical target;
witnessed tactical outcomes update the next strategic calibration state; and
longer policies use a named temporal discount of their own rather than
overloading the commitment dial. Its invariant is that each level has its own
quantities: hierarchy is a relationship between levels and timescales, not a
second use of one score.

This module states the second role through `TwoTickFeedback` and the third
through `discountedScore`, `selectionProbability`, and `TemporalRecordConforms`.
The first role is not stated here: the current runtime shapes tactical move
priors and costs but carries no strategic-target field that could witness a
fixed tactical target.

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

A slow state is a list of entries here and a map in the runtime, and the
clauses of `TwoTickFeedback` compare lists. Two lists holding the same entries
in a different order, or one listing a class at its fresh Beta(1,1) value and
one omitting it, are the same runtime map and different lists. A retained
record is therefore comparable with this predicate only once its three states
are listed in the order `advance` produces (existing classes in place, a new
class appended). Restating the clauses through `countsFor`, class by class,
would remove that condition; it is not done here.

The temporal portion transcribes `rollout.clj/project-policy` and
`rollout-discount` at the same Futon2 commit: `S(π) = Σ t < H, δ^t g_t`, where
δ is runtime `:temporal-discount` (legacy alias `:gamma`, default `0.9`). The
registry names horizon `:T` and commitment temperature `:tau`, but has no
symbol for δ; `PolicyHorizon.lean` states the undiscounted horizon sum. At
δ = 1, `discountedScore` is exactly the ordinary sum (`discountedScore_one`).
Runtime `:gamma` here is δ, whereas R14's γ is policy precision `1 / τ`; they
are different quantities.

The conformance carrier below is deliberately stronger than today's retained
slow-feedback record. That record retains requested/effective horizon and
checks it was not rewritten, but it does not join the candidate step costs,
temporal discount, commitment temperature, reported discounted scores, and
reported softmax probabilities in one independently retained record. Thus
this module states what such a record must satisfy; it does not certify that
the current runtime retains one.
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

/-! ## Named temporal discount, separate from commitment temperature -/

/-- Exact-rational transcription of runtime `:policy-rollout-score`: the
ordered list is the policy's per-step `:g`/cost values, and `discount` is
runtime `:temporal-discount` (legacy `:gamma`). -/
def discountedScore (discount : ℚ) : List ℚ → ℚ
  | [] => 0
  | cost :: rest => cost + discount * discountedScore discount rest

/-- At discount one, the runtime recurrence reduces to the undiscounted finite
horizon sum stated by `PolicyHorizon.lean` (after identifying that module's
indexed step costs with this ordered list). -/
theorem discountedScore_one (costs : List ℚ) :
    discountedScore 1 costs = costs.sum := by
  induction costs with
  | nil => rfl
  | cons cost rest ih => simp [discountedScore, ih]

/-- Runtime `select-policy`'s unnormalised `exp(-S/τ)` weight. -/
noncomputable def selectionWeight (temperature score : ℝ) : ℝ :=
  Real.exp (-score / temperature)

/-- The normalised probability for the first member of a two-policy field.
This is the two-candidate instance of runtime `softmax`. -/
noncomputable def selectionProbability (temperature first second : ℝ) : ℝ :=
  selectionWeight temperature first /
    (selectionWeight temperature first + selectionWeight temperature second)

/-- Temperature changes decisiveness but never reverses score order: at every
positive τ, the lower-score policy has the greater unnormalised softmax weight. -/
theorem selectionWeight_reverse_order {temperature first second : ℝ}
    (positive : 0 < temperature) :
    selectionWeight temperature first > selectionWeight temperature second ↔
      first < second := by
  simp only [selectionWeight, Real.exp_lt_exp]
  constructor
  · intro h
    have := (div_lt_div_iff_of_pos_right positive).mp h
    linarith
  · intro h
    apply (div_lt_div_iff_of_pos_right positive).2
    linarith

/-- The same order survives normalisation in a two-policy field. -/
theorem selectionProbability_gt_half_iff {temperature first second : ℝ}
    (positive : 0 < temperature) :
    1 / 2 < selectionProbability temperature first second ↔ first < second := by
  let a := selectionWeight temperature first
  let b := selectionWeight temperature second
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hab : 0 < a + b := add_pos ha hb
  constructor
  · intro h
    rw [selectionProbability, div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hab] at h
    have : b < a := by linarith
    exact (selectionWeight_reverse_order positive).mp this
  · intro h
    have : b < a := (selectionWeight_reverse_order positive).mpr h
    rw [selectionProbability, div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hab]
    linarith

/-- Concrete policies whose order changes when δ changes: the delayed cost of
`lateCostPolicy` is preferred at δ=1/2, but `frontCostPolicy` is preferred at
δ=1. -/
def lateCostPolicy : List ℚ := [0, 10]
def frontCostPolicy : List ℚ := [6, 0]

theorem discount_changes_policy_order :
    discountedScore (1 / 2) lateCostPolicy < discountedScore (1 / 2) frontCostPolicy ∧
    discountedScore 1 frontCostPolicy < discountedScore 1 lateCostPolicy := by
  norm_num [discountedScore, lateCostPolicy, frontCostPolicy]

/-- No positive commitment temperature can reproduce the reversal caused by
changing δ: the more probable member of this pair changes for every τ. -/
theorem temperature_cannot_reproduce_discount_change (temperature : ℝ)
    (positive : 0 < temperature) :
    1 / 2 < selectionProbability temperature
      (discountedScore (1 / 2) lateCostPolicy)
      (discountedScore (1 / 2) frontCostPolicy) ∧
    1 / 2 < selectionProbability temperature
      (discountedScore 1 frontCostPolicy)
      (discountedScore 1 lateCostPolicy) := by
  constructor <;> apply (selectionProbability_gt_half_iff positive).2 <;>
    norm_num [discountedScore, lateCostPolicy, frontCostPolicy]

/-- One candidate policy in a retained temporal decision record. `stepCosts`
stands for the ordered per-step cost records; `reportedScore` and
`reportedProbability` stand for `:policy-rollout-score` and
`:selection/probability`. -/
structure TemporalCandidate where
  stepCosts : List ℚ
  reportedScore : ℚ
  reportedProbability : ℝ

/-- Two-policy retained carrier. `horizon`, `discount`, and `temperature` stand
for runtime horizon (`:horizon`/`:depth`), `:temporal-discount`, and selection
`:tau`. Two candidates make the normalisation and controls explicit. -/
structure TemporalDecisionRecord where
  horizon : Nat
  discount : ℚ
  temperature : ℝ
  first : TemporalCandidate
  second : TemporalCandidate

/-- R15 temporal conformance: horizons match both policies, reported scores use
the named δ, τ is positive, and reported probabilities use τ only after those
scores have been computed. -/
def TemporalRecordConforms (record : TemporalDecisionRecord) : Prop :=
  record.first.stepCosts.length = record.horizon ∧
  record.second.stepCosts.length = record.horizon ∧
  record.first.reportedScore = discountedScore record.discount record.first.stepCosts ∧
  record.second.reportedScore = discountedScore record.discount record.second.stepCosts ∧
  0 < record.temperature ∧
  record.first.reportedProbability = selectionProbability record.temperature
    record.first.reportedScore record.second.reportedScore ∧
  record.second.reportedProbability = selectionProbability record.temperature
    record.second.reportedScore record.first.reportedScore

noncomputable def conformingTemporalRecord : TemporalDecisionRecord :=
  ⟨2, 1 / 2, 2,
    ⟨lateCostPolicy, 5, selectionProbability 2 5 6⟩,
    ⟨frontCostPolicy, 6, selectionProbability 2 6 5⟩⟩

theorem conformingTemporalRecord_accepts :
    TemporalRecordConforms conformingTemporalRecord := by
  norm_num [TemporalRecordConforms, conformingTemporalRecord, discountedScore,
    lateCostPolicy, frontCostPolicy]

/-- Control: using τ=2 as δ produces the wrong reported delayed-cost score. -/
noncomputable def temperatureAsDiscountRecord : TemporalDecisionRecord :=
  { conformingTemporalRecord with
    first := { conformingTemporalRecord.first with reportedScore := 20 } }

theorem temperatureAsDiscountRecord_rejected :
    ¬ TemporalRecordConforms temperatureAsDiscountRecord := by
  intro h
  norm_num [TemporalRecordConforms, temperatureAsDiscountRecord,
    conformingTemporalRecord, discountedScore, lateCostPolicy] at h

/-- Control: correct δ-scores paired with temperature-ignoring uniform weights. -/
noncomputable def temperatureIgnoredRecord : TemporalDecisionRecord :=
  { conformingTemporalRecord with
    first := { conformingTemporalRecord.first with reportedProbability := 1 / 2 }
    second := { conformingTemporalRecord.second with reportedProbability := 1 / 2 } }

theorem temperatureIgnoredRecord_rejected :
    ¬ TemporalRecordConforms temperatureIgnoredRecord := by
  intro h
  have probability := h.2.2.2.2.2.1
  have ordered : (5 : ℝ) < 6 := by norm_num
  have nonuniform := (selectionProbability_gt_half_iff (temperature := (2 : ℝ))
    (first := (5 : ℝ)) (second := (6 : ℝ)) (by norm_num)).2 ordered
  simp only [temperatureIgnoredRecord, conformingTemporalRecord] at probability
  change (1 / 2 : ℝ) = selectionProbability 2 5 6 at probability
  linarith

end DarkTower.WarMachine.R15TemporalHierarchy
