import DarkTower.WarMachine.PrecisionFromObservation
import DarkTower.WarMachine.EvidenceFromTheProcess
import DarkTower.WarMachine.R15HabitPrior
import DarkTower.WarMachine.CTauClassPreference
import DarkTower.WarMachine.R15StrategicTarget
import DarkTower.WarMachine.R10ScheduledEntrypoint
import DarkTower.WarMachine.R11JointAction
import Mathlib.Tactic

/-!
# R20: the per-click active-inference certificate

At the end of a click the machine says, node by node, what happened in the
terms of the theory and whether its retained record agrees.  The click is
certified as active inference only when every row agrees.  Absence is a hole,
never a pass.

This is the final assembly described by `PROOF-2a-THEOREM-draft-2026-09-24.md`
lines 28--32 and 47--56: each row identifies consumed values, checks the Lean
proposition on them, and has an independently constructed bad extract that
fails that same proposition.  Da Costa et al. (2020),
`refs/dacosta2020.txt:222-227`, call the paired perception/action account
“self-evidencing”.  R20 is the last term of the PROOF-2a/PROOF-2b series
(Joe, 2026-10-05): each row prints the qualitative result in plain terms, for
example whether F was the same for every policy, and the certificate answers
whether the click was active inference.

| row | module | proposition | control |
| --- | --- | --- | --- |
| precision | `PrecisionFromObservation` | `Conforms` | unchanged despite discriminating F |
| evidence | `EvidenceFromTheProcess` | Bayes posterior correspondence | forged unchanged posterior |
| habit | `R15TemporalHierarchy` | `TwoTickFeedback` | unwitnessed outcome |
| class preference | `CTauClassPreference` | reported `classRisk` | altered risk |
| strategic focus | `R15StrategicTarget` | `StrategicTickConforms` | wrong class |
| liveness | `R10ScheduledEntrypoint` | `HonestLiveness` | green no-op |
| independence | R9 adapter | author is not reviewer | same author and reviewer |
| joint action | `R11JointAction.SharedState` | `OneWriter` | two writers |
| cost | this module | `CostConforms` | total that is not the sum of its jobs |

The cost row says how many tokens and how much time the click spent up to and
including its choice, and how many after it, and checks that the total is the
sum of what its jobs report.  Parr, Pezzulo and Friston (2022), section 10.8,
`refs/parr2022.txt:10854-10892`: "a bounded rational agent has to balance the
costs, effort, and timeliness of computation", and "What is costly during
deliberation is decreasing the entropy (or complexity) of one's beliefs before
a choice".  The row sets no limit on cost; it requires that the cost is fully
accounted for and prints on which side of the choice it fell.

The evidence module supplies the posterior but no before/after receipt, so
`EvidenceRow` is the minimal carrier for those existing quantities.  R9's
`Holes` declarations concern generic claims and witnesses rather than an
author/reviewer receipt; `IndependenceRow` is therefore the equally small
boundary required by this certificate.  Neither adapter adds theory.
-/

namespace DarkTower.WarMachine.R20Certificate

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

inductive Node
  | precision | evidence | habit | classPreference
  | strategicFocus | liveness | independence | jointAction | cost
  deriving DecidableEq, Repr, Fintype

inductive PrecisionCase | unchanged | moreDecisive | lessDecisive deriving DecidableEq, Repr
inductive EvidenceCase | beliefUnchanged | beliefMoved deriving DecidableEq, Repr
inductive HabitCase | reinforced | unchanged deriving DecidableEq, Repr
inductive ClassPreferenceCase
  | beforeHorizon | atHorizonSupported | atHorizonUnsupported
  deriving DecidableEq, Repr
inductive StrategicFocusCase | focusKept | focusChanged deriving DecidableEq, Repr
inductive LivenessCase | live | notLive deriving DecidableEq, Repr
inductive IndependenceCase | authorIsNotReviewer | sameAgent deriving DecidableEq, Repr
inductive JointActionCase | eachTookItsPart | takenTwice | dropped deriving DecidableEq, Repr
inductive CostCase | mostlyChoosing | mostlyActing | even deriving DecidableEq, Repr

inductive Case
  | precision (v : PrecisionCase) | evidence (v : EvidenceCase)
  | habit (v : HabitCase) | classPreference (v : ClassPreferenceCase)
  | strategicFocus (v : StrategicFocusCase) | liveness (v : LivenessCase)
  | independence (v : IndependenceCase) | jointAction (v : JointActionCase)
  | cost (v : CostCase)
  deriving DecidableEq, Repr

abbrev Policy := PrecisionFromObservation.TwoPolicy
abbrev Hidden := Fin 2
abbrev Observation := Bool

/-- The existing finite Bayes quantities, retained before and after. -/
structure EvidenceRow where
  prior : EvidenceFromTheProcess.Belief Hidden
  likelihood : EvidenceFromTheProcess.Likelihood Hidden Observation
  observation : Observation
  posterior : EvidenceFromTheProcess.Belief Hidden

def EvidenceConforms (r : EvidenceRow) : Prop :=
  r.posterior = EvidenceFromTheProcess.posterior r.prior r.likelihood r.observation

structure ClassPreferenceRow where
  horizon : Nat
  tau : Nat
  predicted : CTauClassPreference.Distribution
  reportedRisk : EReal

def ClassPreferenceConforms (r : ClassPreferenceRow) : Prop :=
  r.reportedRisk = CTauClassPreference.classRisk r.predicted
    (CTauClassPreference.classPreference r.horizon r.tau)

structure StrategicFocusRow where
  previousFocus : Nat
  tick : R15StrategicTarget.StrategicTickRecord

def StrategicFocusConforms (r : StrategicFocusRow) : Prop :=
  R15StrategicTarget.StrategicTickConforms r.tick

abbrev LiveRow := R10ScheduledEntrypoint.TickOutcome Nat

/-- The R10 rule as that module states it: a tick labelled live changed
state. A changed tick labelled not-live is permitted there and here. -/
def LivenessConforms (r : LiveRow) : Prop :=
  R10ScheduledEntrypoint.HonestLiveness [r]

structure IndependenceRow where
  author : Fin 2
  reviewer : Fin 2

/-- No self-certification: the row agrees only when the reviewer is a
different agent from the author. A record that honestly reports one agent in
both roles is present and disagrees. -/
def IndependenceConforms (r : IndependenceRow) : Prop :=
  r.author ≠ r.reviewer

abbrev JointRow := Fin 2 → R11JointAction.Ownership Unit (Fin 2)

/-- What one dispatched job reports: its tokens, and whether it ran up to and
including the click's choice (`true`) or after it. -/
structure JobCost where
  throughSelection : Bool
  inputTokens : Nat
  outputTokens : Nat
  totalTokens : Nat

/-- The click's cost as it reports it. Every job here has a usage record; a
click with a job whose usage is missing has no `CostRow`, and its row is
`notRecorded`. Times are in milliseconds. -/
structure CostRow where
  jobs : List JobCost
  msThroughSelection : Nat
  msAfterSelection : Nat
  reportedTotalTokens : Nat
  reportedTokensThroughSelection : Nat
  reportedTokensAfterSelection : Nat

/-- Tokens of the jobs on one side of the choice. -/
def tokensWhere (side : Bool) (jobs : List JobCost) : Nat :=
  (jobs.map fun j => if j.throughSelection = side then j.totalTokens else 0).sum

def totalTokens (jobs : List JobCost) : Nat := (jobs.map (·.totalTokens)).sum

/-- Each job's total is its input plus its output, and the reported total and
the two reported sides are the sums over the jobs. -/
def CostConforms (r : CostRow) : Prop :=
  (∀ j ∈ r.jobs, j.totalTokens = j.inputTokens + j.outputTokens) ∧
  r.reportedTotalTokens = totalTokens r.jobs ∧
  r.reportedTokensThroughSelection = tokensWhere true r.jobs ∧
  r.reportedTokensAfterSelection = tokensWhere false r.jobs

/-- Where the cost fell: by tokens, and by time when the tokens are equal. -/
def costCase (r : CostRow) : CostCase :=
  if r.reportedTokensAfterSelection < r.reportedTokensThroughSelection then .mostlyChoosing
  else if r.reportedTokensThroughSelection < r.reportedTokensAfterSelection then .mostlyActing
  else if r.msAfterSelection < r.msThroughSelection then .mostlyChoosing
  else if r.msThroughSelection < r.msAfterSelection then .mostlyActing
  else .even

def NodeRecord : Node → Type
  | .precision => PrecisionFromObservation.TickRecord Policy
  | .evidence => EvidenceRow
  | .habit => R15TemporalHierarchy.TwoTickRecord
  | .classPreference => ClassPreferenceRow
  | .strategicFocus => StrategicFocusRow
  | .liveness => LiveRow
  | .independence => IndependenceRow
  | .jointAction => JointRow
  | .cost => CostRow

def conforms : (n : Node) → NodeRecord n → Prop
  | .precision, r => PrecisionFromObservation.Conforms r
  | .evidence, r => EvidenceConforms r
  | .habit, r => R15TemporalHierarchy.TwoTickFeedback r
  | .classPreference, r => ClassPreferenceConforms r
  | .strategicFocus, r => StrategicFocusConforms r
  | .liveness, r => LivenessConforms r
  | .independence, r => IndependenceConforms r
  | .jointAction, r => R11JointAction.OneWriter r
  | .cost, r => CostConforms r

def caseOf : (n : Node) → NodeRecord n → Case
  | .precision, r => .precision <| if r.betaPosterior = r.betaPrior then .unchanged
      else if r.betaPosterior < r.betaPrior then .moreDecisive else .lessDecisive
  | .evidence, r => .evidence <| if r.posterior = r.prior then .beliefUnchanged else .beliefMoved
  | .habit, r => .habit <| if r.outcome.witnessed && r.outcome.succeeded then .reinforced else .unchanged
  | .classPreference, r => .classPreference <| if r.tau < r.horizon then .beforeHorizon
      else if r.reportedRisk = ⊤ then .atHorizonUnsupported else .atHorizonSupported
  | .strategicFocus, r => .strategicFocus <|
      if r.previousFocus = r.tick.focus then .focusKept else .focusChanged
  | .liveness, r => .liveness <| if R10ScheduledEntrypoint.LiveTick r then .live else .notLive
  | .independence, r => .independence <|
      if r.author = r.reviewer then .sameAgent else .authorIsNotReviewer
  | .jointAction, r => .jointAction <| match (R11JointAction.writers r ()).card with
      | 0 => .dropped | 1 => .eachTookItsPart | _ => .takenTwice
  | .cost, r => .cost (costCase r)

/-- The precision row prints the fixed-point's qualitative direction. -/
theorem precision_constant_F_is_unchanged
    (r : PrecisionFromObservation.TickRecord Policy) (h : PrecisionFromObservation.Conforms r)
    (c : ℝ) (hc : r.F = fun _ => c) : caseOf .precision r = .precision .unchanged := by
  have fixed := h.2.2.1
  have eq := (PrecisionFromObservation.constant_F_posterior_temperature_iff
    h.2.1 r.E r.G c).mp (by simpa [hc] using fixed)
  simp [caseOf, eq]

/-- With two policies that G ranks differently, a conforming record's
temperature is unchanged exactly when F is the same for both. -/
theorem precision_unchanged_iff_F_equal
    (r : PrecisionFromObservation.TickRecord Policy) (h : PrecisionFromObservation.Conforms r)
    (hG : r.G .a ≠ r.G .b) :
    caseOf .precision r = .precision .unchanged ↔ r.F .a = r.F .b := by
  constructor
  · intro hcase
    by_contra hF
    have eq : r.betaPosterior = r.betaPrior := by
      by_contra ne
      simp only [caseOf, if_neg ne] at hcase
      split_ifs at hcase <;> simp at hcase
    exact PrecisionFromObservation.unchanged_discriminating_refused r hG hF eq h
  · intro hF
    apply precision_constant_F_is_unchanged r h (r.F .a)
    funext p
    cases p
    · rfl
    · exact hF.symm

theorem precision_favoured_is_moreDecisive
    (r : PrecisionFromObservation.TickRecord Policy) (h : PrecisionFromObservation.Conforms r)
    (hG : r.G .a < r.G .b) (hF : r.F .a < r.F .b) :
    caseOf .precision r = .precision .moreDecisive := by
  have lt := PrecisionFromObservation.favoured_observation_raises_precision h.2.2.1 hG hF
  simp [caseOf, lt.ne, lt]

theorem precision_against_is_lessDecisive
    (r : PrecisionFromObservation.TickRecord Policy) (h : PrecisionFromObservation.Conforms r)
    (hG : r.G .a < r.G .b) (hF : r.F .b < r.F .a) :
    caseOf .precision r = .precision .lessDecisive := by
  have gt := PrecisionFromObservation.against_favoured_lowers_precision h.2.2.1 hG hF
  simp [caseOf, gt.ne', not_lt.mpr gt.le]

theorem evidence_state_independent_is_unchanged (r : EvidenceRow)
    (h : EvidenceConforms r) (normal : ∑ s, r.prior s = 1)
    (c : ℝ) (hc : 0 < c) (constant : ∀ s, r.likelihood s r.observation = c) :
    caseOf .evidence r = .evidence .beliefUnchanged := by
  have unchanged := EvidenceFromTheProcess.no_evidence_no_change
    r.prior r.likelihood r.observation normal c hc constant
  simp [caseOf, h.trans unchanged]

theorem failed_habit_is_unchanged (r : R15TemporalHierarchy.TwoTickRecord)
    (failed : r.outcome.succeeded = false) : caseOf .habit r = .habit .unchanged := by
  simp [caseOf, failed]

theorem liveness_case_is_live_iff (r : LiveRow) :
    caseOf .liveness r = .liveness .live ↔ R10ScheduledEntrypoint.LiveTick r := by
  simp [caseOf]

/-! ## The cost row -/

theorem totalTokens_split (jobs : List JobCost) :
    totalTokens jobs = tokensWhere true jobs + tokensWhere false jobs := by
  induction jobs with
  | nil => simp [totalTokens, tokensWhere]
  | cons j rest ih =>
    simp only [totalTokens, tokensWhere, List.map_cons, List.sum_cons] at ih ⊢
    cases h : j.throughSelection <;> simp <;> omega

/-- In a conforming row the total is the tokens through the choice plus the
tokens after it. -/
theorem cost_total_is_sum_of_sides (r : CostRow) (h : CostConforms r) :
    r.reportedTotalTokens =
      r.reportedTokensThroughSelection + r.reportedTokensAfterSelection := by
  obtain ⟨_, total, through, after⟩ := h
  rw [total, through, after, totalTokens_split]

/-- More tokens after the choice than up to it: the row prints `mostlyActing`. -/
theorem cost_mostlyActing (r : CostRow) (h : CostConforms r)
    (more : tokensWhere true r.jobs < tokensWhere false r.jobs) :
    caseOf .cost r = .cost .mostlyActing := by
  obtain ⟨_, _, through, after⟩ := h
  have lt : r.reportedTokensThroughSelection < r.reportedTokensAfterSelection := by
    rw [through, after]; exact more
  simp [caseOf, costCase, lt, Nat.lt_asymm lt]

/-- More tokens up to the choice than after it: the row prints `mostlyChoosing`. -/
theorem cost_mostlyChoosing (r : CostRow) (h : CostConforms r)
    (more : tokensWhere false r.jobs < tokensWhere true r.jobs) :
    caseOf .cost r = .cost .mostlyChoosing := by
  obtain ⟨_, _, through, after⟩ := h
  have lt : r.reportedTokensAfterSelection < r.reportedTokensThroughSelection := by
    rw [through, after]; exact more
  simp [caseOf, costCase, lt]

/-- Equal tokens and equal time on the two sides: the row prints `even`. -/
theorem cost_even (r : CostRow)
    (tokens : r.reportedTokensThroughSelection = r.reportedTokensAfterSelection)
    (time : r.msThroughSelection = r.msAfterSelection) :
    caseOf .cost r = .cost .even := by
  simp [caseOf, costCase, tokens, time]

inductive RowVerdict | notRecorded | agrees (case : Case) | disagrees (case : Case)
  deriving DecidableEq, Repr

abbrev Records := (n : Node) → Option (NodeRecord n)
abbrev Certificate := Node → RowVerdict

noncomputable def certify (records : Records) : Certificate := fun n =>
  match records n with
  | none => .notRecorded
  | some r => if conforms n r then .agrees (caseOf n r) else .disagrees (caseOf n r)

def Certified (certificate : Certificate) : Prop :=
  ∀ node, ∃ c, certificate node = .agrees c

theorem certified_iff (records : Records) :
    Certified (certify records) ↔
      ∀ node, ∃ r, records node = some r ∧ conforms node r := by
  classical
  constructor
  · intro certified node
    generalize present : records node = option
    cases option with
    | none =>
        rcases certified node with ⟨c, hc⟩
        simp [certify, present] at hc
    | some r =>
        refine ⟨r, rfl, ?_⟩
        by_contra bad
        rcases certified node with ⟨c, hc⟩
        simp [certify, present, bad] at hc
  · intro complete node
    have row := complete node
    cases node <;> simp only [certify] at row ⊢ <;>
      rcases row with ⟨r, hr, good⟩ <;> simp [hr, good]

theorem missing_not_certified (records : Records) (node : Node)
    (missing : records node = none) : ¬ Certified (certify records) := by
  intro certified
  rcases certified node with ⟨c, hc⟩
  simp [certify, missing] at hc

theorem refused_row_disagrees (records : Records) (node : Node) (r : NodeRecord node)
    (present : records node = some r) (bad : ¬ conforms node r) :
    certify records node = .disagrees (caseOf node r) := by
  simp [certify, present, bad]

def badEvidence : EvidenceRow where
  prior := fun _ => 1 / 2
  likelihood := fun _ _ => 1
  observation := false
  posterior := fun _ => 0

theorem badEvidence_refused : ¬ EvidenceConforms badEvidence := by
  intro h
  have at0 := congrFun h (0 : Hidden)
  norm_num [badEvidence, EvidenceFromTheProcess.posterior,
    EvidenceFromTheProcess.evidence] at at0

def badClass : ClassPreferenceRow where
  horizon := 2; tau := 1
  predicted := CTauClassPreference.waitingPreference
  reportedRisk := 1

theorem badClass_refused : ¬ ClassPreferenceConforms badClass := by
  change (1 : EReal) ≠ CTauClassPreference.classRisk
    CTauClassPreference.waitingPreference CTauClassPreference.waitingPreference
  rw [CTauClassPreference.waiting_point_mass_risk_zero]
  norm_num

def badLive : LiveRow := ⟨0, 0, true⟩
theorem badLive_refused : ¬ LivenessConforms badLive := by
  intro honest
  have changed := honest badLive (by simp) rfl
  simp [R10ScheduledEntrypoint.ChangedState, badLive] at changed

def badIndependence : IndependenceRow := ⟨0, 0⟩
theorem badIndependence_refused : ¬ IndependenceConforms badIndependence := by
  simp [IndependenceConforms, badIndependence]

/-- A certified click had a reviewer who was not its author. -/
theorem certified_author_is_not_reviewer (records : Records)
    (certified : Certified (certify records)) :
    ∃ r : IndependenceRow, records .independence = some r ∧ r.author ≠ r.reviewer :=
  (certified_iff records).mp certified .independence

/-- The precision control: a record whose temperature did not move although F
differed between two policies that G ranks differently prints "unchanged" and
disagrees. -/
theorem precision_control_disagrees (records : Records)
    (r : PrecisionFromObservation.TickRecord Policy)
    (present : records .precision = some r)
    (hG : r.G .a ≠ r.G .b) (hF : r.F .a ≠ r.F .b)
    (unchanged : r.betaPosterior = r.betaPrior) :
    certify records .precision = .disagrees (.precision .unchanged) := by
  have bad := PrecisionFromObservation.unchanged_discriminating_refused r hG hF unchanged
  rw [refused_row_disagrees records .precision r present bad]
  simp [caseOf, unchanged]

theorem evidence_control_disagrees (records : Records)
    (present : records .evidence = some badEvidence) :
    certify records .evidence = .disagrees (caseOf .evidence badEvidence) :=
  refused_row_disagrees records .evidence badEvidence present badEvidence_refused

theorem habit_control_disagrees (records : Records)
    (present : records .habit = some R15TemporalHierarchy.unwitnessedRecord) :
    certify records .habit = .disagrees (caseOf .habit R15TemporalHierarchy.unwitnessedRecord) :=
  refused_row_disagrees records .habit _ present R15TemporalHierarchy.unwitnessedRecord_is_rejected

theorem class_control_disagrees (records : Records)
    (present : records .classPreference = some badClass) :
    certify records .classPreference = .disagrees (caseOf .classPreference badClass) :=
  refused_row_disagrees records .classPreference badClass present badClass_refused

def badStrategic : StrategicFocusRow := ⟨7, R15StrategicTarget.wrongClassTick⟩
theorem strategic_control_disagrees (records : Records)
    (present : records .strategicFocus = some badStrategic) :
    certify records .strategicFocus = .disagrees (caseOf .strategicFocus badStrategic) :=
  refused_row_disagrees records .strategicFocus badStrategic present
    (by exact R15StrategicTarget.wrongClassTick_rejected)

theorem liveness_control_disagrees (records : Records)
    (present : records .liveness = some badLive) :
    certify records .liveness = .disagrees (caseOf .liveness badLive) :=
  refused_row_disagrees records .liveness badLive present badLive_refused

theorem independence_control_disagrees (records : Records)
    (present : records .independence = some badIndependence) :
    certify records .independence = .disagrees (caseOf .independence badIndependence) :=
  refused_row_disagrees records .independence badIndependence present badIndependence_refused

theorem joint_control_disagrees (records : Records)
    (present : records .jointAction = some R11JointAction.bothClaim) :
    certify records .jointAction =
      .disagrees (caseOf .jointAction R11JointAction.bothClaim) :=
  refused_row_disagrees records .jointAction _ present R11JointAction.both_claim_refused

/-- One job of 12 tokens, reported as a total of 13. -/
def badCost : CostRow :=
  { jobs := [⟨false, 10, 2, 12⟩], msThroughSelection := 0, msAfterSelection := 5,
    reportedTotalTokens := 13, reportedTokensThroughSelection := 0,
    reportedTokensAfterSelection := 12 }

theorem badCost_refused : ¬ CostConforms badCost := by
  intro h
  have total := h.2.1
  simp [badCost, totalTokens] at total

/-- A job whose total is not its input plus its output. -/
def badJobCost : CostRow :=
  { jobs := [⟨false, 10, 2, 13⟩], msThroughSelection := 0, msAfterSelection := 5,
    reportedTotalTokens := 13, reportedTokensThroughSelection := 0,
    reportedTokensAfterSelection := 13 }

theorem badJobCost_refused : ¬ CostConforms badJobCost := by
  intro h
  have job := h.1 ⟨false, 10, 2, 13⟩ (by simp [badJobCost])
  simp at job

theorem cost_control_disagrees (records : Records)
    (present : records .cost = some badCost) :
    certify records .cost = .disagrees (caseOf .cost badCost) :=
  refused_row_disagrees records .cost badCost present badCost_refused

/-- Fixed print order for the run's succinct certificate. -/
def nodeOrder : List Node :=
  [.precision, .evidence, .habit, .classPreference, .strategicFocus,
   .liveness, .independence, .jointAction, .cost]

def summary (certificate : Certificate) : List (Node × RowVerdict) :=
  nodeOrder.map fun node => (node, certificate node)

end
end DarkTower.WarMachine.R20Certificate
