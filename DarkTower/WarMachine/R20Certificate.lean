import DarkTower.WarMachine.PrecisionFiniteMenu
import DarkTower.WarMachine.EvidenceFromTheProcess
import DarkTower.WarMachine.R15HabitPrior
import DarkTower.WarMachine.CTauClassPreference
import DarkTower.WarMachine.R15StrategicTarget
import DarkTower.WarMachine.R10ScheduledEntrypoint
import DarkTower.WarMachine.R11JointAction
import DarkTower.WarMachine.R20Graph
import DarkTower.WarMachine.R20Interoception
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
| interoception | `R20Interoception` | `InteroceptionConforms` | reversed viable preference |

The cost row says how many tokens and how much time the click spent up to and
including its choice, and how many after it, and checks that the total is the
sum of what its jobs report.  Parr, Pezzulo and Friston (2022), section 10.8,
`refs/parr2022.txt:10854-10892`: "a bounded rational agent has to balance the
costs, effort, and timeliness of computation", and "What is costly during
deliberation is decreasing the entropy (or complexity) of one's beliefs before
a choice".  The row sets no limit on cost; it requires that the cost is fully
accounted for and prints on which side of the choice it fell.

The interoception row says whether the machine's own reading at this click was
in its viable range, and checks that viable readings are preferred and that
each policy's reported risk is the ordinary KL risk of its predicted reading
against that preference (`R20Interoception`; Parr, Pezzulo and Friston 2022,
pp. 215-216). A reading modality is any finite type, carried here as `Fin size`.
The row supplies selection's interoceptive risk (`R20Graph.Edge.interoceptionToSelectionG`),
which selection adds to the class risk (`R20Graph.selectionScore`).

The evidence module supplies the posterior but no before/after receipt, so
`EvidenceRow` is the minimal carrier for those existing quantities.  R9's
`Holes` declarations concern generic claims and witnesses rather than an
author/reviewer receipt; `IndependenceRow` is therefore the equally small
boundary required by this certificate.  Neither adapter adds theory.

The menu of policies is any finite, nonempty type `Policy`.  The precision
row's direction is stated for any such menu
(`precision_similarlyOrdered_is_moreDecisive`,
`precision_oppositelyOrdered_is_lessDecisive`, from `PrecisionFiniteMenu`);
the earlier two-policy statements remain as instances on `TwoPolicy`.
-/

namespace DarkTower.WarMachine.R20Certificate

open DarkTower.WarMachine.R20Graph

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

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
inductive InteroceptionCase | inRange | outOfRange deriving DecidableEq, Repr

inductive Case
  | precision (v : PrecisionCase) | evidence (v : EvidenceCase)
  | habit (v : HabitCase) | classPreference (v : ClassPreferenceCase)
  | strategicFocus (v : StrategicFocusCase) | liveness (v : LivenessCase)
  | independence (v : IndependenceCase) | jointAction (v : JointActionCase)
  | cost (v : CostCase) | interoception (v : InteroceptionCase)
  deriving DecidableEq, Repr

variable {Policy : Type} [Fintype Policy] [Nonempty Policy]
open PrecisionFromObservation (TwoPolicy)
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

/-- One interoceptive modality with `size` readings: the viable range, the
preference over readings, each policy's predicted reading and reported risk,
and the reading observed at this click. -/
structure InteroceptionRow (Policy : Type) where
  size : Nat
  viable : Finset (Fin size)
  preference : R20Interoception.Distribution (Fin size)
  prediction : Policy → R20Interoception.Distribution (Fin size)
  reportedRisk : Policy → EReal
  observed : Fin size

def InteroceptionConforms (r : InteroceptionRow Policy) : Prop :=
  R20Interoception.PrefersViable r.preference r.viable ∧
    ∀ π, r.reportedRisk π = R20Interoception.interoceptiveRisk (r.prediction π) r.preference

def NodeRecord (Policy : Type) : Node → Type
  | .precision => PrecisionFromObservation.TickRecord Policy
  | .evidence => EvidenceRow
  | .habit => R15TemporalHierarchy.TwoTickRecord Policy
  | .classPreference => ClassPreferenceRow
  | .strategicFocus => StrategicFocusRow
  | .liveness => LiveRow
  | .independence => IndependenceRow
  | .jointAction => JointRow
  | .cost => CostRow
  | .interoception => InteroceptionRow Policy

def conforms : (n : Node) → NodeRecord Policy n → Prop
  | .precision, r => PrecisionFromObservation.Conforms r
  | .evidence, r => EvidenceConforms r
  | .habit, r => R15TemporalHierarchy.TwoTickFeedback r
  | .classPreference, r => ClassPreferenceConforms r
  | .strategicFocus, r => StrategicFocusConforms r
  | .liveness, r => LivenessConforms r
  | .independence, r => IndependenceConforms r
  | .jointAction, r => R11JointAction.OneWriter r
  | .cost, r => CostConforms r
  | .interoception, r => InteroceptionConforms r

def caseOf : (n : Node) → NodeRecord Policy n → Case
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
  | .interoception, r => .interoception <|
      if r.observed ∈ r.viable then .inRange else .outOfRange

/-- The precision row prints the fixed-point's qualitative direction. -/
theorem precision_constant_F_is_unchanged
    (r : PrecisionFromObservation.TickRecord Policy) (h : PrecisionFromObservation.Conforms r)
    (c : ℝ) (hc : r.F = fun _ => c) : caseOf .precision r = .precision .unchanged := by
  have fixed := h.2.2.1
  have eq := (PrecisionFromObservation.constant_F_posterior_temperature_iff
    h.2.1 r.E r.G c).mp (by simpa [hc] using fixed)
  simp [caseOf, eq]

/-- Any finite menu: the row prints `moreDecisive` exactly when the expected G
fell under the observation, and `lessDecisive` exactly when it rose. -/
theorem precision_moreDecisive_iff
    (r : PrecisionFromObservation.TickRecord Policy) (h : PrecisionFromObservation.Conforms r) :
    caseOf .precision r = .precision .moreDecisive ↔
      PrecisionFromObservation.expectedGChange r.betaPosterior r.E r.G r.F < 0 := by
  rw [← PrecisionFromObservation.posterior_temperature_direction_lt h.2.2.1]
  by_cases eq : r.betaPosterior = r.betaPrior
  · simp [caseOf, eq]
  · by_cases lt : r.betaPosterior < r.betaPrior <;> simp [caseOf, eq, lt]

theorem precision_lessDecisive_iff
    (r : PrecisionFromObservation.TickRecord Policy) (h : PrecisionFromObservation.Conforms r) :
    caseOf .precision r = .precision .lessDecisive ↔
      0 < PrecisionFromObservation.expectedGChange r.betaPosterior r.E r.G r.F := by
  rw [← PrecisionFromObservation.posterior_temperature_direction_gt h.2.2.1]
  by_cases eq : r.betaPosterior = r.betaPrior
  · simp [caseOf, eq]
  · by_cases lt : r.betaPosterior < r.betaPrior
    · simp [caseOf, eq, lt, not_lt.mpr lt.le]
    · have gt : r.betaPrior < r.betaPosterior := lt_of_le_of_ne (not_lt.mp lt) (Ne.symm eq)
      simp [caseOf, eq, lt, gt]

/-- Any finite menu: an observation that ranks the policies as G does prints
`moreDecisive`. -/
theorem precision_similarlyOrdered_is_moreDecisive
    (r : PrecisionFromObservation.TickRecord Policy) (h : PrecisionFromObservation.Conforms r)
    (ordered : PrecisionFromObservation.SimilarlyOrdered r.G r.F) :
    caseOf .precision r = .precision .moreDecisive :=
  (precision_moreDecisive_iff r h).2
    (PrecisionFromObservation.expectedGChange_neg_of_similarlyOrdered ordered)

/-- Any finite menu: an observation that ranks the policies against G prints
`lessDecisive`. -/
theorem precision_oppositelyOrdered_is_lessDecisive
    (r : PrecisionFromObservation.TickRecord Policy) (h : PrecisionFromObservation.Conforms r)
    (ordered : PrecisionFromObservation.OppositelyOrdered r.G r.F) :
    caseOf .precision r = .precision .lessDecisive :=
  (precision_lessDecisive_iff r h).2
    (PrecisionFromObservation.expectedGChange_pos_of_oppositelyOrdered ordered)

omit [Nonempty Policy] in
/-- Any finite menu: a record whose temperature did not move although the
observation changed the expected G does not conform. -/
theorem precision_unchanged_with_change_refused
    (r : PrecisionFromObservation.TickRecord Policy)
    (change : PrecisionFromObservation.expectedGChange r.betaPosterior r.E r.G r.F ≠ 0)
    (unchanged : r.betaPosterior = r.betaPrior) : ¬ PrecisionFromObservation.Conforms r := by
  rintro ⟨_, _, ⟨_, zero⟩, _, _⟩
  unfold PrecisionFromObservation.precisionError at zero
  rw [unchanged] at zero
  exact change (by rw [unchanged]; linarith)

/-- With two policies that G ranks differently, a conforming record's
temperature is unchanged exactly when F is the same for both. -/
theorem precision_unchanged_iff_F_equal
    (r : PrecisionFromObservation.TickRecord TwoPolicy) (h : PrecisionFromObservation.Conforms r)
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
    (r : PrecisionFromObservation.TickRecord TwoPolicy) (h : PrecisionFromObservation.Conforms r)
    (hG : r.G .a < r.G .b) (hF : r.F .a < r.F .b) :
    caseOf .precision r = .precision .moreDecisive := by
  have lt := PrecisionFromObservation.favoured_observation_raises_precision h.2.2.1 hG hF
  simp [caseOf, lt.ne, lt]

theorem precision_against_is_lessDecisive
    (r : PrecisionFromObservation.TickRecord TwoPolicy) (h : PrecisionFromObservation.Conforms r)
    (hG : r.G .a < r.G .b) (hF : r.F .b < r.F .a) :
    caseOf .precision r = .precision .lessDecisive := by
  have gt := PrecisionFromObservation.against_favoured_lowers_precision h.2.2.1 hG hF
  simp [caseOf, gt.ne', not_lt.mpr gt.le]

omit [Fintype Policy] [Nonempty Policy] in
theorem evidence_state_independent_is_unchanged (r : EvidenceRow)
    (h : EvidenceConforms r) (normal : ∑ s, r.prior s = 1)
    (c : ℝ) (hc : 0 < c) (constant : ∀ s, r.likelihood s r.observation = c) :
    caseOf (Policy := Policy) .evidence r = .evidence .beliefUnchanged := by
  have unchanged := EvidenceFromTheProcess.no_evidence_no_change
    r.prior r.likelihood r.observation normal c hc constant
  simp [caseOf, h.trans unchanged]

omit [Fintype Policy] [Nonempty Policy] in
theorem failed_habit_is_unchanged (r : R15TemporalHierarchy.TwoTickRecord Policy)
    (failed : r.outcome.succeeded = false) :
    caseOf (Policy := Policy) .habit r = .habit .unchanged := by
  simp [caseOf, failed]

omit [Fintype Policy] [Nonempty Policy] in
theorem liveness_case_is_live_iff (r : LiveRow) :
    caseOf (Policy := Policy) .liveness r = .liveness .live ↔
      R10ScheduledEntrypoint.LiveTick r := by
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

omit [Fintype Policy] [Nonempty Policy] in
/-- More tokens after the choice than up to it: the row prints `mostlyActing`. -/
theorem cost_mostlyActing (r : CostRow) (h : CostConforms r)
    (more : tokensWhere true r.jobs < tokensWhere false r.jobs) :
    caseOf (Policy := Policy) .cost r = .cost .mostlyActing := by
  obtain ⟨_, _, through, after⟩ := h
  have lt : r.reportedTokensThroughSelection < r.reportedTokensAfterSelection := by
    rw [through, after]; exact more
  simp [caseOf, costCase, lt, Nat.lt_asymm lt]

omit [Fintype Policy] [Nonempty Policy] in
/-- More tokens up to the choice than after it: the row prints `mostlyChoosing`. -/
theorem cost_mostlyChoosing (r : CostRow) (h : CostConforms r)
    (more : tokensWhere false r.jobs < tokensWhere true r.jobs) :
    caseOf (Policy := Policy) .cost r = .cost .mostlyChoosing := by
  obtain ⟨_, _, through, after⟩ := h
  have lt : r.reportedTokensAfterSelection < r.reportedTokensThroughSelection := by
    rw [through, after]; exact more
  simp [caseOf, costCase, lt]

omit [Fintype Policy] [Nonempty Policy] in
/-- Equal tokens and equal time on the two sides: the row prints `even`. -/
theorem cost_even (r : CostRow)
    (tokens : r.reportedTokensThroughSelection = r.reportedTokensAfterSelection)
    (time : r.msThroughSelection = r.msAfterSelection) :
    caseOf (Policy := Policy) .cost r = .cost .even := by
  simp [caseOf, costCase, tokens, time]

inductive RowVerdict | notRecorded | agrees (case : Case) | disagrees (case : Case)
  deriving DecidableEq, Repr

abbrev Records (Policy : Type) := (n : Node) → Option (NodeRecord Policy n)
abbrev Certificate := Node → RowVerdict

noncomputable def certify (records : Records Policy) : Certificate := fun n =>
  match records n with
  | none => .notRecorded
  | some r => if conforms n r then .agrees (caseOf n r) else .disagrees (caseOf n r)

def RowsCertified (certificate : Certificate) : Prop :=
  ∀ node, ∃ c, certificate node = .agrees c

/-- Selection's G schedule is the class-preference row's C at every tick.
The runtime builds `:class-preference` only for tau in `1 .. H`
(`CTauClassPreference.classPreference`), so G has H ticks and its tick `t`
(0-based) is runtime step `t + 1`. Without this, the schedule's provenance is
a producer label only and a schedule with any values passes (H4 review). -/
def ScheduleIsRows {Policy : Type} (r : ClassPreferenceRow)
    (g : R20Graph.PolicyExpectedFreeEnergy Policy) : Prop :=
  g.ticks = r.horizon ∧
    ∀ t : Fin g.ticks,
      g.schedule.value t = CTauClassPreference.classPreference r.horizon (t.val + 1)

/-- The menu: every policy, listed once. -/
def menu (Policy : Type) [Fintype Policy] : List Policy := (Finset.univ : Finset Policy).toList

/-- The consumer rows were judged on the values in their ports.  `Wired`
relates the ports to each other; this ties the precision row's E, G and F, and
the class-preference row's prediction and preference, to those ports, so a row
judged on some other F is not certified. The habit row's port carries E as the
normalised counts the click started from (`policyHabitPrior` of the row's
`before`, never its `after`: E is fixed within a trial, Parr :12645). G is compared after embedding the
row's real value in EReal: an infinite G port cannot certify this real-valued
precision row, and no toReal conversion drops infinity. -/
def RowsReadPorts (records : Records Policy) (ports : R20Graph.Ports Policy) : Prop :=
  (∀ r, records .precision = some r →
    r.E = ports.precisionHabit.value ∧ (fun π => (r.G π : EReal)) = ports.precisionG.value ∧
      r.F = ports.precisionF.value) ∧
  (∀ r, records .classPreference = some r →
    r.predicted = ports.classPredicted.value ∧
      CTauClassPreference.classPreference r.horizon r.tau = ports.classPreference.value ∧
      ScheduleIsRows r ports.selectionG) ∧
  (∀ s r, records .strategicFocus = some s → records .classPreference = some r →
    s.tick.preferenceAt r.tau = ports.strategicPreference.value) ∧
  (∀ h, records .habit = some h → ∀ π,
    ports.habitRowE.value π = (R15HabitPrior.policyHabitPrior h.before (menu Policy) π : ℝ)) ∧
  (∀ r, records .interoception = some r → ports.interoceptionRisk.value = r.reportedRisk)

/-- A click is certified only when every row agrees, its shared quantities
are the exact artifacts declared by the R20 graph, and the consumer rows were
judged on those artifacts. -/
def Certified (records : Records Policy) (certificate : Certificate)
    (ports : R20Graph.Ports Policy) : Prop :=
  RowsCertified certificate ∧ R20Graph.Wired records ports ∧ RowsReadPorts records ports

omit [Nonempty Policy] in
theorem rowsCertified_iff (records : Records Policy) :
    RowsCertified (certify records) ↔
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

omit [Nonempty Policy] in
theorem certified_iff (records : Records Policy) (ports : R20Graph.Ports Policy) :
    Certified records (certify records) ports ↔
      (∀ node, ∃ r, records node = some r ∧ conforms node r) ∧
        R20Graph.Wired records ports ∧ RowsReadPorts records ports := by
  rw [Certified, rowsCertified_iff]

omit [Nonempty Policy] in
/-- The precision row reads this run's post-observation inference F, whose
value is defined from its tick inputs by H1. -/
theorem certified_precision_reads_inference_F (records : Records Policy) (c : Certificate)
    (ports : R20Graph.Ports Policy) (certified : Certified records c ports)
    (r : PrecisionFromObservation.TickRecord Policy) (hr : records .precision = some r) :
    r.F = ports.inferenceF.value ∧ ports.inferenceF.producer = .postObservationInference ∧
      ports.inferenceF.runId = ports.runId := by
  rcases certified with ⟨_, wired, reads⟩
  exact ⟨(reads.1 r hr).2.2.trans (by rw [wired.fRead]), wired.fProducer, wired.fRun⟩

omit [Nonempty Policy] in
/-- The wrong-F control at the certificate: a precision row judged on an F
other than post-observation inference's defined F is not certified. K5. -/
theorem wrongF_not_certified (records : Records Policy) (c : Certificate)
    (ports : R20Graph.Ports Policy)
    (r : PrecisionFromObservation.TickRecord Policy) (hr : records .precision = some r)
    (wrong : r.F ≠ ports.inferenceF.value) : ¬ Certified records c ports :=
  fun certified => wrong (certified_precision_reads_inference_F records c ports certified r hr).1

omit [Nonempty Policy] in
/-- K11: a schedule labelled as the class-preference row's but holding other
values at some tick is not certified. -/
theorem wrongSchedule_not_certified (records : Records Policy) (c : Certificate)
    (ports : R20Graph.Ports Policy) (r : ClassPreferenceRow)
    (hr : records .classPreference = some r) (t : Fin ports.selectionG.ticks)
    (wrong : ports.selectionG.schedule.value t ≠
      CTauClassPreference.classPreference r.horizon (t.val + 1)) :
    ¬ Certified records c ports := by
  rintro ⟨_, _, reads⟩
  exact wrong ((reads.2.1 r hr).2.2.2 t)

omit [Nonempty Policy] in
/-- K11b: G over a different number of ticks than the row's horizon is not
certified. -/
theorem wrongTicks_not_certified (records : Records Policy) (c : Certificate)
    (ports : R20Graph.Ports Policy) (r : ClassPreferenceRow)
    (hr : records .classPreference = some r) (wrong : ports.selectionG.ticks ≠ r.horizon) :
    ¬ Certified records c ports := by
  rintro ⟨_, _, reads⟩
  exact wrong (reads.2.1 r hr).2.2.1

omit [Nonempty Policy] in
theorem missing_not_certified (records : Records Policy) (node : Node)
    (ports : R20Graph.Ports Policy) (missing : records node = none) :
    ¬ Certified records (certify records) ports := by
  intro certified
  rcases certified.1 node with ⟨c, hc⟩
  simp [certify, missing] at hc

omit [Nonempty Policy] in
theorem refused_row_disagrees (records : Records Policy) (node : Node) (r : NodeRecord Policy node)
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

omit [Nonempty Policy] in
/-- A certified click had a reviewer who was not its author. -/
theorem certified_author_is_not_reviewer (records : Records Policy)
    (ports : R20Graph.Ports Policy)
    (certified : Certified records (certify records) ports) :
    ∃ r : IndependenceRow, records .independence = some r ∧ r.author ≠ r.reviewer :=
  ((certified_iff records ports).mp certified).1 .independence

/-- The precision control: a record whose temperature did not move although F
differed between two policies that G ranks differently prints "unchanged" and
disagrees. -/
theorem precision_control_disagrees (records : Records TwoPolicy)
    (r : PrecisionFromObservation.TickRecord TwoPolicy)
    (present : records .precision = some r)
    (hG : r.G .a ≠ r.G .b) (hF : r.F .a ≠ r.F .b)
    (unchanged : r.betaPosterior = r.betaPrior) :
    certify records .precision = .disagrees (.precision .unchanged) := by
  have bad := PrecisionFromObservation.unchanged_discriminating_refused r hG hF unchanged
  rw [refused_row_disagrees records .precision r present bad]
  simp [caseOf, unchanged]

omit [Nonempty Policy] in
theorem evidence_control_disagrees (records : Records Policy)
    (present : records .evidence = some badEvidence) :
    certify records .evidence =
      .disagrees (caseOf (Policy := Policy) .evidence badEvidence) :=
  refused_row_disagrees records .evidence badEvidence present badEvidence_refused

omit [Nonempty Policy] in
/-- The habit control: a row whose outcome was not witnessed disagrees, whatever
its counts. -/
theorem habit_control_disagrees (records : Records Policy)
    (r : R15TemporalHierarchy.TwoTickRecord Policy) (present : records .habit = some r)
    (unwitnessed : r.outcome.witnessed = false) :
    certify records .habit = .disagrees (caseOf .habit r) :=
  refused_row_disagrees records .habit r present
    (R15TemporalHierarchy.unwitnessed_never_accepted r unwitnessed)

omit [Nonempty Policy] in
theorem class_control_disagrees (records : Records Policy)
    (present : records .classPreference = some badClass) :
    certify records .classPreference =
      .disagrees (caseOf (Policy := Policy) .classPreference badClass) :=
  refused_row_disagrees records .classPreference badClass present badClass_refused

def badStrategic : StrategicFocusRow := ⟨7, R15StrategicTarget.wrongClassTick⟩
omit [Nonempty Policy] in
theorem strategic_control_disagrees (records : Records Policy)
    (present : records .strategicFocus = some badStrategic) :
    certify records .strategicFocus =
      .disagrees (caseOf (Policy := Policy) .strategicFocus badStrategic) :=
  refused_row_disagrees records .strategicFocus badStrategic present
    (by exact R15StrategicTarget.wrongClassTick_rejected)

omit [Nonempty Policy] in
theorem liveness_control_disagrees (records : Records Policy)
    (present : records .liveness = some badLive) :
    certify records .liveness =
      .disagrees (caseOf (Policy := Policy) .liveness badLive) :=
  refused_row_disagrees records .liveness badLive present badLive_refused

omit [Nonempty Policy] in
theorem independence_control_disagrees (records : Records Policy)
    (present : records .independence = some badIndependence) :
    certify records .independence =
      .disagrees (caseOf (Policy := Policy) .independence badIndependence) :=
  refused_row_disagrees records .independence badIndependence present badIndependence_refused

omit [Nonempty Policy] in
theorem joint_control_disagrees (records : Records Policy)
    (present : records .jointAction = some R11JointAction.bothClaim) :
    certify records .jointAction =
      .disagrees (caseOf (Policy := Policy) .jointAction R11JointAction.bothClaim) :=
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

omit [Nonempty Policy] in
theorem cost_control_disagrees (records : Records Policy)
    (present : records .cost = some badCost) :
    certify records .cost =
      .disagrees (caseOf (Policy := Policy) .cost badCost) :=
  refused_row_disagrees records .cost badCost present badCost_refused

/-- A row whose preference ranks the alarm above the in-range reading. -/
def badInteroception : InteroceptionRow Policy :=
  { size := 2, viable := ({0} : Finset (Fin 2))
    preference := fun i : Fin 2 => if i = 0 then 1 / 10 else 9 / 10
    prediction := fun _ => R20Interoception.pointMass 1
    reportedRisk := fun _ => ⊤
    observed := (1 : Fin 2) }

omit [Fintype Policy] [Nonempty Policy] in
theorem badInteroception_refused : ¬ InteroceptionConforms (badInteroception (Policy := Policy)) := by
  intro h
  have wrong : (fun i : Fin 2 => if i = 0 then (1 : ℝ) / 10 else 9 / 10) 1 <
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) / 10 else 9 / 10) 0 :=
    h.1 (0 : Fin 2) (Finset.mem_singleton_self _) (1 : Fin 2)
      (show (1 : Fin 2) ∉ ({0} : Finset (Fin 2)) by decide)
  norm_num at wrong

omit [Nonempty Policy] in
theorem interoception_control_disagrees (records : Records Policy)
    (present : records .interoception = some badInteroception) :
    certify records .interoception =
      .disagrees (caseOf .interoception (badInteroception (Policy := Policy))) :=
  refused_row_disagrees records .interoception badInteroception present badInteroception_refused

/-- The gauge preference of `R20Interoception` on `Fin 2`: reading 0 is in range. -/
def gauge2 : R20Interoception.Distribution (Fin 2) := fun i => if i = 0 then 9 / 10 else 1 / 10

open PrecisionFromObservation (TwoPolicy) in
/-- The gauge example on two policies: `a` is expected to restore the reading,
`b` to leave it in alarm; observed in range. -/
def goodInteroception : InteroceptionRow TwoPolicy :=
  { size := 2, viable := ({0} : Finset (Fin 2)), preference := gauge2
    prediction := fun | .a => R20Interoception.pointMass 0 | .b => R20Interoception.pointMass 1
    reportedRisk := fun π => R20Interoception.interoceptiveRisk
      ((fun | .a => R20Interoception.pointMass 0 | .b => R20Interoception.pointMass 1 :
        TwoPolicy → R20Interoception.Distribution (Fin 2)) π) gauge2
    observed := (0 : Fin 2) }

theorem goodInteroception_conforms : InteroceptionConforms goodInteroception := by
  constructor
  · show ∀ v ∈ ({0} : Finset (Fin 2)), ∀ n ∉ ({0} : Finset (Fin 2)), gauge2 n < gauge2 v
    intro v hv n hn
    rw [Finset.mem_singleton] at hv hn
    subst hv
    norm_num [gauge2, hn]
  · intro π
    cases π <;> rfl

theorem goodInteroception_inRange :
    caseOf .interoception goodInteroception = .interoception .inRange := by
  show Case.interoception (if (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) then .inRange
    else .outOfRange) = _
  simp

omit [Fintype Policy] [Nonempty Policy] in
/-- In a conforming row, a policy predicted to restore a viable reading with
certainty reports lower risk than one predicted to leave it out of range. -/
theorem interoception_restoring_lower_risk (r : InteroceptionRow Policy)
    (h : InteroceptionConforms r)
    {restored outside : Fin r.size} (restoredViable : restored ∈ r.viable)
    (notViable : outside ∉ r.viable)
    (restoredPositive : 0 < r.preference restored)
    (outsidePositive : 0 < r.preference outside)
    {p q : Policy}
    (pRestores : r.prediction p = R20Interoception.pointMass restored)
    (qLeaves : r.prediction q = R20Interoception.pointMass outside) :
    r.reportedRisk p < r.reportedRisk q := by
  rw [h.2 p, h.2 q, pRestores, qLeaves]
  exact R20Interoception.viable_point_has_lower_risk h.1 restoredViable notViable
    restoredPositive outsidePositive

omit [Nonempty Policy] in
/-- In a certified click, selection scores each policy with the interoception
row's reported risk. -/
theorem certified_selection_reads_interoception (records : Records Policy)
    (ports : R20Graph.Ports Policy) (certified : Certified records (certify records) ports)
    (r : InteroceptionRow Policy) (hr : records .interoception = some r) :
    ports.selectionInteroceptionRisk.value = r.reportedRisk := by
  rcases certified with ⟨_, wired, reads⟩
  rw [wired.interoceptionRead]
  exact reads.2.2.2.2 r hr

omit [Nonempty Policy] in
/-- In a certified click, of two policies with the same finite class G, the
one predicted to restore a viable reading scores lower than the one predicted
to leave it out of range: the out-of-range reading is ordinary risk, with no
special rule. -/
theorem certified_restoring_policy_scores_lower (records : Records Policy)
    (ports : R20Graph.Ports Policy) (certified : Certified records (certify records) ports)
    (r : InteroceptionRow Policy) (hr : records .interoception = some r)
    {restored outside : Fin r.size} (restoredViable : restored ∈ r.viable)
    (notViable : outside ∉ r.viable)
    (restoredPositive : 0 < r.preference restored)
    (outsidePositive : 0 < r.preference outside)
    {p q : Policy}
    (pRestores : r.prediction p = R20Interoception.pointMass restored)
    (qLeaves : r.prediction q = R20Interoception.pointMass outside)
    (g : ℝ) (gp : ports.selectionG.value p = g) (gq : ports.selectionG.value q = g) :
    R20Graph.selectionScore ports p < R20Graph.selectionScore ports q := by
  obtain ⟨row, present, good⟩ := ((certified_iff records ports).mp certified).1 .interoception
  rw [hr] at present
  have same : row = r := (Option.some.inj present).symm
  subst same
  have reads := certified_selection_reads_interoception records ports certified row hr
  unfold R20Graph.selectionScore
  rw [gp, gq, reads]
  exact EReal.add_lt_add_left_coe (interoception_restoring_lower_risk row good restoredViable
    notViable restoredPositive outsidePositive pRestores qLeaves) g

/-- Fixed print order for the run's succinct certificate. -/
def nodeOrder : List Node :=
  [.precision, .evidence, .habit, .classPreference, .strategicFocus,
   .liveness, .independence, .jointAction, .cost, .interoception]

def summary (certificate : Certificate) : List (Node × RowVerdict) :=
  nodeOrder.map fun node => (node, certificate node)

#print axioms certified_iff
#print axioms wrongF_not_certified
#print axioms certified_precision_reads_inference_F
#print axioms wrongSchedule_not_certified
#print axioms wrongTicks_not_certified

end
end DarkTower.WarMachine.R20Certificate
