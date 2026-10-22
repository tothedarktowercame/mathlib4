import DarkTower.WarMachine.R20FocusedSelection

/-!
# R20 over a run: what one click hands to the next

In plain terms: the certificate judges one click. A machine is a sequence of
clicks, and each click starts from what the previous one left. This module
states what carries across a click boundary, and proves what follows over a
run: the habit counts are the fold of every outcome, the belief about the
initial state is the count of every posterior, the prior precision does not
move, and each click's strategic row names the focus the previous click held.

Friston et al. (2017), `refs/friston2017.txt`:

* :718-721: "at the end of each sequence of observations (i.e., trial of
  observation epochs), the expected (concentration) parameters are updated to
  mediate learning over trials". A click is a trial here.
* :378-379: concentration parameters "can be regarded as the number of
  occurrences encountered in the past".
* eq. 2.7, :678: `d = d + s1`, the update of the initial-state counts.
  :820-822: "if a particular state is encountered frequently, it will come to
  dominate posterior expectations" (`repeated_state_dominates`).
* eq. 2.1, :324-339: `β` is a parameter of the model with prior `Γ(1, β)`;
  :1356-1357: in that paper "the only parameters that are updated are those
  encoding prior beliefs about the initial state". So the prior precision is
  the same at every click; carrying a click's posterior `β` forward as the
  next prior is refused (`posteriorBetaCarried_refused`).

The evidence row's prior is the mean of `Dir(d)`, `d / Σ d`. Friston writes
the expected log, `ψ(d) − ψ(d0)`, inside inference; the row records a
probability, and the mean is the probability that `Dir(d)` assigns.

The habit counts (`R15TemporalHierarchy`) are the same kind of parameter: the
next click consumes the slow state this click produced. The strategic row's
`previousFocus` is, by its meaning, the focus of the previous click; this
module makes that a condition, so a focus change is read off two clicks.

Results, for a run whose clicks are each focus-certified and carried:

* `run_habit_accumulates`: the last click's slow state is the fold of
  `advance` over every click's outcome, from the first click's;
* `run_concentration_accumulates`: the d counts at click `n` are the first
  click's plus every earlier posterior;
* `repeated_state_dominates`: if every posterior so far was certain of `s`,
  the prior on `s` at click `n` is `(d₀ s + n) / (Σ d₀ + n)`, and it tends to 1;
* `run_betaPrior_constant`: every click has the first click's prior `β`;
* `run_focus_case`: a click's strategic case is `focusKept` exactly when its
  focus equals the previous click's;
* `run_ids_distinct`: no two clicks share a run id, so a click whose
  precision row reads another click's G is not wired (`stale_G_not_wired`).

Controls, each refused by `Carries`: habit counts reset between clicks; the
d counts not updated; the posterior `β` carried as prior; a stale previous
focus; a replayed run id. `example_carries` shows the conditions can be met.
-/

namespace DarkTower.WarMachine.R20Run

open DarkTower.WarMachine.CTauClassPreference
open DarkTower.WarMachine.R20Graph (Node)
open DarkTower.WarMachine.R20Certificate
open DarkTower.WarMachine.R20FocusedSelection
open DarkTower.WarMachine.R15StrategicTarget
open DarkTower.WarMachine.R15TemporalHierarchy
open Filter Topology

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- One click as the run keeps it: its rows, its ports, its outer choice, and
the initial-state counts `d` it started from. -/
structure Click where
  records : Records
  ports : R20Graph.Ports Policy
  selection : OuterSelection
  d : Hidden → ℝ

/-- The evidence row's prior is the mean of `Dir(d)`. -/
def PriorFromCounts (c : Click) : Prop :=
  (∀ s, 0 < c.d s) ∧
    ∀ r, c.records .evidence = some r → r.prior = fun s => c.d s / ∑ x, c.d x

/-- What click `a` hands to the next click `b`. -/
structure Carries (a b : Click) : Prop where
  runAdvances : a.ports.runId < b.ports.runId
  habit : ∀ ra rb, a.records .habit = some ra → b.records .habit = some rb →
    rb.before = ra.nextConsumed
  counts : ∀ ra, a.records .evidence = some ra → b.d = a.d + ra.posterior
  betaPrior : ∀ ra rb, a.records .precision = some ra → b.records .precision = some rb →
    rb.betaPrior = ra.betaPrior
  focus : ∀ sa sb, a.records .strategicFocus = some sa →
    b.records .strategicFocus = some sb → sb.previousFocus = sa.tick.focus

/-- Clicks `0 .. n`: each focus-certified with its prior read from its counts,
and each carried into the next. -/
def RunCertified (relation : Target → Target → TargetRelation) (c : ℕ → Click) (n : ℕ) :
    Prop :=
  (∀ i ≤ n, FocusCertified relation (c i).records (c i).ports (c i).selection ∧
    PriorFromCounts (c i)) ∧
  ∀ i < n, Carries (c i) (c (i + 1))

/-- A certified click has every row, and every row conforms. -/
theorem row_of_certified {relation : Target → Target → TargetRelation} {c : Click}
    (h : FocusCertified relation c.records c.ports c.selection) (node : Node) :
    ∃ r, c.records node = some r ∧ conforms node r :=
  ((certified_iff c.records c.ports).mp h.1).1 node

/-! ## Habit counts -/

/-- The fold, stated on the rows: if each row is R15 feedback and each click
consumes the previous click's slow state, the last after-state is every
outcome folded into the first before-state. -/
theorem habit_fold (hab : ℕ → TwoTickRecord) (n : ℕ)
    (feedback : ∀ i ≤ n, TwoTickFeedback (hab i))
    (carried : ∀ i < n, (hab (i + 1)).before = (hab i).nextConsumed) :
    (hab n).after =
      ((List.range (n + 1)).map fun i => (hab i).outcome).foldl advance (hab 0).before := by
  induction n with
  | zero => simp [(feedback 0 le_rfl).2.1]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append,
      ← ih (fun i hi => feedback i (by omega)) (fun i hi => carried i (by omega))]
    have fb := feedback (n + 1) le_rfl
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [fb.2.1, carried n (by omega), (feedback n (by omega)).2.2]

theorem run_habit_accumulates {relation : Target → Target → TargetRelation}
    {c : ℕ → Click} {n : ℕ} (run : RunCertified relation c n)
    (hab : ℕ → TwoTickRecord) (hh : ∀ i ≤ n, (c i).records .habit = some (hab i)) :
    (hab n).after =
      ((List.range (n + 1)).map fun i => (hab i).outcome).foldl advance (hab 0).before := by
  apply habit_fold hab n
  · intro i hi
    obtain ⟨r, hr, good⟩ := row_of_certified (run.1 i hi).1 .habit
    rw [hh i hi] at hr
    cases hr
    exact good
  · intro i hi
    exact (run.2 i hi).habit _ _ (hh i (by omega)) (hh (i + 1) (by omega))

/-! ## Initial-state counts -/

theorem run_concentration_accumulates {relation : Target → Target → TargetRelation}
    {c : ℕ → Click} {n : ℕ} (run : RunCertified relation c n)
    (ev : ℕ → EvidenceRow) (he : ∀ i ≤ n, (c i).records .evidence = some (ev i)) :
    (c n).d = (c 0).d + ∑ i ∈ Finset.range n, (ev i).posterior := by
  induction n with
  | zero => simp
  | succ n ih =>
    have run' : RunCertified relation c n :=
      ⟨fun i hi => run.1 i (by omega), fun i hi => run.2 i (by omega)⟩
    rw [Finset.sum_range_succ, ← add_assoc,
      ← ih run' (fun i hi => he i (by omega)),
      (run.2 n (by omega)).counts _ (he n (by omega))]

def pointMass (s : Hidden) : Hidden → ℝ := fun x => if x = s then 1 else 0

/-- `(a + n) / (b + n)` tends to 1. -/
theorem shifted_ratio_tendsto_one (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => (a + n) / (b + n)) atTop (𝓝 1) := by
  have key : ∀ n : ℕ, (a + n) / (b + n) = 1 - (b - a) / (b + n) := by
    intro n
    have : (b + n) ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [key]
  have : Tendsto (fun n : ℕ => (b - a) / (b + n)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_left _ b tendsto_natCast_atTop_atTop
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this

/-- Friston 2017 :820-822. If every posterior so far was certain of `s`, the
prior on `s` at click `n` is `(d₀ s + n) / (Σ d₀ + n)`. -/
theorem repeated_state_prior {relation : Target → Target → TargetRelation}
    {c : ℕ → Click} {n : ℕ} (run : RunCertified relation c n)
    (ev : ℕ → EvidenceRow) (he : ∀ i ≤ n, (c i).records .evidence = some (ev i))
    (s : Hidden) (certain : ∀ i < n, (ev i).posterior = pointMass s) :
    (ev n).prior s = ((c 0).d s + n) / ((∑ x, (c 0).d x) + n) := by
  have counts := run_concentration_accumulates run ev he
  have point : ∀ x, ∑ i ∈ Finset.range n, (ev i).posterior x = n * pointMass s x := by
    intro x
    rw [Finset.sum_congr rfl (fun i hi => congrFun (certain i (Finset.mem_range.mp hi)) x)]
    simp
  rw [(run.1 n le_rfl).2.2 _ (he n le_rfl), counts]
  simp only [Pi.add_apply, Finset.sum_apply, point, Fin.sum_univ_two]
  fin_cases s <;> simp [pointMass] <;> ring

/-- The repeated state comes to dominate: along runs that keep observing it,
its prior tends to 1. -/
theorem repeated_state_dominates (d₀ : Hidden → ℝ) (pos : ∀ x, 0 < d₀ x) (s : Hidden) :
    Tendsto (fun n : ℕ => (d₀ s + n) / ((∑ x, d₀ x) + n)) atTop (𝓝 1) :=
  shifted_ratio_tendsto_one _ _ (Finset.sum_pos (fun x _ => pos x) Finset.univ_nonempty)

/-! ## Prior precision, focus, run ids -/

theorem run_betaPrior_constant {relation : Target → Target → TargetRelation}
    {c : ℕ → Click} {n : ℕ} (run : RunCertified relation c n)
    (pr : ℕ → PrecisionFromObservation.TickRecord Policy)
    (hp : ∀ i ≤ n, (c i).records .precision = some (pr i)) :
    ∀ i ≤ n, (pr i).betaPrior = (pr 0).betaPrior := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [(run.2 i (by omega)).betaPrior _ _ (hp i (by omega)) (hp (i + 1) hi), ih (by omega)]

/-- The strategic case of click `i + 1` is read off two clicks. -/
theorem run_focus_case {relation : Target → Target → TargetRelation}
    {c : ℕ → Click} {n : ℕ} (run : RunCertified relation c n) {i : ℕ} (hi : i < n)
    (sa sb : StrategicFocusRow) (ha : (c i).records .strategicFocus = some sa)
    (hb : (c (i + 1)).records .strategicFocus = some sb) :
    caseOf .strategicFocus sb = .strategicFocus .focusKept ↔ sb.tick.focus = sa.tick.focus := by
  have prev := (run.2 i hi).focus _ _ ha hb
  by_cases eq : sb.tick.focus = sa.tick.focus
  · simp [caseOf, prev, eq]
  · have ne : sa.tick.focus ≠ sb.tick.focus := fun h => eq h.symm
    simp [caseOf, prev, eq, ne]

theorem run_ids_distinct {relation : Target → Target → TargetRelation}
    {c : ℕ → Click} {n : ℕ} (run : RunCertified relation c n) {i j : ℕ}
    (hij : i < j) (hj : j ≤ n) : (c i).ports.runId < (c j).ports.runId := by
  induction j with
  | zero => omega
  | succ j ih =>
    have step := (run.2 j (by omega)).runAdvances
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with lt | rfl
    · exact (ih lt (by omega)).trans step
    · exact step

/-- A later click whose precision row reads an earlier click's G is not
wired: that G carries the earlier run id. -/
theorem stale_G_not_wired {relation : Target → Target → TargetRelation}
    {c : ℕ → Click} {n : ℕ} (run : RunCertified relation c n) {i j : ℕ}
    (hij : i < j) (hj : j ≤ n)
    (stale : (c j).ports.precisionG = (c i).ports.selectionG) :
    ¬ R20Graph.Wired (c j).records (c j).ports := by
  intro wired
  have lt := run_ids_distinct run hij hj
  have wi := ((certified_iff (c i).records (c i).ports).mp (run.1 i (by omega)).1.1).2.1
  have run_i := wi.gRun
  rw [← stale, wired.gRead, wired.gRun] at run_i
  exact (ne_of_gt lt) run_i

/-! ## Controls

Two clicks with the habit, evidence, precision and strategic rows present.
The other rows are absent: `Carries` is about the four rows that cross the
boundary, and a certified run supplies all of them (`row_of_certified`). -/

def rows (h : TwoTickRecord) (e : EvidenceRow)
    (p : PrecisionFromObservation.TickRecord Policy) (s : StrategicFocusRow) : Records
  | .habit => some h
  | .evidence => some e
  | .precision => some p
  | .strategicFocus => some s
  | _ => none

def evidenceAt (prior posterior : Hidden → ℝ) : EvidenceRow :=
  ⟨prior, fun _ _ => 1, true, posterior⟩

def precisionAt (betaPrior betaPosterior : ℝ) : PrecisionFromObservation.TickRecord Policy :=
  ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 1 / 2, fun _ => 1 / 2, betaPrior, betaPosterior⟩

def selection0 : OuterSelection := ⟨[⟨7, 1⟩], ⟨7, 1⟩⟩

def counts0 : Hidden → ℝ := fun _ => 1

/-- Click 0: focus 7, posterior certain of state 0, `β` moved from 1 to 1/2. -/
def click0 : Click :=
  ⟨rows successRecord (evidenceAt (fun _ => 1 / 2) (pointMass 0)) (precisionAt 1 (1 / 2))
    ⟨7, tickAt 7 [7]⟩, R20Graph.goodPorts 0, selection0, counts0⟩

/-- The successor that click 0 hands on. -/
def nextHabit : TwoTickRecord :=
  { before := successRecord.nextConsumed, outcome := failureOutcome
    after := advance successRecord.nextConsumed failureOutcome
    nextConsumed := advance successRecord.nextConsumed failureOutcome }

def click1With (h : TwoTickRecord) (d : Hidden → ℝ) (betaPrior : ℝ) (previousFocus : Target)
    (run : R20Graph.RunId) : Click :=
  ⟨rows h (evidenceAt (fun s => d s / ∑ x, d x) (pointMass 0)) (precisionAt betaPrior 1)
    ⟨previousFocus, tickAt 3 [3]⟩, R20Graph.goodPorts run, selection0, d⟩

def click1 : Click := click1With nextHabit (counts0 + pointMass 0) 1 7 1

theorem example_carries : Carries click0 click1 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro ra rb ha hb
    simp only [click0, click1, click1With, rows] at ha hb
    cases ha; cases hb; rfl
  · intro ra ha
    simp only [click0, rows] at ha
    cases ha; rfl
  · intro ra rb ha hb
    simp only [click0, click1, click1With, rows] at ha hb
    cases ha; cases hb; rfl
  · intro sa sb ha hb
    simp only [click0, click1, click1With, rows] at ha hb
    cases ha; cases hb; rfl

/-- The successor's prior is the mean of its counts, `(2/3, 1/3)`. -/
theorem click1_prior : PriorFromCounts click1 := by
  refine ⟨fun s => ?_, fun r hr => ?_⟩
  · simp only [click1, click1With, counts0, pointMass, Pi.add_apply]
    split_ifs <;> norm_num
  · simp only [click1, click1With, rows] at hr
    cases hr
    rfl

/-- Habit counts reset to the first click's before-state. -/
theorem habitReset_refused :
    ¬ Carries click0 (click1With { nextHabit with before := initialState }
      (counts0 + pointMass 0) 1 7 1) := by
  intro h
  have := h.habit _ _ rfl rfl
  simp only [successRecord] at this
  exact advance_ne_before initialState successOutcome this.symm

/-- The counts not updated: click 1 starts from click 0's d. -/
theorem countsNotUpdated_refused : ¬ Carries click0 (click1With nextHabit counts0 1 7 1) := by
  intro h
  have := congrFun (h.counts _ rfl) 0
  simp [click0, click1With, evidenceAt, counts0, pointMass] at this

/-- Click 0's posterior `β` (1/2) carried as click 1's prior. -/
theorem posteriorBetaCarried_refused :
    ¬ Carries click0 (click1With nextHabit (counts0 + pointMass 0) (1 / 2) 7 1) := by
  intro h
  have := h.betaPrior _ _ rfl rfl
  norm_num [precisionAt] at this

/-- Click 1 reports a previous focus that click 0 did not hold. -/
theorem staleFocus_refused :
    ¬ Carries click0 (click1With nextHabit (counts0 + pointMass 0) 1 8 1) := by
  intro h
  have := h.focus _ _ rfl rfl
  simp [tickAt] at this

/-- Click 1 replays click 0's run id. -/
theorem replayedRun_refused :
    ¬ Carries click0 (click1With nextHabit (counts0 + pointMass 0) 1 7 0) := by
  intro h
  exact absurd h.runAdvances (by decide)

#print axioms run_habit_accumulates
#print axioms repeated_state_prior
#print axioms stale_G_not_wired
#print axioms example_carries

end
end DarkTower.WarMachine.R20Run
