import DarkTower.WarMachine.R20Run

/-!
# R20: the precision row's E is the habit row's counts

In plain terms: within one click, the habit prior E that enters the policy
prior and the precision update is the normalised count of what has worked,
read from the slow state this click started from. Over a run, a click's E is
therefore the counts left by the previous click's outcome: a success of a
policy raises that policy's E at the next click, and a failure leaves
it where it was.

Sources.

* Friston et al. (2016), `refs/friston2016.txt` :436-442: "the vectors
  encoding beliefs about the initial state and selected policy accumulate
  evidence by simply counting the number of times they occur ... habit
  learning (in terms of policy selection)"; :675-678: "prior beliefs about
  policies were initialised to e = 4 ... These concentration parameters can
  be regarded as the number of times each ... policy has been encountered in
  previous trials". E is the mean of `Dir(e)`, `e / Σ e`.
* Parr, Pezzulo and Friston (2022), `refs/parr2022.txt` :12645: "E is a
  vector of fixed beliefs about policies". Fixed within a trial: E is read
  before this click's outcome, so it uses the habit row's `before`, not its
  `after` (`postOutcomeE_refused`).

The counts are indexed by policy, as in the sources: the habit row's slow
state is keyed by the menu's `Policy` (`R15TemporalHierarchy`), and E at `π` is
`π`'s count over the sum of the menu's counts. (Until 2026-10-22 the counts
were keyed by action class, with a menu condition of one policy per class; that
layer came from the earlier implementation, has no cited source, and is gone.)

What is counted follows Parr p. 209 (which policies were *successful*), as
`R15HabitPrior` says; Friston et al. (2016) count how often a policy was
selected. Both are cited active inference; this module follows Parr.

The habit row supplies selection's E (`R20Graph.Edge.habitToSelectionHabit`),
and the certificate checks the supplied value (`RowsReadPorts`), so a
certified click's E is its counts' prior with no further hypothesis.

Results, for a certified click:

* `selection_E_is_habit`: selection's E port is the habit prior of the habit
  row's before-state;
* `certified_habitFeedsE`: so the precision row's E is that prior too;
* `fed_E_sums_to_one`: that E is a distribution over the menu's policies;
* `run_E_reads_previous_outcome`: over a carried run, click `i + 1`'s E is
  the prior of the counts after click `i`'s outcome;
* `success_raises_next_E`, `failure_keeps_next_E`: what one outcome does to
  the next click's E.

Controls, each refused by `HabitFeedsE`: an E not computed from the counts
(uniform where the counts give 3/5 and 2/5); an E computed from the counts
after this click's own outcome. `example_feeds` shows the condition can be met.
-/

namespace DarkTower.WarMachine.R20HabitPrior

open DarkTower.WarMachine.CTauClassPreference
open DarkTower.WarMachine.R20Graph (Node)
open DarkTower.WarMachine.R20Certificate
open DarkTower.WarMachine.R20FocusedSelection
open DarkTower.WarMachine.R20Run
open DarkTower.WarMachine.R15StrategicTarget
open DarkTower.WarMachine.R15TemporalHierarchy
open DarkTower.WarMachine.R15HabitPrior

open scoped BigOperators
noncomputable section
variable {Policy : Type} [Fintype Policy] [Nonempty Policy]
attribute [local instance] Classical.propDecidable

omit [Nonempty Policy] in
theorem menu_nodup : (menu Policy).Nodup := Finset.nodup_toList _

omit [Nonempty Policy] in
theorem mem_menu (π : Policy) : π ∈ menu Policy := by simp [menu]

theorem menu_ne_nil : menu Policy ≠ [] := by
  obtain ⟨π⟩ := (inferInstance : Nonempty Policy)
  exact List.ne_nil_of_mem (mem_menu π)

omit [Nonempty Policy] in
/-- Summing over the policies is summing over the menu. -/
theorem sum_menu (f : Policy → ℚ) : ∑ π, f π = ((menu Policy).map f).sum := by
  rw [menu, Finset.sum_map_toList]

/-- The precision row's E is the habit prior of the slow state this click
started from. -/
def HabitFeedsE (records : Records Policy) : Prop :=
  ∀ h p, records .habit = some h → records .precision = some p →
    ∀ π, p.E π = (policyHabitPrior h.before (menu Policy) π : ℝ)

omit [Nonempty Policy] in
/-- In a certified click, selection's E port, which enters the policy prior,
is the habit prior of the counts the click started from: the habit row
supplies it (`habitToSelectionHabit`). -/
theorem selection_E_is_habit {records : Records Policy}
    {ports : R20Graph.Ports Policy} (certified : Certified records (certify records) ports)
    {h : TwoTickRecord Policy} (hh : records .habit = some h) (π : Policy) :
    ports.selectionHabit.value π = (policyHabitPrior h.before (menu Policy) π : ℝ) := by
  rcases certified with ⟨_, wired, reads⟩
  rw [wired.habitIntoSelection]
  exact reads.2.2.2 h hh π

omit [Nonempty Policy] in
/-- A certified click's precision row reads the habit prior: certification
implies `HabitFeedsE`. -/
theorem certified_habitFeedsE {records : Records Policy}
    {ports : R20Graph.Ports Policy} (certified : Certified records (certify records) ports) :
    HabitFeedsE records := by
  intro h p hh hp π
  have reads := certified.2.2
  rw [(reads.1 p hp).1, certified.2.1.habitRead]
  exact selection_E_is_habit certified hh π

/-- A positive quotient of a nonnegative numerator has a positive numerator. -/
private theorem num_pos_of_div_pos {x y : ℚ} (hx : 0 ≤ x) (pos : 0 < x / y) : 0 < x := by
  rcases hx.lt_or_eq with lt | eq
  · exact lt
  · rw [← eq, zero_div] at pos
    exact absurd pos (lt_irrefl 0)

/-- A conforming precision row has positive E, so every policy has positive
count and the fed E sums to one. -/
theorem fed_E_sums_to_one {records : Records Policy}
    (fed : HabitFeedsE records)
    {h : TwoTickRecord Policy} {p : PrecisionFromObservation.TickRecord Policy}
    (hh : records .habit = some h) (hp : records .precision = some p)
    (conforms : PrecisionFromObservation.Conforms p) :
    ∑ π, p.E π = 1 := by
  have positive : PositiveAlphas h.before (menu Policy) := by
    intro π _
    have e := conforms.1 π
    rw [fed h p hh hp π] at e
    exact num_pos_of_div_pos (by simp [policyAlpha]) (by exact_mod_cast e)
  have sum := policyHabitPrior_sum_one menu_ne_nil positive
  rw [← sum_menu] at sum
  simp only [fed h p hh hp]
  exact_mod_cast sum

/-! ## Over a run -/

omit [Nonempty Policy] in
/-- Over a carried run, click `i + 1`'s E
is the habit prior of the counts after click `i`'s outcome. -/
theorem run_E_reads_previous_outcome {relation : Target → Target → TargetRelation}
    {c : ℕ → Click Policy} {n : ℕ} (run : RunCertified relation c n)
    (hab : ℕ → TwoTickRecord Policy) (hh : ∀ i ≤ n, (c i).records .habit = some (hab i))
    (pr : ℕ → PrecisionFromObservation.TickRecord Policy)
    (hp : ∀ i ≤ n, (c i).records .precision = some (pr i))
    {i : ℕ} (hi : i < n) (π : Policy) :
    (pr (i + 1)).E π =
      (policyHabitPrior (advance (hab i).before (hab i).outcome) (menu Policy) π : ℝ) := by
  have fed := fun i (hi : i ≤ n) => certified_habitFeedsE (run.1 i hi).1.1
  obtain ⟨r, hr, good⟩ := row_of_certified (run.1 i (by omega)).1 .habit
  rw [hh i (by omega)] at hr
  cases hr
  have carried := (run.2 i hi).habit _ _ (hh i (by omega)) (hh (i + 1) (by omega))
  rw [fed (i + 1) hi _ _ (hh (i + 1) (by omega)) (hp (i + 1) hi) π, carried, good.2.2, good.2.1]

omit [Nonempty Policy] in
/-- A witnessed success of policy `π` at click `i` raises `π`'s E at click
`i + 1`, whenever another policy holds positive count. -/
theorem success_raises_next_E {relation : Target → Target → TargetRelation}
    {c : ℕ → Click Policy} {n : ℕ} (run : RunCertified relation c n)
    (hab : ℕ → TwoTickRecord Policy) (hh : ∀ i ≤ n, (c i).records .habit = some (hab i))
    (pr : ℕ → PrecisionFromObservation.TickRecord Policy)
    (hp : ∀ i ≤ n, (c i).records .precision = some (pr i))
    {i : ℕ} (hi : i < n) (π : Policy)
    (success : (hab i).outcome = ⟨π, true, true⟩)
    (positiveTotal : 0 < totalAlpha (hab i).before (menu Policy))
    (outsideMass : policyAlpha (hab i).before π < totalAlpha (hab i).before (menu Policy)) :
    (pr i).E π < (pr (i + 1)).E π := by
  have fed := fun i (hi : i ≤ n) => certified_habitFeedsE (run.1 i hi).1.1
  rw [run_E_reads_previous_outcome run hab hh pr hp hi π, success,
    fed i (by omega) _ _ (hh i (by omega)) (hp i (by omega)) π]
  exact_mod_cast success_strictly_increases_habit menu_nodup (mem_menu π) positiveTotal outsideMass

omit [Nonempty Policy] in
/-- A witnessed failure at click `i` leaves every policy's E at click `i + 1`
where it was. -/
theorem failure_keeps_next_E {relation : Target → Target → TargetRelation}
    {c : ℕ → Click Policy} {n : ℕ} (run : RunCertified relation c n)
    (hab : ℕ → TwoTickRecord Policy) (hh : ∀ i ≤ n, (c i).records .habit = some (hab i))
    (pr : ℕ → PrecisionFromObservation.TickRecord Policy)
    (hp : ∀ i ≤ n, (c i).records .precision = some (pr i))
    {i : ℕ} (hi : i < n) (k : Policy) (failure : (hab i).outcome = ⟨k, true, false⟩) (π : Policy) :
    (pr (i + 1)).E π = (pr i).E π := by
  have fed := fun i (hi : i ≤ n) => certified_habitFeedsE (run.1 i hi).1.1
  rw [run_E_reads_previous_outcome run hab hh pr hp hi π, failure,
    fed i (by omega) _ _ (hh i (by omega)) (hp i (by omega)) π,
    failure_leaves_habit_unchanged]

/-! ## Controls

One click with the habit row's before-state `countsAB` (policy `a` count 3,
policy `b` count 2), so the counts give E = (3/5, 2/5). -/

open PrecisionFromObservation (TwoPolicy)

def countsAB : SlowState TwoPolicy := [(.a, ⟨3, 1⟩), (.b, ⟨2, 1⟩)]

/-! The count lemmas below take the decidable-equality instance on `TwoPolicy`
as an ordinary implicit argument, so a rewrite unifies it with whichever
instance a statement was elaborated with. -/

private theorem a_ne_b : TwoPolicy.a ≠ TwoPolicy.b := fun h => by cases h

theorem alpha_a {_ : DecidableEq TwoPolicy} : policyAlpha countsAB .a = 3 := by
  simp [policyAlpha, countsAB, countsFor]

theorem alpha_b {_ : DecidableEq TwoPolicy} : policyAlpha countsAB .b = 2 := by
  simp [policyAlpha, countsAB, countsFor, a_ne_b]

theorem totalAlpha_menu2 {_ : DecidableEq TwoPolicy} (state : SlowState TwoPolicy) :
    totalAlpha state (menu TwoPolicy) = policyAlpha state .a + policyAlpha state .b := by
  have univ : (Finset.univ : Finset TwoPolicy) = {.a, .b} := by
    ext x; cases x <;> simp
  rw [totalAlpha, menu, Finset.sum_map_toList, univ, Finset.sum_pair a_ne_b]

theorem total_countsAB {_ : DecidableEq TwoPolicy} : totalAlpha countsAB (menu TwoPolicy) = 5 := by
  rw [totalAlpha_menu2, alpha_a, alpha_b]; norm_num

def habitAt (before : SlowState TwoPolicy) : TwoTickRecord TwoPolicy :=
  let outcome : FastOutcome TwoPolicy := ⟨.a, true, true⟩
  ⟨before, outcome, advance before outcome, advance before outcome⟩

def precisionWithE (E : Policy → ℝ) : PrecisionFromObservation.TickRecord Policy :=
  ⟨E, fun _ => 0, fun _ => 0, fun _ => 1 / 2, fun _ => 1 / 2, 1, 1⟩

def clickRecords (E : TwoPolicy → ℝ) : Records TwoPolicy :=
  rows (habitAt countsAB) (evidenceAt (fun _ => 1 / 2) (fun _ => 1 / 2)) (precisionWithE E)
    ⟨7, tickAt 7 [7]⟩

def countedE : TwoPolicy → ℝ := fun | .a => 3 / 5 | .b => 2 / 5

theorem example_feeds : HabitFeedsE (clickRecords countedE) := by
  intro h p hh hp π
  simp only [clickRecords, rows] at hh hp
  cases hh; cases hp
  cases π <;> simp only [precisionWithE, countedE, habitAt, policyHabitPrior]
  · rw [alpha_a, total_countsAB]; norm_num
  · rw [alpha_b, total_countsAB]; norm_num

/-- E uniform although the counts give 3/5 and 2/5. -/
theorem uncountedE_refused : ¬ HabitFeedsE (clickRecords fun _ => 1 / 2) := by
  intro fed
  have := fed _ _ rfl rfl .a
  simp only [precisionWithE, habitAt, policyHabitPrior] at this
  rw [alpha_a, total_countsAB] at this; norm_num at this

/-- E computed from the counts after this click's own success of policy `a`,
(4/6, 2/6): the click's outcome read into its own choice. -/
theorem postOutcomeE_refused :
    ¬ HabitFeedsE (clickRecords fun | .a => 2 / 3 | .b => 1 / 3) := by
  intro fed
  have := fed _ _ rfl rfl .a
  simp only [precisionWithE, habitAt, policyHabitPrior] at this
  rw [alpha_a, total_countsAB] at this; norm_num at this

#print axioms selection_E_is_habit
#print axioms fed_E_sums_to_one
#print axioms success_raises_next_E
#print axioms failure_keeps_next_E
#print axioms example_feeds

end
end DarkTower.WarMachine.R20HabitPrior
