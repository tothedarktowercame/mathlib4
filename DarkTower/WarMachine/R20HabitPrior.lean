import DarkTower.WarMachine.R20Run

/-!
# R20: the precision row's E is the habit row's counts

In plain terms: within one click, the habit prior E that enters the policy
prior and the precision update is the normalised count of what has worked,
read from the slow state this click started from. Over a run, a click's E is
therefore the counts left by the previous click's outcome: a success of a
policy's class raises that policy's E at the next click, and a failure leaves
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

The counts in the sources are indexed by policy. `R15TemporalHierarchy` keeps
them by action class. The two grains coincide when each policy on the menu is
the only policy of its class, which `ClassMenu` requires (`classOf` is
injective). No cited publication says how to split one class's count among
several policies of that class, so a menu with two policies in one class is
outside this condition; `R20Graph` still declares no habit-row edge for it.

What is counted also differs, as `R15HabitPrior` says: Friston counts the
selected policy, R15 counts witnessed successes of a class. This module ties
E to R15's counts as they are and does not settle that difference.

Results, for a click that is certified and whose E is fed by its counts:

* `selection_E_is_habit`: selection's E port is the habit prior of the habit
  row's before-state, since precision reads that port;
* `fed_E_sums_to_one`: that E is a distribution over the two policies;
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
attribute [local instance] Classical.propDecidable

/-- The action class of each policy on the menu, one policy per class. -/
structure ClassMenu where
  classOf : Policy → Nat
  injective : Function.Injective classOf

/-- The menu's classes, in policy order. -/
def ClassMenu.classes (m : ClassMenu) : List Nat := [m.classOf .a, m.classOf .b]

theorem ClassMenu.nodup (m : ClassMenu) : m.classes.Nodup := by
  have ne : m.classOf .a ≠ m.classOf .b := fun h => by cases m.injective h
  simp [ClassMenu.classes, ne]

theorem ClassMenu.mem (m : ClassMenu) (π : Policy) : m.classOf π ∈ m.classes := by
  cases π <;> simp [ClassMenu.classes]

/-- The precision row's E is the habit prior of the slow state this click
started from, at each policy's class. -/
def HabitFeedsE (m : ClassMenu) (records : Records) : Prop :=
  ∀ h p, records .habit = some h → records .precision = some p →
    ∀ π, p.E π = (classHabitPrior h.before m.classes (m.classOf π) : ℝ)

/-- In a certified click fed by its counts, selection's E port, which
enters the policy prior, is the habit prior: precision reads that port. -/
theorem selection_E_is_habit {m : ClassMenu} {records : Records}
    {ports : R20Graph.Ports Policy} (certified : Certified records (certify records) ports)
    (fed : HabitFeedsE m records) {h : TwoTickRecord}
    {p : PrecisionFromObservation.TickRecord Policy}
    (hh : records .habit = some h) (hp : records .precision = some p) (π : Policy) :
    ports.selectionHabit.value π = (classHabitPrior h.before m.classes (m.classOf π) : ℝ) := by
  rcases certified with ⟨_, wired, reads⟩
  rw [← wired.habitRead, ← (reads.1 p hp).1]
  exact fed h p hh hp π

/-- A positive quotient of a nonnegative numerator has a positive numerator. -/
private theorem num_pos_of_div_pos {x y : ℚ} (hx : 0 ≤ x) (pos : 0 < x / y) : 0 < x := by
  rcases hx.lt_or_eq with lt | eq
  · exact lt
  · rw [← eq, zero_div] at pos
    exact absurd pos (lt_irrefl 0)

/-- A conforming precision row has positive E, so every class on the menu has
positive count and the fed E sums to one. -/
theorem fed_E_sums_to_one {m : ClassMenu} {records : Records} (fed : HabitFeedsE m records)
    {h : TwoTickRecord} {p : PrecisionFromObservation.TickRecord Policy}
    (hh : records .habit = some h) (hp : records .precision = some p)
    (conforms : PrecisionFromObservation.Conforms p) :
    ∑ π, p.E π = 1 := by
  have positive : PositiveAlphas h.before m.classes := by
    intro k hk
    have : ∃ π, m.classOf π = k := by
      simp only [ClassMenu.classes, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl
      · exact ⟨.a, rfl⟩
      · exact ⟨.b, rfl⟩
    obtain ⟨π, rfl⟩ := this
    have e := conforms.1 π
    rw [fed h p hh hp π] at e
    exact num_pos_of_div_pos (by simp [classAlpha]) (by exact_mod_cast e)
  have sum := classHabitPrior_sum_one (by simp [ClassMenu.classes]) positive
  rw [PrecisionFromObservation.sum_twoPolicy, fed h p hh hp, fed h p hh hp]
  simp only [ClassMenu.classes, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at sum
  exact_mod_cast sum

/-! ## Over a run -/

/-- Over a carried run whose clicks are fed by their counts, click `i + 1`'s E
is the habit prior of the counts after click `i`'s outcome. -/
theorem run_E_reads_previous_outcome {relation : Target → Target → TargetRelation}
    {c : ℕ → Click} {n : ℕ} (run : RunCertified relation c n) (m : ClassMenu)
    (fed : ∀ i ≤ n, HabitFeedsE m (c i).records)
    (hab : ℕ → TwoTickRecord) (hh : ∀ i ≤ n, (c i).records .habit = some (hab i))
    (pr : ℕ → PrecisionFromObservation.TickRecord Policy)
    (hp : ∀ i ≤ n, (c i).records .precision = some (pr i))
    {i : ℕ} (hi : i < n) (π : Policy) :
    (pr (i + 1)).E π =
      (classHabitPrior (advance (hab i).before (hab i).outcome) m.classes (m.classOf π) : ℝ) := by
  obtain ⟨r, hr, good⟩ := row_of_certified (run.1 i (by omega)).1 .habit
  rw [hh i (by omega)] at hr
  cases hr
  have carried := (run.2 i hi).habit _ _ (hh i (by omega)) (hh (i + 1) (by omega))
  rw [fed (i + 1) hi _ _ (hh (i + 1) (by omega)) (hp (i + 1) hi) π, carried, good.2.2, good.2.1]

/-- A witnessed success of policy `π`'s class at click `i` raises `π`'s E at
click `i + 1`, whenever the other class holds positive count. -/
theorem success_raises_next_E {relation : Target → Target → TargetRelation}
    {c : ℕ → Click} {n : ℕ} (run : RunCertified relation c n) (m : ClassMenu)
    (fed : ∀ i ≤ n, HabitFeedsE m (c i).records)
    (hab : ℕ → TwoTickRecord) (hh : ∀ i ≤ n, (c i).records .habit = some (hab i))
    (pr : ℕ → PrecisionFromObservation.TickRecord Policy)
    (hp : ∀ i ≤ n, (c i).records .precision = some (pr i))
    {i : ℕ} (hi : i < n) (π : Policy)
    (success : (hab i).outcome = ⟨m.classOf π, true, true⟩)
    (positiveTotal : 0 < totalAlpha (hab i).before m.classes)
    (outsideMass : classAlpha (hab i).before (m.classOf π) < totalAlpha (hab i).before m.classes) :
    (pr i).E π < (pr (i + 1)).E π := by
  rw [run_E_reads_previous_outcome run m fed hab hh pr hp hi π, success,
    fed i (by omega) _ _ (hh i (by omega)) (hp i (by omega)) π]
  exact_mod_cast success_strictly_increases_habit m.nodup (m.mem π) positiveTotal outsideMass

/-- A witnessed failure at click `i` leaves every policy's E at click `i + 1`
where it was. -/
theorem failure_keeps_next_E {relation : Target → Target → TargetRelation}
    {c : ℕ → Click} {n : ℕ} (run : RunCertified relation c n) (m : ClassMenu)
    (fed : ∀ i ≤ n, HabitFeedsE m (c i).records)
    (hab : ℕ → TwoTickRecord) (hh : ∀ i ≤ n, (c i).records .habit = some (hab i))
    (pr : ℕ → PrecisionFromObservation.TickRecord Policy)
    (hp : ∀ i ≤ n, (c i).records .precision = some (pr i))
    {i : ℕ} (hi : i < n) (k : Nat) (failure : (hab i).outcome = ⟨k, true, false⟩) (π : Policy) :
    (pr (i + 1)).E π = (pr i).E π := by
  rw [run_E_reads_previous_outcome run m fed hab hh pr hp hi π, failure,
    fed i (by omega) _ _ (hh i (by omega)) (hp i (by omega)) π,
    failure_leaves_habit_unchanged]

/-! ## Controls

One click with the habit row's before-state `countsA` (class 1 count 3,
class 2 count 2), so the counts give E = (3/5, 2/5). -/

def menu12 : ClassMenu :=
  ⟨fun | .a => 1 | .b => 2, by intro x y h; cases x <;> cases y <;> first | rfl | cases h⟩

def habitAt (before : SlowState) : TwoTickRecord :=
  let outcome : FastOutcome := ⟨1, true, true⟩
  ⟨before, outcome, advance before outcome, advance before outcome⟩

def precisionWithE (E : Policy → ℝ) : PrecisionFromObservation.TickRecord Policy :=
  ⟨E, fun _ => 0, fun _ => 0, fun _ => 1 / 2, fun _ => 1 / 2, 1, 1⟩

def clickRecords (E : Policy → ℝ) : Records :=
  rows (habitAt countsA) (evidenceAt (fun _ => 1 / 2) (fun _ => 1 / 2)) (precisionWithE E)
    ⟨7, tickAt 7 [7]⟩

def countedE : Policy → ℝ := fun | .a => 3 / 5 | .b => 2 / 5

theorem example_feeds : HabitFeedsE menu12 (clickRecords countedE) := by
  intro h p hh hp π
  simp only [clickRecords, rows] at hh hp
  cases hh; cases hp
  cases π <;>
    norm_num [precisionWithE, countedE, habitAt, menu12, ClassMenu.classes, classHabitPrior,
      totalAlpha, classAlpha, countsA, countsFor]

/-- E uniform although the counts give 3/5 and 2/5. -/
theorem uncountedE_refused : ¬ HabitFeedsE menu12 (clickRecords fun _ => 1 / 2) := by
  intro fed
  have := fed _ _ rfl rfl .a
  norm_num [precisionWithE, habitAt, menu12, ClassMenu.classes, classHabitPrior,
    totalAlpha, classAlpha, countsA, countsFor] at this

/-- E computed from the counts after this click's own success of class 1,
(4/6, 2/6): the click's outcome read into its own choice. -/
theorem postOutcomeE_refused :
    ¬ HabitFeedsE menu12 (clickRecords fun | .a => 2 / 3 | .b => 1 / 3) := by
  intro fed
  have := fed _ _ rfl rfl .a
  norm_num [precisionWithE, habitAt, menu12, ClassMenu.classes, classHabitPrior,
    totalAlpha, classAlpha, countsA, countsFor] at this

#print axioms selection_E_is_habit
#print axioms fed_E_sums_to_one
#print axioms success_raises_next_E
#print axioms failure_keeps_next_E
#print axioms example_feeds

end
end DarkTower.WarMachine.R20HabitPrior
