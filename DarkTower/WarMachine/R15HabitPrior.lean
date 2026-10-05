import DarkTower.WarMachine.R15TemporalHierarchy
import DarkTower.WarMachine.Proof2.EnactmentHabit
import Mathlib.Tactic

/-!
# What has worked becomes a prior on what to do next

In plain terms: the counts of what worked, normalised, are a prior over the
classes of action. Each witnessed success shifts that prior a little toward
its own class and away from the others; a failure does not move it. The prior
enters the choice of policy once, beside the expected free energy, and the
commitment temperature does not turn it up or down.

Sources. Parr, Pezzulo and Friston (2022), B.7: `π₀ = σ(ln E − G)`, where "E is
a vector of fixed beliefs about policies (this may be thought of as a bias, or
habit, term)"; p. 94: high-level states "form empirical priors (E) that
influence policy selection independently of the expected free energy"; p. 209:
habits are acquired by "caching information about which policies are
successful in which contexts". Friston et al. (2016) learn E as Dirichlet
concentration counts.

The model already states this at the grain of policies: the equation registry's
`:enactment-habit` row defines `E(π) = (n(π)+1)/Σ(n(π')+1)` over verified
enactments, and `Proof2.EnactmentHabit.habitPrior` proves it is a distribution.
`classHabitPrior` here is the same normalised count at the grain of action
classes, over the counts of `R15TemporalHierarchy`. The two are not identified
by a theorem: one counts verified enactments of a policy, the other witnessed
successes of a class.

Placement. `theoryWeight` is `E · exp(−G/τ)`. `equal_score_weight_ratio` says
that with equal G the ratio of two candidates is the ratio of their habit
masses at every temperature. `costSitedWeight` is the alternative of putting
`−ln E` inside the tempered score; it agrees at `τ = 1` and not otherwise
(`cost_siting_tempers_habit`), so under it the commitment temperature would
change how much the habit counts. In futon2 `src/futon2/aif/policy.clj`, which
the rebuilt decision code requires, `softmax-weights` takes `ln E` unscaled by
τ and its docstring says not to add a second prior site (read at `0f9587532`).

The failure count does not enter `classHabitPrior`. That distinguishes it from
a posterior mean `successes/(successes+failures)` and matches the sources,
which speak of what was successful.

Whether the rebuilt decision code passes any habit prior into that seam was
not read for this module. Code that does must satisfy `HabitTickConforms`.
-/

namespace DarkTower.WarMachine.R15HabitPrior

open DarkTower.WarMachine.R15TemporalHierarchy

/-- The success count of one action class. -/
def classAlpha (state : SlowState) (actionClass : Nat) : ℚ :=
  (countsFor state actionClass).alpha

/-- Sum of alpha over the finite declared class menu. -/
def totalAlpha (state : SlowState) (classes : List Nat) : ℚ :=
  (classes.map (classAlpha state)).sum

/-- The class-grain habit prior E. Callers establish a nonempty, duplicate-free
menu and positive alpha entries; the definition remains total. -/
def classHabitPrior (state : SlowState) (classes : List Nat) (actionClass : Nat) : ℚ :=
  classAlpha state actionClass / totalAlpha state classes

def PositiveAlphas (state : SlowState) (classes : List Nat) : Prop :=
  ∀ actionClass ∈ classes, 0 < classAlpha state actionClass

theorem totalAlpha_pos {state : SlowState} {classes : List Nat}
    (nonempty : classes ≠ []) (positive : PositiveAlphas state classes) :
    0 < totalAlpha state classes := by
  unfold totalAlpha
  apply List.sum_pos
  · intro value member
    obtain ⟨actionClass, inClasses, rfl⟩ := List.mem_map.mp member
    exact positive actionClass inClasses
  · simpa using nonempty

theorem classHabitPrior_pos {state : SlowState} {classes : List Nat}
    (nonempty : classes ≠ []) (positive : PositiveAlphas state classes)
    {actionClass : Nat} (member : actionClass ∈ classes) :
    0 < classHabitPrior state classes actionClass :=
  div_pos (positive actionClass member) (totalAlpha_pos nonempty positive)

/-- The normalized class habit sums to one over a duplicate-free menu. -/
theorem classHabitPrior_sum_one {state : SlowState} {classes : List Nat}
    (nonempty : classes ≠ []) (positive : PositiveAlphas state classes) :
    (classes.map (classHabitPrior state classes)).sum = 1 := by
  unfold classHabitPrior totalAlpha
  have distribute (entries : List Nat) :
      (entries.map (fun actionClass => classAlpha state actionClass /
        (classes.map (classAlpha state)).sum)).sum =
      (entries.map (classAlpha state)).sum /
        (classes.map (classAlpha state)).sum := by
    induction entries with
    | nil => simp
    | cons head tail ih => simp [ih, add_div]
  rw [distribute]
  exact div_self (totalAlpha_pos nonempty positive).ne'

theorem success_alpha_same (state : SlowState) (actionClass : Nat) :
    classAlpha (advance state ⟨actionClass, true, true⟩) actionClass =
      classAlpha state actionClass + 1 := by
  simp [classAlpha, advance, updatedCounts, countsFor_setCounts_same]

theorem success_alpha_other (state : SlowState) (actionClass other : Nat)
    (different : other ≠ actionClass) :
    classAlpha (advance state ⟨actionClass, true, true⟩) other = classAlpha state other := by
  simp [classAlpha, advance,
    countsFor_setCounts_other state actionClass other _ different]

theorem failure_alpha_unchanged (state : SlowState) (actionClass other : Nat) :
    classAlpha (advance state ⟨actionClass, true, false⟩) other = classAlpha state other := by
  by_cases same : other = actionClass
  · subst other
    simp [classAlpha, advance, updatedCounts, countsFor_setCounts_same]
  · simp [classAlpha, advance,
      countsFor_setCounts_other state actionClass other _ same]

theorem totalAlpha_success {state : SlowState} {classes : List Nat} {actionClass : Nat}
    (nodup : classes.Nodup) (member : actionClass ∈ classes) :
    totalAlpha (advance state ⟨actionClass, true, true⟩) classes =
      totalAlpha state classes + 1 := by
  induction classes with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.nodup_cons] at nodup
      simp only [List.mem_cons] at member
      unfold totalAlpha
      simp only [List.map_cons, List.sum_cons]
      rcases member with rfl | member
      · rw [success_alpha_same]
        have tailUnchanged :
            (tail.map (classAlpha (advance state ⟨actionClass, true, true⟩))).sum =
              (tail.map (classAlpha state)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro other inTail
          exact success_alpha_other state actionClass other (by
            intro eq; subst other; exact nodup.1 inTail)
        rw [tailUnchanged]
        ring
      · rw [success_alpha_other state actionClass head (by
          intro eq; subst head; exact nodup.1 member)]
        have recurse := ih nodup.2 member
        unfold totalAlpha at recurse
        rw [recurse]
        ring

theorem totalAlpha_failure (state : SlowState) (classes : List Nat) (actionClass : Nat) :
    totalAlpha (advance state ⟨actionClass, true, false⟩) classes =
      totalAlpha state classes := by
  unfold totalAlpha
  apply congrArg List.sum
  apply List.map_congr_left
  intro other _member
  exact failure_alpha_unchanged state actionClass other

/-- A success raises its class habit whenever the menu contains positive habit
mass outside that class. A singleton menu is necessarily unchanged at mass 1,
so `alpha < totalAlpha` is the exact necessary side condition. -/
theorem success_strictly_increases_habit {state : SlowState} {classes : List Nat}
    {actionClass : Nat} (nodup : classes.Nodup) (member : actionClass ∈ classes)
    (positiveTotal : 0 < totalAlpha state classes)
    (outsideMass : classAlpha state actionClass < totalAlpha state classes) :
    classHabitPrior state classes actionClass <
      classHabitPrior (advance state ⟨actionClass, true, true⟩) classes actionClass := by
  rw [classHabitPrior, classHabitPrior, success_alpha_same,
    totalAlpha_success nodup member]
  apply (div_lt_div_iff₀ positiveTotal (by linarith)).2
  nlinarith

/-- The same success lowers every other listed class's habit mass. -/
theorem success_strictly_decreases_other {state : SlowState} {classes : List Nat}
    {actionClass other : Nat} (nodup : classes.Nodup) (member : actionClass ∈ classes)
    (different : other ≠ actionClass) (positiveOther : 0 < classAlpha state other)
    (positiveTotal : 0 < totalAlpha state classes) :
    classHabitPrior (advance state ⟨actionClass, true, true⟩) classes other <
      classHabitPrior state classes other := by
  rw [classHabitPrior, classHabitPrior, success_alpha_other state actionClass other different,
    totalAlpha_success nodup member]
  apply (div_lt_div_iff₀ (by linarith) positiveTotal).2
  nlinarith

/-- A witnessed failure changes no class habit mass. -/
theorem failure_leaves_habit_unchanged (state : SlowState) (classes : List Nat)
    (actionClass other : Nat) :
    classHabitPrior (advance state ⟨actionClass, true, false⟩) classes other =
      classHabitPrior state classes other := by
  simp [classHabitPrior, failure_alpha_unchanged, totalAlpha_failure]

/-! ## Correct and cost-sited placement -/

/-- The policy weight `E * exp(-G/τ)`, with E unscaled by τ. -/
noncomputable def theoryWeight (habit score temperature : ℝ) : ℝ :=
  habit * Real.exp (-score / temperature)

/-- The one-step effect of putting `-ln w` inside the tempered cost. -/
noncomputable def costSitedWeight (habit score temperature : ℝ) : ℝ :=
  Real.exp (-(score - Real.log habit) / temperature)

/-- With equal G, the weight ratio is exactly the habit ratio at every
positive τ; temperature does not temper E. -/
theorem equal_score_weight_ratio {firstHabit secondHabit score temperature : ℝ}
    (secondPositive : 0 < secondHabit) :
    theoryWeight firstHabit score temperature /
      theoryWeight secondHabit score temperature = firstHabit / secondHabit := by
  unfold theoryWeight
  have expNonzero : Real.exp (-score / temperature) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- Uniform habit leaves ordering entirely to `-G/τ`. -/
theorem uniform_habit_order {habit firstScore secondScore temperature : ℝ}
    (habitPositive : 0 < habit) (temperaturePositive : 0 < temperature) :
    theoryWeight habit firstScore temperature > theoryWeight habit secondScore temperature ↔
      firstScore < secondScore := by
  simp only [theoryWeight]
  constructor
  · intro h
    have exponentOrder :
        Real.exp (-secondScore / temperature) < Real.exp (-firstScore / temperature) := by
      nlinarith [Real.exp_pos (-firstScore / temperature),
        Real.exp_pos (-secondScore / temperature)]
    rw [Real.exp_lt_exp] at exponentOrder
    have := (div_lt_div_iff_of_pos_right temperaturePositive).mp exponentOrder
    linarith
  · intro h
    have exponentOrder :
        Real.exp (-secondScore / temperature) < Real.exp (-firstScore / temperature) := by
      rw [Real.exp_lt_exp]
      apply (div_lt_div_iff_of_pos_right temperaturePositive).2
      linarith
    nlinarith [Real.exp_pos (-firstScore / temperature),
      Real.exp_pos (-secondScore / temperature)]

/-- At τ=1, cost siting happens to equal the theory's unscaled habit weight. -/
theorem cost_siting_agrees_at_one {habit score : ℝ} (habitPositive : 0 < habit) :
    costSitedWeight habit score 1 = theoryWeight habit score 1 := by
  simp [costSitedWeight, theoryWeight, Real.exp_sub, Real.exp_log habitPositive,
    Real.exp_neg, div_eq_mul_inv]

/-- At τ=2 the disagreement is explicit: with equal zero G and habits
`exp(-2)` and 1, cost siting yields ratio `exp(-1)`, while theory yields
`exp(-2)`. -/
theorem cost_siting_tempers_habit :
    costSitedWeight (Real.exp (-2)) 0 2 / costSitedWeight 1 0 2 = Real.exp (-1) ∧
    theoryWeight (Real.exp (-2)) 0 2 / theoryWeight 1 0 2 = Real.exp (-2) ∧
    Real.exp (-1) ≠ Real.exp (-2) := by
  constructor
  · simp [costSitedWeight, Real.log_exp]
  · constructor
    · simp [theoryWeight]
    · intro equal
      have := Real.exp_injective equal
      norm_num at this

/-! ## The leading class alone does not determine the prior -/

def countsA : SlowState := [(1, ⟨3, 1⟩), (2, ⟨2, 1⟩)]
def countsB : SlowState := [(1, ⟨3, 1⟩), (2, ⟨1, 1⟩)]
def twoClasses : List Nat := [1, 2]

/-- Both states have class 1 as their greatest-alpha class. -/
theorem states_share_leading_class :
    classAlpha countsA 2 < classAlpha countsA 1 ∧
    classAlpha countsB 2 < classAlpha countsB 1 := by
  norm_num [classAlpha, countsA, countsB, countsFor]

/-- Yet their normalised class habits differ, so no rule that reads only which
class leads can reproduce the prior. -/
theorem states_with_same_leader_differ_in_prior :
    classHabitPrior countsA twoClasses 2 ≠ classHabitPrior countsB twoClasses 2 := by
  norm_num [classHabitPrior, totalAlpha, classAlpha, countsA, countsB,
    twoClasses, countsFor]

/-! ## Retained-record conformance -/

structure HabitCandidate where
  actionClass : Nat
  score : ℝ
  reportedWeight : ℝ

structure HabitTickRecord where
  slowState : SlowState
  classes : List Nat
  reportedMass : Nat → ℚ
  temperature : ℝ
  candidates : List HabitCandidate

def HabitTickConforms (record : HabitTickRecord) : Prop :=
  record.classes ≠ [] ∧ record.classes.Nodup ∧
  PositiveAlphas record.slowState record.classes ∧ 0 < record.temperature ∧
  (∀ actionClass ∈ record.classes,
    record.reportedMass actionClass =
      classHabitPrior record.slowState record.classes actionClass) ∧
  (∀ candidate ∈ record.candidates,
    candidate.reportedWeight = theoryWeight
      (record.reportedMass candidate.actionClass) candidate.score record.temperature)

noncomputable def goodHabitTick : HabitTickRecord :=
  { slowState := countsA, classes := twoClasses
    reportedMass := classHabitPrior countsA twoClasses
    temperature := 2
    candidates := [⟨1, 0, theoryWeight (3 / 5) 0 2⟩,
                   ⟨2, 0, theoryWeight (2 / 5) 0 2⟩] }

theorem goodHabitTick_conforms : HabitTickConforms goodHabitTick := by
  refine ⟨by decide, by decide, ?_, by norm_num [goodHabitTick], ?_, ?_⟩
  · intro actionClass member
    simp [goodHabitTick, twoClasses] at member ⊢
    rcases member with rfl | rfl <;>
      norm_num [classAlpha, countsA, countsFor]
  · intro actionClass _member
    rfl
  · intro candidate member
    simp [goodHabitTick] at member ⊢
    rcases member with rfl | rfl <;>
      norm_num [classHabitPrior, totalAlpha, classAlpha, countsA, twoClasses, countsFor]

/-- Control: masses 7/10 and 2/10 that were not computed from the counts
(which give 3/5 and 2/5) fail mass conformance. -/
noncomputable def uncountedMassTick : HabitTickRecord :=
  { goodHabitTick with reportedMass := fun c => if c = 1 then 7 / 10 else 2 / 10 }

theorem uncountedMassTick_rejected : ¬ HabitTickConforms uncountedMassTick := by
  intro conforms
  have mass := conforms.2.2.2.2.1 1 (by simp [uncountedMassTick, goodHabitTick, twoClasses])
  norm_num [uncountedMassTick, goodHabitTick, classHabitPrior, totalAlpha,
    classAlpha, countsA, twoClasses, countsFor] at mass

/-- Control: even with correct masses, reporting the τ=2 cost-sited weight for
class 1 violates the untempered theory placement. -/
noncomputable def costSitedHabitTick : HabitTickRecord :=
  { goodHabitTick with candidates :=
      [⟨1, 0, costSitedWeight (3 / 5) 0 2⟩] }

theorem costSitedHabitTick_rejected : ¬ HabitTickConforms costSitedHabitTick := by
  intro conforms
  have weight := conforms.2.2.2.2.2
    (⟨1, 0, costSitedWeight (3 / 5) 0 2⟩ : HabitCandidate)
    (by simp [costSitedHabitTick])
  simp [costSitedHabitTick, goodHabitTick] at weight
  have positive : (0 : ℝ) < 3 / 5 := by norm_num
  norm_num [costSitedWeight, theoryWeight, classHabitPrior, totalAlpha,
    classAlpha, countsA, twoClasses, countsFor] at weight
  rw [← Real.exp_log positive] at weight
  have logThreeFifthsNeg : Real.log ((3 : ℝ) / 5) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have expInject := Real.exp_injective weight
  rw [Real.log_exp] at expInject
  nlinarith

end DarkTower.WarMachine.R15HabitPrior
