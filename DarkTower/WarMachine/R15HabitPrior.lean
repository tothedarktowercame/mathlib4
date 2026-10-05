import DarkTower.WarMachine.R15TemporalHierarchy
import DarkTower.WarMachine.Proof2.EnactmentHabit
import Mathlib.Tactic

/-!
# R15 witnessed outcomes as a habit prior

R15 says that witnessed tactical outcomes update the next strategic
calibration state, while “no quantity does duty at two levels at once.” Parr
et al. (2022), B.7 gives `π₀ = σ(ln E − G)`, with E a fixed policy belief or
habit term. The same text says high-level states form empirical priors E that
influence policy selection independently of expected free energy (lines
4854–4863), and that successful goal-directed policies can be cached as prior
policy values (lines 10724–10740). Friston et al. (2016) treats habits as
Dirichlet concentration counts.

The system already states that theory at policy grain. Registry row
`:enactment-habit` defines E at R17 as `(n(π)+1)/Σ(n(π')+1)`, and
`Proof2.EnactmentHabit.habitPrior` proves that distribution from distinct,
W_c-verified enactment records. This module uses the same normalized-count
formula at action-class grain: runtime slow-state alpha starts at one and each
witnessed success increments it once. The carriers deliberately differ:
verified policy enactments keyed by cascade policy versus witnessed successful
fast outcomes keyed by action class. No artificial isomorphism identifies
those records.

At Futon2 commit `0f9587532031beb50a21091cc41cd10f4a16ff63`,
`policy.clj/softmax-weights` lines 123–143 is the single declared habit seam:
`ln E` enters unscaled by τ, and its docstring says not to add a second prior
site. `temporal_hierarchy.clj/apply-slow-prior` lines 111–163 is exactly such a
second site: it multiplies a move prior by w and also puts `-ln w` inside the
cost later divided by τ. It is not on the production tick path: source search
finds it called only from `machine_slow_prior_evidence.clj` and the otherwise
uncalled `hierarchical-rollout`; `advance-slow-state` is called only from
`machine_slow_feedback_evidence.clj`. This module states the disagreement; it
does not soften or repair it.

Beta failures change beta but not alpha. Consequently they do not change this
habit prior. This distinguishes the habit count from a Beta posterior mean
`alpha/(alpha+beta)`, and matches the cited theory's successful-policy count.
-/

namespace DarkTower.WarMachine.R15HabitPrior

open DarkTower.WarMachine.R15TemporalHierarchy

/-- Runtime slow-state alpha for one action class. -/
def classAlpha (state : SlowState) (actionClass : Nat) : ℚ :=
  (countsFor state actionClass).alpha

/-- Sum of alpha over the finite declared class menu. -/
def totalAlpha (state : SlowState) (classes : List Nat) : ℚ :=
  (classes.map (classAlpha state)).sum

/-- R15's class-grain habit E. Callers establish a nonempty, duplicate-free
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

/-- Theory/runtime policy seam: `E * exp(-G/τ)`, with E unscaled by τ. -/
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

/-! ## Mode collapse is not the habit distribution -/

def modeStateA : SlowState := [(1, ⟨3, 1⟩), (2, ⟨2, 1⟩)]
def modeStateB : SlowState := [(1, ⟨3, 1⟩), (2, ⟨1, 1⟩)]
def twoClasses : List Nat := [1, 2]

/-- Both states have class 1 as their greatest-alpha class. -/
theorem mode_states_same_greatest_alpha :
    classAlpha modeStateA 2 < classAlpha modeStateA 1 ∧
    classAlpha modeStateB 2 < classAlpha modeStateB 1 := by
  norm_num [classAlpha, modeStateA, modeStateB, countsFor]

/-- Yet their normalized class habits differ, so one mode-table row cannot be
the class habit distribution. The runtime regex/table is intentionally not
transcribed here. -/
theorem mode_states_have_different_habits :
    classHabitPrior modeStateA twoClasses 2 ≠ classHabitPrior modeStateB twoClasses 2 := by
  norm_num [classHabitPrior, totalAlpha, classAlpha, modeStateA, modeStateB,
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
  { slowState := modeStateA, classes := twoClasses
    reportedMass := classHabitPrior modeStateA twoClasses
    temperature := 2
    candidates := [⟨1, 0, theoryWeight (3 / 5) 0 2⟩,
                   ⟨2, 0, theoryWeight (2 / 5) 0 2⟩] }

theorem goodHabitTick_conforms : HabitTickConforms goodHabitTick := by
  refine ⟨by decide, by decide, ?_, by norm_num [goodHabitTick], ?_, ?_⟩
  · intro actionClass member
    simp [goodHabitTick, twoClasses] at member ⊢
    rcases member with rfl | rfl <;>
      norm_num [classAlpha, modeStateA, countsFor]
  · intro actionClass _member
    rfl
  · intro candidate member
    simp [goodHabitTick] at member ⊢
    rcases member with rfl | rfl <;>
      norm_num [classHabitPrior, totalAlpha, classAlpha, modeStateA, twoClasses, countsFor]

/-- Control: substituting the exploitation mode row 0.7/0.2 for the count
distribution 3/5,2/5 fails mass conformance. -/
noncomputable def modeTableMassTick : HabitTickRecord :=
  { goodHabitTick with reportedMass := fun c => if c = 1 then 7 / 10 else 2 / 10 }

theorem modeTableMassTick_rejected : ¬ HabitTickConforms modeTableMassTick := by
  intro conforms
  have mass := conforms.2.2.2.2.1 1 (by simp [modeTableMassTick, goodHabitTick, twoClasses])
  norm_num [modeTableMassTick, goodHabitTick, classHabitPrior, totalAlpha,
    classAlpha, modeStateA, twoClasses, countsFor] at mass

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
    classAlpha, modeStateA, twoClasses, countsFor] at weight
  rw [← Real.exp_log positive] at weight
  have logThreeFifthsNeg : Real.log ((3 : ℝ) / 5) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have expInject := Real.exp_injective weight
  rw [Real.log_exp] at expInject
  nlinarith

end DarkTower.WarMachine.R15HabitPrior
