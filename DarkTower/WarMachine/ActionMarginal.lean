import Mathlib

/-!
# Bayesian action selection (Da Costa et al. 2020, eq. 11)

`u_t = argmax_{u ∈ U} ∑_{π ∈ Π} δ(u, π_t) Q(π)`: the selected action is the
one with the greatest posterior mass summed over the policies that take it at
time t (a Bayesian model average over policies). Source: eq. (11),
`refs/dacosta2020.txt:685-697`. The policy-to-action projection
`step : Policy → U` (π ↦ π_t) and the posterior `Q` are named data of the
equation, supplied as arguments.
-/

namespace DarkTower.WarMachine.ActionMarginal

variable {Policy U : Type*} [Fintype Policy] [Fintype U] [DecidableEq U]
  (step : Policy → U) (Q : Policy → ℝ)

/-- Eq. (11) aggregation: posterior mass of `u` summed over the policies
taking action `u` at time `t`. -/
def actionMarginal (u : U) : ℝ :=
  ∑ π ∈ Finset.univ.filter (fun π => step π = u), Q π

/-- Eq. (11) argmax as a predicate; ties are allowed: any maximiser of the
action marginal satisfies eq. (11). -/
def IsBayesAction (u : U) : Prop :=
  ∀ u', actionMarginal step Q u' ≤ actionMarginal step Q u

variable {step Q}

/-- Action marginals are nonnegative for a nonnegative posterior. -/
theorem actionMarginal_nonneg (hQ : ∀ π, 0 ≤ Q π) (u : U) :
    0 ≤ actionMarginal step Q u :=
  Finset.sum_nonneg fun π _ => hQ π

/-- The action marginals of a posterior sum to one. -/
theorem actionMarginal_sum (hsum : ∑ π, Q π = 1) :
    ∑ u, actionMarginal step Q u = 1 := by
  have key : ∑ u, actionMarginal step Q u = ∑ π, Q π := by
    have expand : ∀ u, actionMarginal step Q u
        = ∑ π ∈ Finset.univ, (if step π = u then Q π else 0) := by
      intro u; rw [actionMarginal, Finset.sum_filter]
    simp only [expand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single (step y)]
    · simp
    · intro b _ hb
      exact if_neg fun h => hb h.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [key, hsum]

/-- A maximiser of the action marginal exists, so eq. (11) is satisfiable. -/
theorem exists_bayesAction [Nonempty U] :
    ∃ u, IsBayesAction step Q u := by
  obtain ⟨u, hu⟩ := Finite.exists_max (f := fun u => actionMarginal step Q u)
  exact ⟨u, fun u' => hu u'⟩

/-- With one policy per action (`step` injective), the individual-policy
argmax agrees with eq. (11) — the only condition under which it does. -/
theorem bayesAction_of_injective (hQ : ∀ π, 0 ≤ Q π)
    (hinj : Function.Injective step) (πstar : Policy)
    (hmax : ∀ π, Q π ≤ Q πstar) : IsBayesAction step Q (step πstar) := by
  intro u'
  have hself : Q πstar ≤ actionMarginal step Q (step πstar) := by
    rw [actionMarginal]
    exact Finset.single_le_sum (fun p _ => hQ p)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ πstar, rfl⟩)
  calc actionMarginal step Q u' ≤ Q πstar := by
        by_cases hu : ∃ π, step π = u'
        · obtain ⟨π, hπ⟩ := hu
          have hsub : Finset.univ.filter (fun p => step p = u') ⊆ {π} := by
            intro p hp
            have hp' := (Finset.mem_filter.mp hp).2
            simp only [Finset.mem_singleton]
            exact hinj (hp'.trans hπ.symm)
          have hzero : ∀ x ∈ ({π} : Finset Policy),
              x ∉ Finset.univ.filter (fun p => step p = u') → Q x = 0 := by
            intro x hx hx'
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ x,
              by rwa [Finset.mem_singleton.mp hx]⟩) hx'
          calc actionMarginal step Q u'
              = ∑ p ∈ Finset.univ.filter (fun p => step p = u'), Q p := rfl
            _ ≤ ∑ x ∈ ({π} : Finset Policy), Q x := (Finset.sum_subset hsub hzero).le
            _ = Q π := by simp
            _ ≤ Q πstar := hmax π
        · have hempty : (Finset.univ.filter (fun p => step p = u')) = ∅ :=
            Finset.filter_eq_empty_iff.mpr fun p _ hstep => hu ⟨p, hstep⟩
          rw [actionMarginal, hempty, Finset.sum_empty]
          exact hQ πstar
    _ ≤ actionMarginal step Q (step πstar) := hself

/-- A Bayes action's marginal mass dominates every single policy's
posterior. -/
theorem bayesAction_marginal_ge_policy (hQ : ∀ π, 0 ≤ Q π) (u : U)
    (h : IsBayesAction step Q u) (π : Policy) :
    Q π ≤ actionMarginal step Q u := by
  have hπ : Q π ≤ actionMarginal step Q (step π) := by
    rw [actionMarginal]
    exact Finset.single_le_sum (fun p _ => hQ p)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ π, rfl⟩)
  exact hπ.trans (h (step π))

/-! ## Audit A4 §4 fixture

Four policies with steps `[a, a, a, b]` (`a := true`, `b := false`) and
scores `[0, 0, 0, 1]`; the posterior is `Q ∝ exp score`, normalised
explicitly. Eq. (11) selects `a` (mass 3/(3+e) > e/(3+e)) while the
individual-policy argmax is policy 3, which takes `b`. -/

/-- The audit's step function: policies 0, 1, 2 take `a` (true); policy 3
takes `b` (false). -/
def fixtureStep : Fin 4 → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | _ => false

/-- The audit's scores: `[0, 0, 0, 1]`. -/
def fixtureScore : Fin 4 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | _ => 1

/-- The normalised posterior `Q(π) = exp (score π) / (3 + exp 1)`. -/
noncomputable def fixtureQ (π : Fin 4) : ℝ :=
  Real.exp (fixtureScore π) / (3 + Real.exp 1)

theorem fixtureQ_nonneg (π : Fin 4) : 0 ≤ fixtureQ π := by
  unfold fixtureQ
  exact div_nonneg (Real.exp_nonneg _) (by positivity)

theorem fixtureQ_sum : ∑ π, fixtureQ π = 1 := by
  rw [Fin.sum_univ_four]
  simp only [fixtureQ, fixtureScore, Real.exp_zero]
  try norm_num
  try field_simp
  try ring

theorem fixtureMarginal_a :
    actionMarginal fixtureStep fixtureQ true = 3 / (3 + Real.exp 1) := by
  have hd : (0:ℝ) < 3 + Real.exp 1 := by positivity
  rw [actionMarginal, Finset.sum_filter, Fin.sum_univ_four]
  simp only [fixtureStep, fixtureQ, fixtureScore, Real.exp_zero, if_true]
  try norm_num
  try field_simp
  try ring

theorem fixtureMarginal_b :
    actionMarginal fixtureStep fixtureQ false = Real.exp 1 / (3 + Real.exp 1) := by
  have hd : (0:ℝ) < 3 + Real.exp 1 := by positivity
  rw [actionMarginal, Finset.sum_filter, Fin.sum_univ_four]
  simp only [fixtureStep, fixtureQ, fixtureScore, Real.exp_zero, if_true]
  try norm_num
  try field_simp
  try ring

/-- Eq. (11) selects `a` for the audit fixture. -/
theorem fixture_bayes_a : IsBayesAction fixtureStep fixtureQ true := by
  intro u'
  cases u' with
  | true => exact le_refl _
  | false =>
      rw [fixtureMarginal_a, fixtureMarginal_b]
      exact (div_le_div_iff_of_pos_right (by positivity)).mpr Real.exp_one_lt_three.le

/-- Eq. (11) does not select `b` for the audit fixture. -/
theorem fixture_not_bayes_b : ¬ IsBayesAction fixtureStep fixtureQ false := by
  intro h
  have h3 : (3:ℝ) ≤ Real.exp 1 := by
    have := h true
    rw [fixtureMarginal_a, fixtureMarginal_b] at this
    exact (div_le_div_iff_of_pos_right (by positivity)).mp this
  linarith [Real.exp_one_lt_three]

/-- Policy 3 is the individual-policy argmax of the fixture posterior. -/
theorem fixture_policy3_is_individual_argmax :
    ∀ π, fixtureQ π ≤ fixtureQ 3 := by
  intro π
  have hs : fixtureScore π ≤ fixtureScore 3 := by
    fin_cases π
    all_goals first
      | show (0:ℝ) ≤ 1; norm_num
      | show (1:ℝ) ≤ 1; norm_num
  unfold fixtureQ
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr (Real.exp_le_exp.mpr hs)

/-- Strictly: every policy other than 3 has strictly smaller posterior. -/
theorem fixture_policy3_strict (π : Fin 4) (hπ : π ≠ 3) :
    fixtureQ π < fixtureQ 3 := by
  have hs : fixtureScore π < fixtureScore 3 := by
    fin_cases π
    · show (0:ℝ) < 1; norm_num
    · show (0:ℝ) < 1; norm_num
    · show (0:ℝ) < 1; norm_num
    · exact absurd rfl hπ
  unfold fixtureQ
  exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (Real.exp_lt_exp.mpr hs)

end DarkTower.WarMachine.ActionMarginal
