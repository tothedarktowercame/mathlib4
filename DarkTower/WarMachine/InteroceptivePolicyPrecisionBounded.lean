import Mathlib
import DarkTower.WarMachine.InteroceptivePolicyPrecisionProposal

/-!
# Bounded finite-policy refinement of the interoceptive proposal

The earlier affine counterexample allowed an arbitrary unbounded evidence
function.  Here the evidence term is treated at its actual finite-policy grain:
a difference of two expectations of the same finite `G` field.  We prove its
range bound and the conditional root-order theorem.  No claim is made that the
floating production solver establishes the continuity or uniqueness premises.
-/
namespace DarkTower.WarMachine.InteroceptivePolicyPrecisionBounded

open scoped BigOperators
open DarkTower.WarMachine.InteroceptivePolicyPrecisionProposal

variable {n : ℕ}

/-- A finite probability vector, stated without choosing a softmax formula. -/
structure FiniteWeights (n : ℕ) where
  weight : Fin n → ℝ
  nonnegative : ∀ i, 0 ≤ weight i
  normalised : ∑ i, weight i = 1

noncomputable def expectation (w : FiniteWeights n) (g : Fin n → ℝ) : ℝ :=
  ∑ i, w.weight i * g i

theorem expectation_le {w : FiniteWeights n} {g : Fin n → ℝ} {hi : ℝ}
    (hg : ∀ i, g i ≤ hi) : expectation w g ≤ hi := by
  calc
    expectation w g ≤ ∑ i, w.weight i * hi := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hg i) (w.nonnegative i)
    _ = hi := by rw [← Finset.sum_mul, w.normalised, one_mul]

theorem le_expectation {w : FiniteWeights n} {g : Fin n → ℝ} {lo : ℝ}
    (hg : ∀ i, lo ≤ g i) : lo ≤ expectation w g := by
  calc
    lo = ∑ i, w.weight i * lo := by rw [← Finset.sum_mul, w.normalised, one_mul]
    _ ≤ expectation w g := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hg i) (w.nonnegative i)

/-- Two policy distributions over the same bounded finite `G` field differ in
expected G by at most the field range.  Softmax weights qualify through their
separate nonnegativity and normalisation theorems. -/
theorem finitePolicyDeltaBound {p q : FiniteWeights n} {g : Fin n → ℝ}
    {lo hi : ℝ} (hlo : ∀ i, lo ≤ g i) (hhi : ∀ i, g i ≤ hi) :
    |expectation p g - expectation q g| ≤ hi - lo := by
  have pp_hi := expectation_le (w := p) hhi
  have qq_hi := expectation_le (w := q) hhi
  have lo_pp := le_expectation (w := p) hlo
  have lo_qq := le_expectation (w := q) hlo
  rw [abs_le]
  constructor <;> linarith

/-- With bounded continuous evidence, increasing the prior rate has a root
strictly above any baseline root.  If the new positive root is unique, it is
therefore the solver's only admissible branch and has strictly lower gamma.
Baseline-root uniqueness is not used. -/
theorem increasedRateLowersGammaAtUniquePositiveRoot
    {delta : ℝ → ℝ} {bound c1 c2 b1 : ℝ}
    (hcont : Continuous delta)
    (hbound : ∀ b, |delta b| ≤ bound)
    (hb1pos : 0 < b1)
    (hb1root : PosteriorRoot c1 delta b1)
    (hrates : c1 < c2)
    (hunique : ∀ ⦃x y : ℝ⦄,
      0 < x → PosteriorRoot c2 delta x →
      0 < y → PosteriorRoot c2 delta y → x = y) :
    ∃ b2, PosteriorRoot c2 delta b2 ∧ b1 < b2 ∧
      appliedGamma b2 < appliedGamma b1 := by
  let f : ℝ → ℝ := fun b => b - delta b
  let upper : ℝ := max (b1 + 1) (c2 + bound + 1)
  have hfcont : Continuous f := continuous_id.sub hcont
  have hb1f : f b1 = c1 := by
    dsimp [f]
    exact (eq_sub_iff_add_eq).2 hb1root
  have hub : bound < upper - c2 := by
    have hle : c2 + bound + 1 ≤ upper := le_max_right _ _
    linarith
  have hdeltaUpper : delta upper ≤ bound :=
    le_trans (le_abs_self (delta upper)) (hbound upper)
  have hfu : c2 < f upper := by
    dsimp [f]
    linarith
  have hb1u : b1 ≤ upper := by
    have : b1 + 1 ≤ upper := le_max_left _ _
    linarith
  have hc2mem : c2 ∈ Set.Icc (f b1) (f upper) := by
    constructor
    · rw [hb1f]
      exact hrates.le
    · exact hfu.le
  obtain ⟨b2, hb2mem, hb2f⟩ :=
    (intermediate_value_Icc hb1u hfcont.continuousOn) hc2mem
  have hb1b2le : b1 ≤ b2 := hb2mem.1
  have hb2root : PosteriorRoot c2 delta b2 := by
    dsimp [f] at hb2f
    exact (eq_sub_iff_add_eq).1 hb2f.symm
  have hb1b2 : b1 < b2 := by
    refine lt_of_le_of_ne hb1b2le ?_
    intro heq
    subst b2
    have : c1 = c2 := by
      rw [← hb1f, hb2f]
    exact (ne_of_lt hrates) this
  have hb2pos : 0 < b2 := lt_trans hb1pos hb1b2
  refine ⟨b2, hb2root, hb1b2, ?_⟩
  exact one_div_lt_one_div_of_lt hb1pos hb1b2

#print axioms finitePolicyDeltaBound
#print axioms increasedRateLowersGammaAtUniquePositiveRoot

end DarkTower.WarMachine.InteroceptivePolicyPrecisionBounded
