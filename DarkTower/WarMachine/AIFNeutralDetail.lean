import DarkTower.WarMachine.AIFJointObjectiveIdentity

/-!
# A fixed uniform detail modality adds one common constant

Parr 2022 describes modality-indexed preferences (`refs/parr2022.txt:13534-13560`)
and gives an example modality with nearly uniform preferences (`:6743-6747`).
Those passages do not mandate a product preference. Here `C × U_W` is an
explicit mathematical proposal: `C` is a normalized positive preference on
`Y`, and `U_W` is uniform on one fixed finite nonempty detail type.

Using the outcome-risk boundary established in `AIFJointObjectiveIdentity`, we
prove only an expected-negative-log-preference identity. No mutual-information
preservation, scoring equivalence, user preference, runtime, or R20 claim is
made. The joint prediction may correlate `Y` and `W` and may assign zero mass
to arbitrary pairs; the product preference is not renormalized per candidate.
-/

namespace DarkTower.WarMachine.AIFNeutralDetail

open scoped BigOperators
open DarkTower.WarMachine.Holes

noncomputable section

variable {Y W : Type*} [Fintype Y] [Fintype W] [Nonempty W]

def marginalY (q : ProbabilityKernel Unit (Y × W)) : ProbabilityKernel Unit Y :=
  CascadeEFE.finiteKernel (fun _ y => ∑ w, q.mass () (y, w))
    (by intros; exact Finset.sum_nonneg fun w _ => q.nonnegative () _)
    (by intro; rw [← Fintype.sum_prod_type]; exact CascadeEFE.kernel_sum q ())

def productPreference (C : ProbabilityKernel Unit Y) : ProbabilityKernel Unit (Y × W) :=
  CascadeEFE.finiteKernel
    (fun _ yw => C.mass () yw.1 / Fintype.card W)
    (by intros; exact div_nonneg (C.nonnegative () _) (by positivity))
    (by
      intro
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hc : (Fintype.card W : ℝ) ≠ 0 := by positivity
      simp_rw [← Finset.mul_sum]
      have hsum : ∑ y, C.mass () y = 1 := CascadeEFE.kernel_sum C ()
      rw [← Finset.sum_div, hsum]
      simp [div_eq_mul_inv, hc])

theorem productPreference_positive (C : ProbabilityKernel Unit Y)
    (positive : ∀ y, 0 < C.mass () y) (yw : Y × W) :
    0 < (productPreference C).mass () yw := by
  simp [productPreference]
  exact div_pos (positive _) (by exact_mod_cast Fintype.card_pos)

omit [Nonempty W] in theorem marginalY_mass (q : ProbabilityKernel Unit (Y × W)) (y : Y) :
    (marginalY q).mass () y = ∑ w, q.mass () (y, w) := rfl

private theorem pragmaticCost_eq_sum {X : Type*} [Fintype X]
    (q C : ProbabilityKernel Unit X) :
    CascadeEFE.pragmaticCost q C = -∑ x, q.mass () x * Real.log (C.mass () x) := by
  unfold CascadeEFE.pragmaticCost
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : q.mass () x = 0 <;> simp [h]

/-- The fixed uniform detail contributes exactly `log |W|`, without any
independence assumption on the joint prediction. -/
theorem neutral_detail_cost
    (q : ProbabilityKernel Unit (Y × W))
    (C : ProbabilityKernel Unit Y) (positive : ∀ y, 0 < C.mass () y) :
    CascadeEFE.pragmaticCost q (productPreference C) =
      CascadeEFE.pragmaticCost (marginalY q) C + Real.log (Fintype.card W) := by
  rw [pragmaticCost_eq_sum q (productPreference C), pragmaticCost_eq_sum (marginalY q) C]
  have hn : (Fintype.card W : ℝ) ≠ 0 := by positivity
  simp_rw [productPreference, CascadeEFE.finiteKernel, Real.log_div
    (ne_of_gt (positive _)) hn]
  rw [Fintype.sum_prod_type]
  simp_rw [mul_sub]
  have hmass : ∑ y, ∑ w, q.mass () (y, w) = 1 := by
    rw [← Fintype.sum_prod_type]
    exact CascadeEFE.kernel_sum q ()
  simp only [marginalY, CascadeEFE.finiteKernel]
  simp_rw [Finset.sum_sub_distrib]
  have hfirst : ∑ y, ∑ w, q.mass () (y, w) * Real.log (C.mass () y) =
      ∑ y, (∑ w, q.mass () (y, w)) * Real.log (C.mass () y) := by
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_mul]
  have hsecond : ∑ y, ∑ w, q.mass () (y, w) * Real.log (Fintype.card W) =
      Real.log (Fintype.card W) := by
    simp_rw [← Finset.sum_mul]
    rw [hmass, one_mul]
  rw [hfirst, hsecond]
  ring

/-- On the same detail domain, subtracting arbitrary separately supplied
information terms preserves pairwise order after the common constant is
removed. -/
theorem same_detail_order_iff
    (q₁ q₂ : ProbabilityKernel Unit (Y × W))
    (C : ProbabilityKernel Unit Y) (positive : ∀ y, 0 < C.mass () y)
    (information₁ information₂ : ℝ) :
    CascadeEFE.pragmaticCost q₁ (productPreference C) - information₁ ≤
        CascadeEFE.pragmaticCost q₂ (productPreference C) - information₂ ↔
      CascadeEFE.pragmaticCost (marginalY q₁) C - information₁ ≤
        CascadeEFE.pragmaticCost (marginalY q₂) C - information₂ := by
  rw [neutral_detail_cost q₁ C positive, neutral_detail_cost q₂ C positive]
  constructor <;> intro h <;> linarith

/-! Synthetic controls: a correlated joint with unreachable off-diagonal
pairs, and unequal detail cardinalities. -/

def uniformBool : ProbabilityKernel Unit Bool :=
  CascadeEFE.finiteKernel (fun _ _ => 1 / 2) (by intros; norm_num)
    (by intro; norm_num [Fintype.sum_bool])

def correlated : ProbabilityKernel Unit (Bool × Bool) :=
  CascadeEFE.finiteKernel (fun _ yw => if yw.1 = yw.2 then 1 / 2 else 0)
    (by intros; split_ifs <;> norm_num)
    (by intro; norm_num [Fintype.sum_prod_type, Fintype.sum_bool])

theorem correlated_has_unreachable_pairs :
    correlated.mass () (false, true) = 0 ∧ correlated.mass () (true, false) = 0 := by
  norm_num [correlated, CascadeEFE.finiteKernel]

theorem correlated_neutral_detail :
    CascadeEFE.pragmaticCost correlated (productPreference uniformBool) =
      CascadeEFE.pragmaticCost (marginalY correlated) uniformBool + Real.log 2 := by
  simpa using neutral_detail_cost correlated uniformBool
    (by intro; norm_num [uniformBool, CascadeEFE.finiteKernel])

theorem correlated_no_constant_false :
    CascadeEFE.pragmaticCost correlated (productPreference uniformBool) ≠
      CascadeEFE.pragmaticCost (marginalY correlated) uniformBool := by
  rw [correlated_neutral_detail]
  intro h
  have : Real.log 2 = 0 := by linarith
  exact (ne_of_gt (Real.log_pos (by norm_num))) this

def unitPreference : ProbabilityKernel Unit Unit := CascadeEFE.point ()
def unitJoint : ProbabilityKernel Unit (Unit × Unit) := CascadeEFE.point ((), ())
def boolDetailJoint : ProbabilityKernel Unit (Unit × Bool) := CascadeEFE.point ((), false)

theorem different_cardinalities_not_common :
    CascadeEFE.pragmaticCost unitJoint (productPreference unitPreference) = 0 ∧
    CascadeEFE.pragmaticCost boolDetailJoint (productPreference unitPreference) = Real.log 2 := by
  constructor
  · rw [neutral_detail_cost]
    · norm_num [marginalY, unitJoint, unitPreference, CascadeEFE.point,
        CascadeEFE.finiteKernel, CascadeEFE.pragmaticCost]
    · intro; norm_num [unitPreference, CascadeEFE.point, CascadeEFE.finiteKernel]
  · rw [neutral_detail_cost]
    · norm_num [marginalY, boolDetailJoint, unitPreference, CascadeEFE.point,
        CascadeEFE.finiteKernel, CascadeEFE.pragmaticCost]
    · intro; norm_num [unitPreference, CascadeEFE.point, CascadeEFE.finiteKernel]

#print axioms neutral_detail_cost
#print axioms same_detail_order_iff
#print axioms correlated_neutral_detail
#print axioms different_cardinalities_not_common

end
end DarkTower.WarMachine.AIFNeutralDetail
