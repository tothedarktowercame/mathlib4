import DarkTower.WarMachine.PolicyPrecision
import DarkTower.WarMachine.OutcomeRiskKL

/-!
# Policy selection: γ-scaled posterior with infinite-risk exclusion, in one law

Approved design P7 (`p4ng/wm-walkthroughs/build-loop/closure/PROPOSAL-wm-model-design-2026-09-16.md`):
policy probability is `σ(log E − F − γG)` with `γ = 1/β`, and a policy whose risk
is infinite (it predicts, with positive mass, an outcome the preferences exclude)
has probability zero. `PolicyPrecision.precisionWeightedPosterior` states the first
for real `G`; `OutcomeRiskKL.policyPosterior` states the second at `γ = 1`. This
module states both as a single law over an extended `G`, which is what a runtime
must implement: a γ-scaled softmax over the candidates whose `G` is finite, with
every infinite-`G` candidate at probability zero.
-/

namespace DarkTower.WarMachine.PolicySelection

open DarkTower.WarMachine.PolicyPrecision DarkTower.WarMachine.OutcomeRiskKL

variable {ι : Type*} [Fintype ι]

/-- Unnormalised weight `E(π) · exp(−γ G(π) − F(π))` with `G` extended. -/
noncomputable def selectionWeight (t : PolicyTemperature) (habit F : ι → ℝ) (G : ι → EReal)
    (π : ι) : ENNReal :=
  ENNReal.ofReal (habit π) * EReal.exp (-((policyPrecision t : EReal) * G π) - (F π : EReal))

/-- Policy probability `σ(log E − F − γ G)` with `G` extended. -/
noncomputable def selectionPosterior (t : PolicyTemperature) (habit F : ι → ℝ) (G : ι → EReal)
    (π : ι) : ENNReal :=
  selectionWeight t habit F G π / ∑ π', selectionWeight t habit F G π'

/-- A policy with `G = ⊤` has weight zero at every positive precision. -/
theorem selectionWeight_top (t : PolicyTemperature) (habit F : ι → ℝ) (G : ι → EReal) (π : ι)
    (hG : G π = ⊤) : selectionWeight t habit F G π = 0 := by
  rw [selectionWeight, hG, EReal.coe_mul_top_of_pos (policyPrecision_pos t)]
  simp

/-- **Infinite risk excludes the policy, at every temperature.** -/
theorem selectionPosterior_eq_zero_of_risk_top {Obs : Holes.Vertex → Type*}
    (Q : Holes.PredictiveOutcomeKernel ι Obs) (C : Holes.PreferenceDistribution Obs)
    (t : PolicyTemperature) (habit F ambiguity : ι → ℝ) (π : ι)
    (hrisk : outcomeRisk Q C π = ⊤) :
    selectionPosterior t habit F (fun π => outcomeRisk Q C π + (ambiguity π : EReal)) π = 0 := by
  rw [selectionPosterior, selectionWeight_top _ _ _ _ _ (by simp [hrisk]), ENNReal.zero_div]

/-- On a finite candidate the weight is the real γ-scaled softmax weight. -/
theorem selectionWeight_coe (t : PolicyTemperature) (habit F : ι → ℝ) (hhabit : ∀ π, 0 < habit π)
    (G : ι → EReal) (g : ι → ℝ) (π : ι) (hg : G π = g π) :
    selectionWeight t habit F G π
      = ENNReal.ofReal (Real.exp (Real.log (habit π) - F π - policyPrecision t * g π)) := by
  rw [selectionWeight, hg, ← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_sub, EReal.exp_coe,
    ← ENNReal.ofReal_mul (hhabit π).le]
  congr 1
  rw [show Real.log (habit π) - F π - policyPrecision t * g π
      = Real.log (habit π) + (-(policyPrecision t * g π) - F π) by ring,
    Real.exp_add, Real.exp_log (hhabit π)]

/-- **The single law.** Let `fin` mark the candidates with finite `G = g`; every
other candidate has `G = ⊤`. Then each finite candidate's probability is its
γ-scaled softmax weight normalised over the finite candidates only, and every
infinite candidate has probability zero. -/
theorem selectionPosterior_finite (t : PolicyTemperature) (habit F : ι → ℝ)
    (hhabit : ∀ π, 0 < habit π) (fin : ι → Prop) [DecidablePred fin] (g : ι → ℝ) (π : ι)
    (hπ : fin π) :
    selectionPosterior t habit F (fun π => if fin π then (g π : EReal) else ⊤) π
      = ENNReal.ofReal (Real.exp (Real.log (habit π) - F π - policyPrecision t * g π)) /
          ∑ π' ∈ Finset.univ.filter fin,
            ENNReal.ofReal (Real.exp (Real.log (habit π') - F π' - policyPrecision t * g π')) := by
  have hw : ∀ π', selectionWeight t habit F (fun π => if fin π then (g π : EReal) else ⊤) π'
      = if fin π' then
          ENNReal.ofReal (Real.exp (Real.log (habit π') - F π' - policyPrecision t * g π'))
        else 0 := fun π' => by
    by_cases h : fin π'
    · rw [if_pos h, selectionWeight_coe t habit F hhabit _ g π' (by simp [h])]
    · rw [if_neg h, selectionWeight_top t habit F _ π' (by simp [h])]
  rw [selectionPosterior, hw π, if_pos hπ, Finset.sum_congr rfl fun π' _ => hw π',
    Finset.sum_ite, Finset.sum_const_zero, add_zero]

/-- With every candidate finite, the law is exactly the real precision-weighted
posterior of `PolicyPrecision`. -/
theorem selectionPosterior_all_finite [Nonempty ι] (t : PolicyTemperature) (habit F g : ι → ℝ)
    (hhabit : ∀ π, 0 < habit π) (π : ι) :
    selectionPosterior t habit F (fun π => (g π : EReal)) π
      = ENNReal.ofReal (precisionWeightedPosterior t habit g F hhabit π) := by
  have hw : ∀ π', selectionWeight t habit F (fun π => (g π : EReal)) π'
      = ENNReal.ofReal (Real.exp (Real.log (habit π') - F π' - policyPrecision t * g π')) :=
    fun π' => selectionWeight_coe t habit F hhabit _ g π' rfl
  rw [selectionPosterior, hw π, Finset.sum_congr rfl fun π' _ => hw π',
    ← ENNReal.ofReal_sum_of_nonneg (fun π' _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_div_of_pos (precisionWeighted_total_pos t habit g F hhabit)]
  rfl

end DarkTower.WarMachine.PolicySelection
