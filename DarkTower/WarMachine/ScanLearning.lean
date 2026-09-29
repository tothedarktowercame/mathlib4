import DarkTower.WarMachine.Holes

/-!
# Integrated predictive for the learned scan observation model

This module states the pure mathematics used by
`futon2.aif.scan-learn/log-predictive` and
`futon2.aif.scan-learn/status-log-likelihoods`.  The frozen
`Holes.logMultivariateBeta` uses a positive, nonempty `List ℝ`; `parameters`
below is the minimal bridge from a finite indexed family to that carrier.
-/

namespace DarkTower.WarMachine.ScanLearning

open scoped BigOperators
open DarkTower.WarMachine.Holes

noncomputable section

variable {O K S : Type*}

/-- `scan_learn.clj:154-156`, `log-multinomial-coefficient`: the logarithm
of the multinomial coefficient for a finite outcome-indexed count vector. -/
def logMultinomialCoefficient [Fintype O] (n : O → ℕ) : ℝ :=
  Real.log (Nat.factorial (∑ o, n o)) - ∑ o, Real.log (Nat.factorial (n o))

/-- Minimal bridge to the list carrier of `Holes.logMultivariateBeta`
(`scan_learn.clj:158-169`, the Binomial/Multinomial arms). -/
def parameters [Fintype O] [Nonempty O] (alpha : O → ℝ) (hα : ∀ o, 0 < alpha o) :
    DirichletConcentrations :=
  ⟨Finset.univ.toList.map alpha,
    by
      classical
      apply List.ne_nil_of_length_pos
      simp [Fintype.card_pos],
    by
      intro x hx
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hα _⟩

/-- `scan_learn.clj:158-169`, `log-predictive`: integrated
Dirichlet-multinomial log predictive, reusing `Holes.logMultivariateBeta`. -/
def dirichletMultinomialLogPredictive [Fintype O] [Nonempty O]
    (alpha : O → ℝ) (hα : ∀ o, 0 < alpha o) (n : O → ℕ) : ℝ :=
  logMultinomialCoefficient n +
    logMultivariateBeta (parameters (fun o => alpha o + n o)
      (fun o => add_pos_of_pos_of_nonneg (hα o) (Nat.cast_nonneg _))) -
    logMultivariateBeta (parameters alpha hα)

/-- A one-hot count, used by the categorical arm at `scan_learn.clj:170-173`. -/
def oneHot [DecidableEq O] (observed : O) : O → ℕ :=
  fun o => if o = observed then 1 else 0

/-- `scan_learn.clj:170-173`: a one-hot Dirichlet-multinomial predictive is
the categorical posterior predictive `log (alpha[o] / sum alpha)`. -/
theorem dirichletCategoricalLogPredictive_eq [Fintype O] [Nonempty O] [DecidableEq O]
    (alpha : O → ℝ) (hα : ∀ o, 0 < alpha o) (observed : O) :
    dirichletMultinomialLogPredictive alpha hα (oneHot observed) =
      Real.log (alpha observed / ∑ o, alpha o) := by
  have ha0 : alpha observed ≠ 0 := ne_of_gt (hα observed)
  have hsumpos : 0 < ∑ o, alpha o :=
    Finset.sum_pos (fun o _ => hα o) Finset.univ_nonempty
  have hsum0 : (∑ o, alpha o) ≠ 0 := ne_of_gt hsumpos
  have hcoeff : (∑ x, Real.log ((if x = observed then 1 else 0 : ℕ).factorial)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    split <;> simp
  have hsum : (∑ o, (alpha o + (if o = observed then (1 : ℝ) else 0))) =
      (∑ o, alpha o) + 1 := by
    simp [Finset.sum_add_distrib]
  have hgamma :
      (∑ o, Real.log (Real.Gamma (alpha o + (if o = observed then (1 : ℝ) else 0)))) =
        Real.log (Real.Gamma (alpha observed + 1)) +
          ∑ o ∈ Finset.univ.erase observed, Real.log (Real.Gamma (alpha o)) := by
    rw [Finset.sum_eq_add_sum_diff_singleton observed]
    · congr 1
      · simp
      simp only [Finset.erase_eq]
      apply Finset.sum_congr rfl
      intro o ho
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at ho
      simp [ho]
    · simp
  simp [dirichletMultinomialLogPredictive, logMultinomialCoefficient, oneHot,
    parameters, logMultivariateBeta]
  rw [hgamma, hsum, Finset.sum_eq_add_sum_diff_singleton observed]
  simp [Real.Gamma_add_one ha0,
    Real.log_mul ha0 (Real.Gamma_pos_of_pos (hα observed)).ne',
    Real.Gamma_add_one hsum0, Real.log_mul hsum0 (Real.Gamma_pos_of_pos hsumpos).ne',
    Real.log_div ha0 hsum0] <;> simp_all <;> ring
  all_goals
    intro
    simp

/-- `scan_learn.clj:158-169`: the two-outcome instance is definitionally the
Beta-Binomial specialization of the Dirichlet-multinomial formula. -/
theorem betaBinomialLogPredictive_eq (alpha : Bool → ℝ) (hα : ∀ o, 0 < alpha o)
    (n : Bool → ℕ) :
    dirichletMultinomialLogPredictive alpha hα n =
      logMultinomialCoefficient n +
        logMultivariateBeta (parameters (fun o => alpha o + n o)
          (fun o => add_pos_of_pos_of_nonneg (hα o) (Nat.cast_nonneg _))) -
        logMultivariateBeta (parameters alpha hα) := by
  rfl

/-- `scan_learn.clj:175-199`, `status-log-likelihoods`: for one status, sum
the integrated predictive over exactly the used keys. Unobserved keys are not
members of `used` and therefore contribute nothing. -/
def scanLogLikelihood [Fintype K] (used : Finset K)
    (predictive : K → S → ℝ) (status : S) : ℝ :=
  ∑ key ∈ used, predictive key status

/-- A typed fixture guarding the `key → status` argument order of
`scanLogLikelihood`; transposing outcome/status-indexed data cannot inhabit
the `predictive` argument used here. -/
example :
    scanLogLikelihood ({false} : Finset Bool)
      (fun key status : Bool => if key then (if status then 40 else 30)
                               else (if status then 20 else 10)) true = 20 := by
  norm_num [scanLogLikelihood]

#print axioms dirichletCategoricalLogPredictive_eq
#print axioms betaBinomialLogPredictive_eq

end

end DarkTower.WarMachine.ScanLearning
