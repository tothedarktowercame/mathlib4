import DarkTower.WarMachine.Holes
import DarkTower.WarMachine.DirichletLearning
import DarkTower.WarMachine.ExactBeliefTrajectory

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
open DarkTower.WarMachine.DirichletLearning
open DarkTower.WarMachine.ExactBeliefTrajectory

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

/-- `scan_learn.clj:175-199`, `status-log-likelihoods`: for one status, sum
the integrated predictive over exactly the used keys, reading the existing
`DirichletParams` in its declared outcome-first order `conc o s`. Unobserved
keys are absent from `used` and contribute nothing. This common-`O` version
models a family of keys sharing one outcome carrier. -/
def scanStatusLogLikelihood [Fintype K] [Fintype O] [Nonempty O]
    (used : Finset K) (alpha : K → DirichletParams O S) (counts : K → O → ℕ)
    (status : S) : ℝ :=
  ∑ key ∈ used, dirichletMultinomialLogPredictive
    (fun o => (alpha key).conc o status) (fun o => (alpha key).pos o status) (counts key)

/-- `scan_learn.clj:201-206`, `predicted-q`: the status transition
`B_rho = (1-rho)I + rho*Uniform`, oriented as `B previous next`. -/
def scanTransition [Fintype S] [DecidableEq S] (rho : ℝ) (previous next : S) : ℝ :=
  (1 - rho) * (if previous = next then 1 else 0) + rho / Fintype.card S

/-- Every row of `scanTransition` sums to one (`scan_learn.clj:201-206`). -/
theorem scanTransition_row_sum [Fintype S] [Nonempty S] [DecidableEq S]
    (rho : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) (previous : S) :
    ∑ next, scanTransition rho previous next = 1 := by
  have hc : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [scanTransition, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, hc]
  field_simp
  ring

/-- `scan_learn.clj:230-263`, `step`: exact categorical filtering using
`scanTransition` and the exponentiated integrated status log-likelihood. -/
def scanPosterior [Fintype S] [DecidableEq S] (rho : ℝ) (ll : S → ℝ)
    (qPrevious : S → ℝ) : Option (S → ℝ) :=
  exactUpdate (fun s (_ : Unit) => Real.exp (ll s)) (scanTransition rho) () qPrevious

/-- A successful `scanPosterior` has exactly the normalized
`exp(log-likelihood) * predicted-q` form computed at `scan_learn.clj:248-263`. -/
theorem scanPosterior_some [Fintype S] [DecidableEq S] (rho : ℝ) (ll : S → ℝ)
    (qPrevious q : S → ℝ) (h : scanPosterior rho ll qPrevious = some q) (x : S) :
    q x = Real.exp (ll x) * predictedState (scanTransition rho) qPrevious x /
      ∑ y, Real.exp (ll y) * predictedState (scanTransition rho) qPrevious y := by
  unfold scanPosterior exactUpdate at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    subst q
    rfl

/-- `scan_learn.clj:265-272`, `step`: one key's q-weighted count update,
specialized directly from `DirichletLearning.step`. -/
def scanAccumulate (prior : DirichletParams O S) (counts : O → ℕ) (q : S → ℝ)
    (hq : ∀ s, 0 ≤ q s) : DirichletParams O S :=
  step prior (fun o => counts o, q) (fun o => Nat.cast_nonneg _) hq

/-- The concentration selected by `scanAccumulate` is prior plus count times
posterior mass, the update at `scan_learn.clj:265-272`. -/
theorem scanAccumulate_conc (prior : DirichletParams O S) (counts : O → ℕ)
    (q : S → ℝ) (hq : ∀ s, 0 ≤ q s) (o : O) (s : S) :
    (scanAccumulate prior counts q hq).conc o s = prior.conc o s + counts o * q s := by
  rfl

/-- Concrete outcome-first fixture for `scanStatusLogLikelihood` itself. At
status `true`, outcome `false` has concentration 3 and the row total is 10,
so the one-hot likelihood is `log (3/10)`, not the transposed row's value.
This is the access performed at `scan_learn.clj:195-197`. -/
example :
    let a : Bool → DirichletParams Bool Bool := fun _ =>
      ⟨fun outcome status => if outcome then (if status then 7 else 5)
                             else (if status then 3 else 2), by norm_num⟩
    scanStatusLogLikelihood ({false} : Finset Bool) a
      (fun _ => oneHot false) true = Real.log (3 / 10 : ℝ) := by
  simp only [scanStatusLogLikelihood, Finset.sum_singleton]
  rw [dirichletCategoricalLogPredictive_eq]
  norm_num

#print axioms dirichletCategoricalLogPredictive_eq
#print axioms scanTransition_row_sum
#print axioms scanPosterior_some
#print axioms scanAccumulate_conc

end

end DarkTower.WarMachine.ScanLearning
