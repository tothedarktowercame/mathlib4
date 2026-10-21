import DarkTower.WarMachine.PrecisionFromObservation

/-!
# Policy-conditioned free energy from observed outcomes

Friston et al. (2017), `refs/friston2017.txt:1600-1612`, defines
F_π = ∑_τ F(π,τ), complexity minus accuracy; line 780 distinguishes this
free energy based on past outcomes from expected free energy G.
Parr et al. (2022), B.4 (`refs/parr2022.txt:12560`), uses D at the first
tick and the policy-conditioned transition prior thereafter; :12631-12634
identifies its role as negative log model evidence. Here `prior` is that
supplied categorical predictive prior, and `lik s` is the likelihood of the
actually observed outcome (a column selected from a finite observation model).
The sum identity is conditional on exact Bayes posteriors at every tick;
no claim that approximate/mean-field state inference is exact is made.

Real.log 0 = 0 implements the zero-weight convention. Consequently the Gibbs
bound explicitly requires q to be supported on prior: assigning positive q
to a zero prior must not silently acquire finite cost via that convention.
-/

namespace DarkTower.WarMachine.PolicyFreeEnergy
open scoped BigOperators
noncomputable section
variable {S : Type*} [Fintype S]

def ProbabilityVector (p : S → ℝ) : Prop := (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1

def tickFreeEnergy (q prior lik : S → ℝ) : ℝ :=
  ∑ s, q s * (Real.log (q s) - Real.log (prior s) - Real.log (lik s))

def evidence (prior lik : S → ℝ) : ℝ := ∑ s, prior s * lik s

def policyFreeEnergy {Policy : Type*} {T : ℕ}
    (q prior lik : Policy → Fin T → S → ℝ) (π : Policy) : ℝ :=
  ∑ t, tickFreeEnergy (q π t) (prior π t) (lik π t)

private theorem bayes_sum (prior lik : S → ℝ) (hz : 0 < evidence prior lik) :
    ∑ s, prior s * lik s / evidence prior lik = 1 := by
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hz)

/-- T1: exact categorical inference attains negative log evidence, including
states with zero prior mass. -/
theorem exact_posterior {q prior lik : S → ℝ}
    (hp : ProbabilityVector prior) (hl : ∀ s, 0 < lik s)
    (hz : 0 < evidence prior lik)
    (hq : ∀ s, q s = prior s * lik s / evidence prior lik) :
    tickFreeEnergy q prior lik = -Real.log (evidence prior lik) := by
  have hs : ∑ s, q s = 1 := by
    simp_rw [hq]
    exact bayes_sum prior lik hz
  have term (s : S) : q s * (Real.log (q s) - Real.log (prior s) -
      Real.log (lik s)) = q s * (-Real.log (evidence prior lik)) := by
    by_cases h : prior s = 0
    · simp [hq, h]
    · have pos : 0 < prior s := lt_of_le_of_ne (hp.1 s) (Ne.symm h)
      rw [hq s, Real.log_div (ne_of_gt (mul_pos pos (hl s))) (ne_of_gt hz),
        Real.log_mul h (ne_of_gt (hl s))]
      ring
  simp only [tickFreeEnergy, term, ← Finset.sum_mul, hs, one_mul]

theorem exact_posterior_finiteSurprisal {q prior lik : S → ℝ}
    (hp : ProbabilityVector prior) (hl : ∀ s, 0 < lik s)
    (hz : 0 < evidence prior lik)
    (hq : ∀ s, q s = prior s * lik s / evidence prior lik) :
    tickFreeEnergy q prior lik =
      PrecisionFromObservation.finiteSurprisal (evidence prior lik) :=
  exact_posterior hp hl hz hq

/-- T2: Gibbs bound via log x ≤ x - 1, with explicit support at zero prior. -/
theorem gibbs_bound {q prior lik : S → ℝ}
    (hp : ProbabilityVector prior) (hl : ∀ s, 0 < lik s)
    (hz : 0 < evidence prior lik) (hq : ProbabilityVector q)
    (support : ∀ s, prior s = 0 → q s = 0) :
    -Real.log (evidence prior lik) ≤ tickFreeEnergy q prior lik := by
  let r := fun s => prior s * lik s / evidence prior lik
  have hr : ∑ s, r s = 1 := bayes_sum prior lik hz
  have term (s : S) : q s - r s ≤
      q s * (Real.log (q s) - Real.log (prior s) - Real.log (lik s)) +
        q s * Real.log (evidence prior lik) := by
    by_cases zero : q s = 0
    · have rn : 0 ≤ r s := div_nonneg (mul_nonneg (hp.1 s) (hl s).le) hz.le
      simp only [zero, zero_mul, zero_sub, add_zero]
      linarith
    · have qp : 0 < q s := lt_of_le_of_ne (hq.1 s) (Ne.symm zero)
      have pn : prior s ≠ 0 := fun h => zero (support s h)
      have pp : 0 < prior s := lt_of_le_of_ne (hp.1 s) (Ne.symm pn)
      have rp : 0 < r s := div_pos (mul_pos pp (hl s)) hz
      have bound := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos rp qp)) qp.le
      rw [Real.log_div (ne_of_gt rp) zero] at bound
      have lr : Real.log (r s) = Real.log (prior s) + Real.log (lik s) -
          Real.log (evidence prior lik) := by
        dsimp [r]
        rw [Real.log_div (ne_of_gt (mul_pos pp (hl s))) (ne_of_gt hz),
          Real.log_mul pn (ne_of_gt (hl s))]
      rw [lr] at bound
      have cancel : q s * (r s / q s - 1) = r s - q s := by
        field_simp
      rw [cancel] at bound
      nlinarith
  have total := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => term s)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, hq.2, hr, one_mul, sub_self] at total
  unfold tickFreeEnergy
  linarith

/-- Exact inference at each observed tick makes F_π the sum of surprisals. -/
theorem policyFreeEnergy_eq_sum_surprisal {Policy : Type*} {T : ℕ}
    (q prior lik : Policy → Fin T → S → ℝ)
    (hp : ∀ π t, ProbabilityVector (prior π t))
    (hl : ∀ π t s, 0 < lik π t s)
    (hz : ∀ π t, 0 < evidence (prior π t) (lik π t))
    (hq : ∀ π t s, q π t s = prior π t s * lik π t s /
      evidence (prior π t) (lik π t)) (π : Policy) :
    policyFreeEnergy q prior lik π =
      ∑ t, PrecisionFromObservation.finiteSurprisal (evidence (prior π t) (lik π t)) := by
  apply Finset.sum_congr rfl
  intro t _
  exact exact_posterior_finiteSurprisal (hp π t) (hl π t) (hz π t) (hq π t)

/-- T3: policy-independent evidence leaves policy beliefs unchanged. E, G and
beta are the same in both beliefs; no new menu or preferences are substituted. -/
theorem nondiscriminating_posterior {Policy : Type*} [Fintype Policy] [Nonempty Policy]
    {T : ℕ} (beta : ℝ) (E G : Policy → ℝ)
    (q prior lik : Policy → Fin T → S → ℝ) (z : Fin T → ℝ)
    (hp : ∀ π t, ProbabilityVector (prior π t))
    (hl : ∀ π t s, 0 < lik π t s)
    (hz : ∀ π t, 0 < evidence (prior π t) (lik π t))
    (hq : ∀ π t s, q π t s = prior π t s * lik π t s /
      evidence (prior π t) (lik π t))
    (same : ∀ π t, evidence (prior π t) (lik π t) = z t) :
    PrecisionFromObservation.posteriorPolicy beta E G (fun π => policyFreeEnergy q prior lik π) =
      PrecisionFromObservation.priorPolicy beta E G := by
  have const : (fun π => policyFreeEnergy q prior lik π) =
      (fun _ => ∑ t, PrecisionFromObservation.finiteSurprisal (z t)) := by
    funext π
    rw [policyFreeEnergy_eq_sum_surprisal q prior lik hp hl hz hq]
    simp_rw [same]
  rw [const]
  exact PrecisionFromObservation.posterior_eq_prior_of_constant_F beta E G _

/-- Control: uniform prior, uninformative likelihood 1, but point-mass q.
The exact posterior is uniform; this non-exact q costs log 2 > 0. -/
theorem nonexact_control :
    let q : Bool → ℝ := fun s => if s then 1 else 0
    let prior : Bool → ℝ := fun _ => 1 / 2
    let lik : Bool → ℝ := fun _ => 1
    ProbabilityVector q ∧ ProbabilityVector prior ∧
      (∀ s, 0 < lik s) ∧ 0 < evidence prior lik ∧
      q true ≠ prior true * lik true / evidence prior lik ∧
      -Real.log (evidence prior lik) < tickFreeEnergy q prior lik := by
  norm_num [ProbabilityVector, evidence, tickFreeEnergy,
    Real.log_div, Real.log_one]
  exact Real.log_pos (by norm_num)

#print axioms exact_posterior
#print axioms gibbs_bound
#print axioms nondiscriminating_posterior
#print axioms nonexact_control

end
end DarkTower.WarMachine.PolicyFreeEnergy
