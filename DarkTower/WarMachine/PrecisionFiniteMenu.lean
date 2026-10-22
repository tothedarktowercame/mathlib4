import DarkTower.WarMachine.PrecisionFromObservation

/-!
# Precision from observation, for any finite menu of policies

In plain terms: when the observation favours the same policies that G
favours, the machine becomes more decisive; when it favours the policies G
disfavours, less decisive. `PrecisionFromObservation` proves this for a menu
of two policies. This module proves it for any finite, nonempty menu.

Source: Friston et al. (2017), eq. 2.7, `refs/friston2017.txt:660-685`:
`pi=sigma(-F-gamma G)`, `beta=betaPrior+(pi-pi0).G`, with the habit E of
Parr et al. (2022) B.7 in both beliefs, as in `PrecisionFromObservation`.
The change `(pi-pi0).G` is the posterior expected G minus the prior expected
G. The posterior is the prior reweighted by `exp(-F)`, so the change is a
covariance under the prior between `exp(-F)` and G, divided by a positive
normaliser. Its sign is fixed by how F and G are ordered relative to each
other.

"Similarly ordered" is stated pairwise: for every two policies,
`(G p - G q) * (F p - F q) ≥ 0`, with one pair strictly positive. For two
policies this is the hypothesis pair `G a < G b`, `F a < F b` of
`favoured_observation_raises_precision`; `twoPolicy_similarlyOrdered` checks
that the general statement covers it. No total order on policies, no
monotone map from G to F, and no particular habit E is assumed.
-/

namespace DarkTower.WarMachine.PrecisionFromObservation
open scoped BigOperators
noncomputable section
variable {Policy : Type*} [Fintype Policy] [Nonempty Policy]

/-- The unnormalised prior mass of a policy, `exp(ln E - G/beta)`. -/
def priorWeight (beta : ℝ) (E G : Policy → ℝ) (p : Policy) : ℝ :=
  Real.exp (Real.log (E p) - G p / beta)

/-- The observation's reweighting of a policy, `exp(-F)`. -/
def evidenceWeight (F : Policy → ℝ) (p : Policy) : ℝ := Real.exp (-F p)

/-- F ranks the policies as G does, strictly for at least one pair. -/
def SimilarlyOrdered (G F : Policy → ℝ) : Prop :=
  (∀ p q, 0 ≤ (G p - G q) * (F p - F q)) ∧ ∃ p q, 0 < (G p - G q) * (F p - F q)

/-- F ranks the policies against G, strictly for at least one pair. -/
def OppositelyOrdered (G F : Policy → ℝ) : Prop :=
  (∀ p q, (G p - G q) * (F p - F q) ≤ 0) ∧ ∃ p q, (G p - G q) * (F p - F q) < 0

omit [Nonempty Policy] in
theorem priorPolicy_eq_weight (beta : ℝ) (E G : Policy → ℝ) (p : Policy) :
    priorPolicy beta E G p = priorWeight beta E G p / ∑ q, priorWeight beta E G q := rfl

omit [Nonempty Policy] in
theorem posteriorPolicy_eq_weight (beta : ℝ) (E G F : Policy → ℝ) (p : Policy) :
    posteriorPolicy beta E G F p =
      priorWeight beta E G p * evidenceWeight F p /
        ∑ q, priorWeight beta E G q * evidenceWeight F q := by
  have h : ∀ q, Real.exp (Real.log (E q) - F q - G q / beta) =
      priorWeight beta E G q * evidenceWeight F q := by
    intro q
    simp only [priorWeight, evidenceWeight, ← Real.exp_add]
    congr 1; ring
  simp only [posteriorPolicy, softmax, h]

omit [Nonempty Policy] in
/-- Twice the cross term, as a double sum of pairwise products. -/
theorem pairwise_covariance (u w G : Policy → ℝ) :
    2 * ((∑ p, u p * w p * G p) * (∑ q, u q) - (∑ p, u p * G p) * (∑ q, u q * w q)) =
      ∑ p, ∑ q, u p * u q * ((w p - w q) * (G p - G q)) := by
  have expand : ∀ p q, u p * u q * ((w p - w q) * (G p - G q)) =
      u p * w p * G p * u q - u p * G p * (u q * w q)
        + (u q * w q * G q * u p - u q * G q * (u p * w p)) := by
    intro p q; ring
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun p q => u q * w q * G q * u p)]
  rw [Finset.sum_comm (f := fun p q => u q * G q * (u p * w p))]
  simp only [← Finset.mul_sum, Finset.sum_mul]
  ring

theorem expectedGChange_eq_covariance (beta : ℝ) (E G F : Policy → ℝ) :
    expectedGChange beta E G F =
      ((∑ p, priorWeight beta E G p * evidenceWeight F p * G p) *
          (∑ q, priorWeight beta E G q) -
        (∑ p, priorWeight beta E G p * G p) *
          (∑ q, priorWeight beta E G q * evidenceWeight F q)) /
      ((∑ q, priorWeight beta E G q * evidenceWeight F q) * ∑ q, priorWeight beta E G q) := by
  have hu : 0 < ∑ q, priorWeight beta E G q :=
    Finset.sum_pos (fun q _ => Real.exp_pos _) Finset.univ_nonempty
  have huw : 0 < ∑ q, priorWeight beta E G q * evidenceWeight F q :=
    Finset.sum_pos (fun q _ => mul_pos (Real.exp_pos _) (Real.exp_pos _)) Finset.univ_nonempty
  unfold expectedGChange
  simp only [posteriorPolicy_eq_weight, priorPolicy_eq_weight, sub_mul, Finset.sum_sub_distrib,
    div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp

omit [Nonempty Policy] in
/-- The cross term is negative when `w` is ordered against `g` pair by pair,
strictly for one pair, and every weight `u` is positive. -/
theorem cross_neg {u w g : Policy → ℝ} (pos : ∀ p, 0 < u p)
    (term : ∀ p q, (w p - w q) * (g p - g q) ≤ 0)
    {p₀ q₀ : Policy} (strict : (w p₀ - w q₀) * (g p₀ - g q₀) < 0) :
    (∑ p, u p * w p * g p) * (∑ q, u q) - (∑ p, u p * g p) * (∑ q, u q * w q) < 0 := by
  have inner : ∀ p, ∑ q, u p * u q * ((w p - w q) * (g p - g q)) ≤ 0 := fun p =>
    Finset.sum_nonpos fun q _ =>
      mul_nonpos_of_nonneg_of_nonpos (mul_pos (pos p) (pos q)).le (term p q)
  have innerStrict : ∑ q, u p₀ * u q * ((w p₀ - w q) * (g p₀ - g q)) < 0 := by
    have hlt := Finset.sum_lt_sum (s := Finset.univ)
      (f := fun q => u p₀ * u q * ((w p₀ - w q) * (g p₀ - g q))) (g := fun _ => (0 : ℝ))
      (fun q _ => mul_nonpos_of_nonneg_of_nonpos (mul_pos (pos p₀) (pos q)).le (term p₀ q))
      ⟨q₀, Finset.mem_univ _, mul_neg_of_pos_of_neg (mul_pos (pos p₀) (pos q₀)) strict⟩
    simpa using hlt
  have double : ∑ p, ∑ q, u p * u q * ((w p - w q) * (g p - g q)) < 0 := by
    have hlt := Finset.sum_lt_sum (s := Finset.univ) (g := fun _ => (0 : ℝ))
      (fun p _ => inner p) ⟨p₀, Finset.mem_univ _, innerStrict⟩
    simpa using hlt
  have := pairwise_covariance u w g
  linarith

omit [Fintype Policy] [Nonempty Policy] in
/-- `exp(-F)` is ordered against any `g` that F is similarly ordered with. -/
theorem evidenceWeight_against {g F : Policy → ℝ} (h : SimilarlyOrdered g F) :
    (∀ p q, (evidenceWeight F p - evidenceWeight F q) * (g p - g q) ≤ 0) ∧
      ∃ p q, (evidenceWeight F p - evidenceWeight F q) * (g p - g q) < 0 := by
  have pair : ∀ p q, 0 ≤ (g p - g q) * (F p - F q) →
      (evidenceWeight F p - evidenceWeight F q) * (g p - g q) ≤ 0 ∧
      (0 < (g p - g q) * (F p - F q) →
        (evidenceWeight F p - evidenceWeight F q) * (g p - g q) < 0) := by
    intro p q hle
    rcases lt_trichotomy (F p) (F q) with hf | hf | hf
    · have hw : evidenceWeight F q < evidenceWeight F p :=
        Real.exp_lt_exp.mpr (by linarith)
      have hg : g p - g q ≤ 0 := by nlinarith
      refine ⟨by nlinarith, fun hlt => ?_⟩
      have hg' : g p - g q < 0 := by nlinarith
      nlinarith
    · simp [evidenceWeight, hf]
    · have hw : evidenceWeight F p < evidenceWeight F q :=
        Real.exp_lt_exp.mpr (by linarith)
      have hg : 0 ≤ g p - g q := by nlinarith
      refine ⟨by nlinarith, fun hlt => ?_⟩
      have hg' : 0 < g p - g q := by nlinarith
      nlinarith
  obtain ⟨p₀, q₀, strict⟩ := h.2
  exact ⟨fun p q => (pair p q (h.1 p q)).1, p₀, q₀, (pair p₀ q₀ strict.le).2 strict⟩

theorem expectedGChange_neg_of_similarlyOrdered {beta : ℝ} {E G F : Policy → ℝ}
    (h : SimilarlyOrdered G F) : expectedGChange beta E G F < 0 := by
  have hu : 0 < ∑ q, priorWeight beta E G q :=
    Finset.sum_pos (fun q _ => Real.exp_pos _) Finset.univ_nonempty
  have huw : 0 < ∑ q, priorWeight beta E G q * evidenceWeight F q :=
    Finset.sum_pos (fun q _ => mul_pos (Real.exp_pos _) (Real.exp_pos _)) Finset.univ_nonempty
  obtain ⟨term, p₀, q₀, strict⟩ := evidenceWeight_against h
  rw [expectedGChange_eq_covariance]
  exact div_neg_of_neg_of_pos (cross_neg (fun p => Real.exp_pos _) term strict) (mul_pos huw hu)

omit [Fintype Policy] [Nonempty Policy] in
theorem oppositelyOrdered_neg_similarlyOrdered {G F : Policy → ℝ} (h : OppositelyOrdered G F) :
    SimilarlyOrdered (fun p => -G p) F := by
  refine ⟨fun p q => ?_, ?_⟩
  · nlinarith [h.1 p q]
  · obtain ⟨p, q, hpq⟩ := h.2
    exact ⟨p, q, by nlinarith⟩

/-- Opposite ordering: the same covariance with `-G` in the cross term only;
the prior weights keep G. -/
theorem expectedGChange_pos_of_oppositelyOrdered {beta : ℝ} {E G F : Policy → ℝ}
    (h : OppositelyOrdered G F) : 0 < expectedGChange beta E G F := by
  have hu : 0 < ∑ q, priorWeight beta E G q :=
    Finset.sum_pos (fun q _ => Real.exp_pos _) Finset.univ_nonempty
  have huw : 0 < ∑ q, priorWeight beta E G q * evidenceWeight F q :=
    Finset.sum_pos (fun q _ => mul_pos (Real.exp_pos _) (Real.exp_pos _)) Finset.univ_nonempty
  obtain ⟨term, p₀, q₀, strict⟩ :=
    evidenceWeight_against (oppositelyOrdered_neg_similarlyOrdered h)
  have neg := cross_neg (u := priorWeight beta E G) (fun p => Real.exp_pos _) term strict
  simp only [mul_neg, Finset.sum_neg_distrib] at neg
  rw [expectedGChange_eq_covariance]
  apply div_pos _ (mul_pos huw hu)
  linarith

/-- Any finite menu: an observation that ranks the policies as G does makes
the machine more decisive. -/
theorem similarlyOrdered_raises_precision {betaPrior beta : ℝ} {E G F : Policy → ℝ}
    (fixed : IsPosteriorTemperature betaPrior beta E G F) (h : SimilarlyOrdered G F) :
    beta < betaPrior :=
  (posterior_temperature_direction_lt fixed).2 (expectedGChange_neg_of_similarlyOrdered h)

/-- Any finite menu: an observation that ranks the policies against G makes
the machine less decisive. -/
theorem oppositelyOrdered_lowers_precision {betaPrior beta : ℝ} {E G F : Policy → ℝ}
    (fixed : IsPosteriorTemperature betaPrior beta E G F) (h : OppositelyOrdered G F) :
    betaPrior < beta :=
  (posterior_temperature_direction_gt fixed).2 (expectedGChange_pos_of_oppositelyOrdered h)

/-- For two policies, the two-policy hypotheses are the general ones. -/
theorem twoPolicy_similarlyOrdered {G F : TwoPolicy → ℝ} (hG : G .a < G .b) (hF : F .a < F .b) :
    SimilarlyOrdered G F := by
  refine ⟨fun p q => ?_, .a, .b, by nlinarith⟩
  cases p <;> cases q <;> nlinarith

theorem twoPolicy_oppositelyOrdered {G F : TwoPolicy → ℝ} (hG : G .a < G .b)
    (hF : F .b < F .a) :
    OppositelyOrdered G F := by
  refine ⟨fun p q => ?_, .a, .b, by nlinarith⟩
  cases p <;> cases q <;> nlinarith

/-- A three-policy menu, so the general statement is not only ever applied at
two: G and F both rank `0 < 1 < 2`. -/
example : SimilarlyOrdered (fun p : Fin 3 => (p : ℝ)) (fun p : Fin 3 => 2 * (p : ℝ)) := by
  refine ⟨fun p q => by nlinarith [sq_nonneg ((p : ℝ) - q)], 0, 1, by norm_num⟩

/-- Control: F that agrees with G on one pair and disagrees on another is
neither similarly nor oppositely ordered, so neither direction is claimed. -/
theorem mixed_not_similarlyOrdered :
    ¬ SimilarlyOrdered (fun p : Fin 3 => (p : ℝ))
      (fun p : Fin 3 => if p = 1 then 5 else (p : ℝ)) := by
  rintro ⟨h, _⟩
  have := h 1 2
  simp only [show (2 : Fin 3) ≠ 1 by decide, if_true, if_false] at this
  norm_num at this

#print axioms similarlyOrdered_raises_precision
#print axioms oppositelyOrdered_lowers_precision

end
end DarkTower.WarMachine.PrecisionFromObservation
