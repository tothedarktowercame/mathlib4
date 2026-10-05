import DarkTower.WarMachine.PolicyPrecision
import DarkTower.WarMachine.R20Interoception
import Mathlib.Tactic

/-!
# Precision from observation

How decisive the agent is is not a dial set from outside.  It increases when
the observations support the policies already favoured by expected free
energy, decreases when they count against those policies, and is unchanged
when the observation does not discriminate among policies.

Friston et al. (2017), equation (2.7), `refs/friston2017.txt:674-690`, gives
`pi = softmax (-F - gamma*G)`, `beta = beta + (pi-pi0).G`,
`gamma = 1/beta`, and `pi0 = softmax (-gamma*G)`.  The text says these
equalities are normally iterated to convergence.  This module states one
explicit update step: both distributions use the incoming `beta0`, then the
displayed evidence term produces `beta1`.  Section 2.6, lines 775-800,
explains that reducing expected G under the posterior raises precision.

`PolicyPrecision.precisionWeightedPosterior` additionally admits a habit E;
the distributions below are the paper's displayed equation with no habit
term (equivalently, a uniform habit whose common log mass cancels).

The current rebuilt path computes this update retrospectively when a verified
predecessor observation is admitted: `policy_precision_carry.clj`
`retrospective-f` supplies per-policy F and `advance` calls
`cascade-beta-update`; otherwise it retains the last valid/caller-initialised
beta.  `wm/cascade_decision.clj` then consumes that carried beta.  Per-policy F
is also available at selection through admitted policy prefixes, but absence is
typed and is not silently replaced.  Registry row `:temperature` defines
`:tau` at R14 and has `:imports []`.
-/

namespace DarkTower.WarMachine.PrecisionFromObservation

open scoped BigOperators
noncomputable section

variable {Policy : Type*} [Fintype Policy] [Nonempty Policy]

/-- Finite softmax, used for the prior and posterior policy beliefs. -/
def softmax (score : Policy → ℝ) (p : Policy) : ℝ :=
  Real.exp (score p) / ∑ q, Real.exp (score q)

/-- `pi0 = sigma (-G/beta0)`. -/
def priorPolicy (beta0 : ℝ) (G : Policy → ℝ) : Policy → ℝ :=
  softmax (fun p => -G p / beta0)

/-- `pi = sigma (-F-G/beta0)` for one explicit equation-(2.7) step. -/
def posteriorPolicy (beta0 : ℝ) (G F : Policy → ℝ) : Policy → ℝ :=
  softmax (fun p => -F p - G p / beta0)

/-- `Delta = (pi-pi0).G`, posterior expected G minus prior expected G. -/
def evidenceDelta (beta0 : ℝ) (G F : Policy → ℝ) : ℝ :=
  ∑ p, (posteriorPolicy beta0 G F p - priorPolicy beta0 G p) * G p

/-- The explicit temperature step `beta1 = beta0 + Delta`. -/
def updatedTemperature (beta0 : ℝ) (G F : Policy → ℝ) : ℝ :=
  beta0 + evidenceDelta beta0 G F

def updatedPrecision (beta0 : ℝ) (G F : Policy → ℝ) : ℝ :=
  1 / updatedTemperature beta0 G F

theorem negative_delta_raises_precision {beta0 d : ℝ}
    (hb : 0 < beta0) (hu : 0 < beta0 + d) (hd : d < 0) :
    1 / beta0 < 1 / (beta0 + d) := by
  exact one_div_lt_one_div_of_lt hu (by linarith)

theorem positive_delta_lowers_precision {beta0 d : ℝ}
    (hb : 0 < beta0) (hu : 0 < beta0 + d) (hd : 0 < d) :
    1 / (beta0 + d) < 1 / beta0 := by
  exact one_div_lt_one_div_of_lt hb (by linarith)

theorem posterior_eq_prior_of_constant_F (beta0 : ℝ) (G : Policy → ℝ)
    (c : ℝ) : posteriorPolicy beta0 G (fun _ => c) = priorPolicy beta0 G := by
  funext p
  simp only [posteriorPolicy, priorPolicy, softmax]
  have hs : (∑ q, Real.exp (-c - G q / beta0)) =
      Real.exp (-c) * ∑ q, Real.exp (-G q / beta0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Real.exp_add]
    congr 1 <;> ring
  rw [hs]
  have hn : Real.exp (-c - G p / beta0) =
      Real.exp (-c) * Real.exp (-G p / beta0) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  rw [hn]
  field_simp

theorem constant_F_no_update (beta0 : ℝ) (G : Policy → ℝ) (c : ℝ) :
    evidenceDelta beta0 G (fun _ => c) = 0 ∧
      updatedTemperature beta0 G (fun _ => c) = beta0 ∧
      updatedPrecision beta0 G (fun _ => c) = 1 / beta0 := by
  have h := posterior_eq_prior_of_constant_F beta0 G c
  simp [evidenceDelta, updatedTemperature, updatedPrecision, h]

/-! ## The two-policy consequence -/

inductive TwoPolicy | a | b deriving DecidableEq, Fintype

def priorA (beta Ga Gb : ℝ) : ℝ :=
  let wa := Real.exp (-Ga / beta); let wb := Real.exp (-Gb / beta)
  wa / (wa + wb)

def posteriorA (beta Ga Gb Fa Fb : ℝ) : ℝ :=
  let wa := Real.exp (-Ga / beta); let wb := Real.exp (-Gb / beta)
  let ea := Real.exp (-Fa); let eb := Real.exp (-Fb)
  wa * ea / (wa * ea + wb * eb)

theorem posteriorA_lt_priorA_iff (beta Ga Gb Fa Fb : ℝ) :
    posteriorA beta Ga Gb Fa Fb < priorA beta Ga Gb ↔ Fb < Fa := by
  simp only [posteriorA, priorA]
  rw [div_lt_div_iff₀ (by positivity : 0 < Real.exp (-Ga / beta) * Real.exp (-Fa) +
      Real.exp (-Gb / beta) * Real.exp (-Fb))
    (by positivity : 0 < Real.exp (-Ga / beta) + Real.exp (-Gb / beta))]
  constructor
  · intro h
    ring_nf at h
    have he : Real.exp (-Fa) < Real.exp (-Fb) := by
      have hc : Real.exp (-(Ga * beta⁻¹)) * Real.exp (-(beta⁻¹ * Gb)) * Real.exp (-Fa) <
          Real.exp (-(Ga * beta⁻¹)) * Real.exp (-(beta⁻¹ * Gb)) * Real.exp (-Fb) := by
        linarith
      by_contra nh
      have hle : Real.exp (-Fb) ≤ Real.exp (-Fa) := le_of_not_gt nh
      let z : ℝ := Real.exp (-(Ga * beta⁻¹)) * Real.exp (-(beta⁻¹ * Gb))
      have hz : 0 ≤ z := (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
      have bad : z * Real.exp (-Fb) ≤ z * Real.exp (-Fa) :=
        mul_le_mul_of_nonneg_left hle hz
      dsimp [z] at bad
      exact (not_lt_of_ge bad) (by simpa [mul_assoc] using hc)
    linarith [Real.exp_lt_exp.mp he]
  · intro h
    have he : Real.exp (-Fa) < Real.exp (-Fb) := Real.exp_lt_exp.mpr (by linarith)
    ring_nf
    have hc := mul_lt_mul_of_pos_left he
      (mul_pos (Real.exp_pos (-(Ga * beta⁻¹))) (Real.exp_pos (-(beta⁻¹ * Gb))))
    nlinarith [hc]

theorem priorA_lt_posteriorA_iff (beta Ga Gb Fa Fb : ℝ) :
    priorA beta Ga Gb < posteriorA beta Ga Gb Fa Fb ↔ Fa < Fb := by
  simp only [posteriorA, priorA]
  rw [div_lt_div_iff₀
    (by positivity : 0 < Real.exp (-Ga / beta) + Real.exp (-Gb / beta))
    (by positivity : 0 < Real.exp (-Ga / beta) * Real.exp (-Fa) +
      Real.exp (-Gb / beta) * Real.exp (-Fb))]
  constructor
  · intro h
    ring_nf at h
    have he : Real.exp (-Fb) < Real.exp (-Fa) := by
      have hc : Real.exp (-(Ga * beta⁻¹)) * Real.exp (-(beta⁻¹ * Gb)) * Real.exp (-Fb) <
          Real.exp (-(Ga * beta⁻¹)) * Real.exp (-(beta⁻¹ * Gb)) * Real.exp (-Fa) := by
        linarith
      by_contra nh
      have hle : Real.exp (-Fa) ≤ Real.exp (-Fb) := le_of_not_gt nh
      let z : ℝ := Real.exp (-(Ga * beta⁻¹)) * Real.exp (-(beta⁻¹ * Gb))
      have hz : 0 ≤ z := (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
      have bad : z * Real.exp (-Fa) ≤ z * Real.exp (-Fb) :=
        mul_le_mul_of_nonneg_left hle hz
      dsimp [z] at bad
      exact (not_lt_of_ge bad) (by simpa [mul_assoc] using hc)
    linarith [Real.exp_lt_exp.mp he]
  · intro h
    have he : Real.exp (-Fb) < Real.exp (-Fa) := Real.exp_lt_exp.mpr (by linarith)
    ring_nf
    have hc := mul_lt_mul_of_pos_left he
      (mul_pos (Real.exp_pos (-(Ga * beta⁻¹))) (Real.exp_pos (-(beta⁻¹ * Gb))))
    nlinarith [hc]

def twoDelta (beta Ga Gb Fa Fb : ℝ) : ℝ :=
  (posteriorA beta Ga Gb Fa Fb - priorA beta Ga Gb) * Ga +
  ((1 - posteriorA beta Ga Gb Fa Fb) - (1 - priorA beta Ga Gb)) * Gb

theorem observations_against_favored_raise_temperature {beta Ga Gb Fa Fb : ℝ}
    (hG : Ga < Gb) (hF : Fb < Fa) : 0 < twoDelta beta Ga Gb Fa Fb := by
  have hp := (posteriorA_lt_priorA_iff beta Ga Gb Fa Fb).2 hF
  have hd : twoDelta beta Ga Gb Fa Fb =
      (posteriorA beta Ga Gb Fa Fb - priorA beta Ga Gb) * (Ga - Gb) := by
    simp [twoDelta]; ring
  rw [hd]
  exact mul_pos_of_neg_of_neg (sub_neg.mpr hp) (sub_neg.mpr hG)

theorem observations_for_favored_lower_temperature {beta Ga Gb Fa Fb : ℝ}
    (hG : Ga < Gb) (hF : Fa < Fb) : twoDelta beta Ga Gb Fa Fb < 0 := by
  have hp := (priorA_lt_posteriorA_iff beta Ga Gb Fa Fb).2 hF
  have hd : twoDelta beta Ga Gb Fa Fb =
      (posteriorA beta Ga Gb Fa Fb - priorA beta Ga Gb) * (Ga - Gb) := by
    simp [twoDelta]; ring
  rw [hd]
  exact mul_neg_of_pos_of_neg (sub_pos.mpr hp) (sub_neg.mpr hG)

/-! The two-policy quantities above are the general ones on a two-policy type. -/

theorem sum_twoPolicy (f : TwoPolicy → ℝ) : ∑ p, f p = f .a + f .b := by
  have univ : (Finset.univ : Finset TwoPolicy) = {TwoPolicy.a, TwoPolicy.b} := by decide
  rw [univ, Finset.sum_pair (by decide)]

theorem priorPolicy_a (beta : ℝ) (G : TwoPolicy → ℝ) :
    priorPolicy beta G .a = priorA beta (G .a) (G .b) := by
  simp [priorPolicy, softmax, sum_twoPolicy, priorA]

theorem priorPolicy_b (beta : ℝ) (G : TwoPolicy → ℝ) :
    priorPolicy beta G .b = 1 - priorA beta (G .a) (G .b) := by
  simp only [priorPolicy, softmax, sum_twoPolicy, priorA]
  have pos : 0 < Real.exp (-G .a / beta) + Real.exp (-G .b / beta) := by positivity
  field_simp
  ring

theorem posteriorPolicy_a (beta : ℝ) (G F : TwoPolicy → ℝ) :
    posteriorPolicy beta G F .a = posteriorA beta (G .a) (G .b) (F .a) (F .b) := by
  simp only [posteriorPolicy, softmax, sum_twoPolicy, posteriorA]
  have ea : Real.exp (-F .a - G .a / beta) = Real.exp (-G .a / beta) * Real.exp (-F .a) := by
    rw [← Real.exp_add]; congr 1; ring
  have eb : Real.exp (-F .b - G .b / beta) = Real.exp (-G .b / beta) * Real.exp (-F .b) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [ea, eb]

theorem posteriorPolicy_b (beta : ℝ) (G F : TwoPolicy → ℝ) :
    posteriorPolicy beta G F .b = 1 - posteriorA beta (G .a) (G .b) (F .a) (F .b) := by
  simp only [posteriorPolicy, softmax, sum_twoPolicy, posteriorA]
  have ea : Real.exp (-F .a - G .a / beta) = Real.exp (-G .a / beta) * Real.exp (-F .a) := by
    rw [← Real.exp_add]; congr 1; ring
  have eb : Real.exp (-F .b - G .b / beta) = Real.exp (-G .b / beta) * Real.exp (-F .b) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [ea, eb]
  have pos : 0 < Real.exp (-G .a / beta) * Real.exp (-F .a) +
      Real.exp (-G .b / beta) * Real.exp (-F .b) := by positivity
  field_simp
  ring

/-- On two policies, the general evidence term is `twoDelta`. -/
theorem evidenceDelta_twoPolicy (beta : ℝ) (G F : TwoPolicy → ℝ) :
    evidenceDelta beta G F = twoDelta beta (G .a) (G .b) (F .a) (F .b) := by
  simp only [evidenceDelta, sum_twoPolicy, priorPolicy_a, priorPolicy_b,
    posteriorPolicy_a, posteriorPolicy_b, twoDelta]

/-- The general statement on two policies: observations that count against
the policy expected free energy favours raise the temperature given by the
paper's update, for every incoming temperature. -/
theorem against_favoured_raises_updatedTemperature (beta : ℝ) (G F : TwoPolicy → ℝ)
    (favoured : G .a < G .b) (against : F .b < F .a) :
    beta < updatedTemperature beta G F := by
  have positive := observations_against_favored_raise_temperature
    (beta := beta) favoured against
  rw [← evidenceDelta_twoPolicy] at positive
  simp only [updatedTemperature]
  linarith

/-- Control with nothing assumed about the evidence term: a record that leaves
the temperature where it was, although the observations count against the
favoured policy, does not conform. -/
theorem unchanged_against_favoured_refused (beta : ℝ) (G F : TwoPolicy → ℝ)
    (favoured : G .a < G .b) (against : F .b < F .a) :
    ¬ (0 < beta ∧
      beta = updatedTemperature beta G F) := by
  rintro ⟨_, unchanged⟩
  have raised := against_favoured_raises_updatedTemperature beta G F favoured against
  linarith

/-! ## Interoceptive observations -/

def finiteSurprisal (p : ℝ) : ℝ := -Real.log p

theorem lower_prediction_has_higher_surprisal {pa pb : ℝ}
    (ha : 0 < pa) (h : pa < pb) : finiteSurprisal pb < finiteSurprisal pa := by
  simp only [finiteSurprisal]
  linarith [Real.strictMonoOn_log ha (lt_trans ha h) h]

/-- A finite out-of-range reading predicted less by the favoured policy than
by its alternative supplies exactly the `F_a > F_b` premise above, so it
lowers precision whenever the updated temperature remains positive. -/
theorem interoceptive_reading_lowers_precision {beta Ga Gb pa pb : ℝ}
    (hb : 0 < beta) (hG : Ga < Gb) (ha : 0 < pa) (hp : pa < pb)
    (hu : 0 < beta + twoDelta beta Ga Gb (finiteSurprisal pa) (finiteSurprisal pb)) :
    1 / (beta + twoDelta beta Ga Gb (finiteSurprisal pa) (finiteSurprisal pb)) < 1 / beta := by
  apply positive_delta_lowers_precision hb hu
  exact observations_against_favored_raise_temperature hG
    (lower_prediction_has_higher_surprisal ha hp)

/-- At predictive mass zero, R20's extended-real surprisal is `⊤`; it cannot
be inserted into the real-valued finite update above and instead represents
zero posterior support for that policy. -/
theorem zero_prediction_surprisal_top {Reading : Type*} [Fintype Reading]
    [DecidableEq Reading] (P : Reading → ℝ) (i : Reading) (h : P i = 0) :
    R20Interoception.surprisal P i = ⊤ :=
  R20Interoception.zero_mass_surprisal_top h

/-! ## Retained-record conformance -/

structure TickRecord (Policy : Type*) where
  G : Policy → ℝ
  F : Policy → ℝ
  prior : Policy → ℝ
  posterior : Policy → ℝ
  beta0 : ℝ
  beta1 : ℝ

def Conforms (r : TickRecord Policy) : Prop :=
  0 < r.beta0 ∧ r.prior = priorPolicy r.beta0 r.G ∧
    r.posterior = posteriorPolicy r.beta0 r.G r.F ∧
    r.beta1 = updatedTemperature r.beta0 r.G r.F

def unchangedRecord (beta : ℝ) (G F : Policy → ℝ) : TickRecord Policy :=
  ⟨G, F, priorPolicy beta G, posteriorPolicy beta G F, beta, beta⟩

theorem unchanged_with_evidence_refused {beta : ℝ} {G F : Policy → ℝ}
    (hd : evidenceDelta beta G F ≠ 0) : ¬ Conforms (unchangedRecord beta G F) := by
  intro h
  rcases h with ⟨_, _, _, hu⟩
  simp [unchangedRecord, updatedTemperature] at hu
  exact hd (by linarith)

def factorRecord (k beta : ℝ) (G F : Policy → ℝ) : TickRecord Policy :=
  ⟨G, F, priorPolicy beta G, posteriorPolicy beta G F, beta, beta * k⟩

theorem arbitrary_factor_refused {k beta : ℝ} {G F : Policy → ℝ}
    (wrong : beta * k ≠ updatedTemperature beta G F) :
    ¬ Conforms (factorRecord k beta G F) := by
  intro h
  exact wrong h.2.2.2

end
end DarkTower.WarMachine.PrecisionFromObservation
