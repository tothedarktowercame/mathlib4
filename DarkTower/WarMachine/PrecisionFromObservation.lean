import DarkTower.WarMachine.PolicyPrecision
import DarkTower.WarMachine.R20Interoception
import Mathlib.Tactic

/-!
# Precision from observation

Decisiveness is not an external dial. After an observation it settles where
temperature equals prior temperature plus the observation-induced change in
expected G. Evidence for policies G favoured raises precision; evidence
against them lowers it; non-discriminating evidence leaves it unchanged.

Friston et al. (2017), eq. 2.7, `refs/friston2017.txt:660-685`, gives
`pi=sigma(-F-gamma G)`, `beta=betaPrior+(pi-pi0).G`, `gamma=1/beta`, and
`pi0=sigma(-gamma G)`, iterated to convergence; `:1711` gives the error whose
zero is that solution. Parr et al. (2022) B.7, `refs/parr2022.txt:12636-12646`,
includes habit E in `pi0=sigma(ln E-G)`; B.13, `:12720-12728`, omits E “for
simplicity”. Here E occurs in both beliefs at the Friston fixed point.

Conformance requires positive E and temperatures, both beliefs evaluated at
the posterior beta, and zero precision error (or an explicit tolerance).
General positive-root existence is not claimed: it needs endpoint hypotheses
not supplied here; the sign laws and the non-discriminating unique solution
are proved.
-/

namespace DarkTower.WarMachine.PrecisionFromObservation
open scoped BigOperators
noncomputable section
variable {Policy : Type*} [Fintype Policy] [Nonempty Policy]

def softmax (score : Policy → ℝ) (p : Policy) : ℝ :=
  Real.exp (score p) / ∑ q, Real.exp (score q)

def priorPolicy (beta : ℝ) (E G : Policy → ℝ) : Policy → ℝ :=
  softmax (fun p => Real.log (E p) - G p / beta)

def posteriorPolicy (beta : ℝ) (E G F : Policy → ℝ) : Policy → ℝ :=
  softmax (fun p => Real.log (E p) - F p - G p / beta)

def expectedGChange (beta : ℝ) (E G F : Policy → ℝ) : ℝ :=
  ∑ p, (posteriorPolicy beta E G F p - priorPolicy beta E G p) * G p

def precisionError (betaPrior beta : ℝ) (E G F : Policy → ℝ) : ℝ :=
  betaPrior - beta + expectedGChange beta E G F

def IsPosteriorTemperature (betaPrior beta : ℝ) (E G F : Policy → ℝ) : Prop :=
  0 < beta ∧ precisionError betaPrior beta E G F = 0

/-- First numerical pass only, never the conformance target. -/
def firstIterate (betaPrior beta : ℝ) (E G F : Policy → ℝ) : ℝ :=
  betaPrior + expectedGChange beta E G F

def printedPrior (beta : ℝ) (G : Policy → ℝ) := softmax (fun p => -G p / beta)
def printedPosterior (beta : ℝ) (G F : Policy → ℝ) := softmax (fun p => -F p - G p / beta)

theorem softmax_add_constant (score : Policy → ℝ) (c : ℝ) :
    softmax (fun p => c + score p) = softmax score := by
  funext p
  simp only [softmax, Real.exp_add]
  rw [← Finset.mul_sum]
  field_simp

theorem uniform_habit_prior (beta c : ℝ) (hc : 0 < c) (G : Policy → ℝ) :
    priorPolicy beta (fun _ => c) G = printedPrior beta G := by
  unfold priorPolicy printedPrior
  have hs : (fun p => Real.log c - G p / beta) =
      (fun p => Real.log c + (-G p / beta)) := by funext p; ring
  rw [hs]
  exact softmax_add_constant (Policy := Policy) (fun p => -G p / beta) (Real.log c)

theorem uniform_habit_posterior (beta c : ℝ) (hc : 0 < c) (G F : Policy → ℝ) :
    posteriorPolicy beta (fun _ => c) G F = printedPosterior beta G F := by
  simpa [posteriorPolicy, printedPosterior, sub_eq_add_neg, add_assoc] using
    softmax_add_constant (Policy := Policy) (fun p => -F p - G p / beta) (Real.log c)

theorem posterior_eq_prior_of_constant_F (beta : ℝ) (E G : Policy → ℝ) (c : ℝ) :
    posteriorPolicy beta E G (fun _ => c) = priorPolicy beta E G := by
  funext p
  simp only [posteriorPolicy, priorPolicy, softmax]
  have hs : (∑ q, Real.exp (Real.log (E q) - c - G q / beta)) =
      Real.exp (-c) * ∑ q, Real.exp (Real.log (E q) - G q / beta) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intro q _; rw [← Real.exp_add]; congr 1 <;> ring
  rw [hs]
  have hn : Real.exp (Real.log (E p) - c - G p / beta) =
      Real.exp (-c) * Real.exp (Real.log (E p) - G p / beta) := by
    rw [← Real.exp_add]; congr 1 <;> ring
  rw [hn]; field_simp

theorem constant_F_posterior_temperature_iff {betaPrior beta : ℝ}
    (hprior : 0 < betaPrior) (E G : Policy → ℝ) (c : ℝ) :
    IsPosteriorTemperature betaPrior beta E G (fun _ => c) ↔ beta = betaPrior := by
  have same := posterior_eq_prior_of_constant_F beta E G c
  have change : expectedGChange beta E G (fun _ => c) = 0 := by
    simp [expectedGChange, same]
  constructor
  · rintro ⟨_, h⟩
    simp [precisionError, change] at h
    linarith
  · rintro rfl
    exact ⟨hprior, by simp [precisionError, change]⟩

theorem posterior_temperature_direction_lt {betaPrior beta : ℝ} {E G F : Policy → ℝ}
    (fixed : IsPosteriorTemperature betaPrior beta E G F) :
    beta < betaPrior ↔ expectedGChange beta E G F < 0 := by
  rcases fixed with ⟨_, h⟩
  change betaPrior - beta + expectedGChange beta E G F = 0 at h
  constructor <;> intro hi <;> linarith [h]

theorem posterior_temperature_direction_gt {betaPrior beta : ℝ} {E G F : Policy → ℝ}
    (fixed : IsPosteriorTemperature betaPrior beta E G F) :
    betaPrior < beta ↔ 0 < expectedGChange beta E G F := by
  rcases fixed with ⟨_, h⟩
  change betaPrior - beta + expectedGChange beta E G F = 0 at h
  constructor <;> intro hi <;> linarith [h]

theorem posterior_precision_direction {betaPrior beta : ℝ} {E G F : Policy → ℝ}
    (hprior : 0 < betaPrior) (fixed : IsPosteriorTemperature betaPrior beta E G F) :
    (1 / betaPrior < 1 / beta ↔ expectedGChange beta E G F < 0) ∧
    (1 / beta < 1 / betaPrior ↔ 0 < expectedGChange beta E G F) := by
  constructor
  · simp only [one_div]
    rw [inv_lt_inv₀ hprior fixed.1, posterior_temperature_direction_lt fixed]
  · simp only [one_div]
    rw [inv_lt_inv₀ fixed.1 hprior, posterior_temperature_direction_gt fixed]

inductive TwoPolicy | a | b deriving DecidableEq, Fintype
deriving instance Nonempty for TwoPolicy
theorem sum_twoPolicy (f : TwoPolicy → ℝ) : ∑ p, f p = f .a + f .b := by
  have h : (Finset.univ : Finset TwoPolicy) = {.a, .b} := by decide
  rw [h, Finset.sum_pair (by decide)]

def binaryPrior (wa wb : ℝ) := wa / (wa + wb)
def binaryPosterior (wa wb ea eb : ℝ) := wa * ea / (wa * ea + wb * eb)

theorem binaryPosterior_lt_prior_iff {wa wb ea eb : ℝ}
    (hwa : 0 < wa) (hwb : 0 < wb) (hea : 0 < ea) (heb : 0 < eb) :
    binaryPosterior wa wb ea eb < binaryPrior wa wb ↔ ea < eb := by
  simp only [binaryPosterior, binaryPrior]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h
  · by_contra hn
    have := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (mul_pos hwa hwb).le
    nlinarith
  · have := mul_lt_mul_of_pos_left h (mul_pos hwa hwb)
    nlinarith

theorem binaryPrior_lt_posterior_iff {wa wb ea eb : ℝ}
    (hwa : 0 < wa) (hwb : 0 < wb) (hea : 0 < ea) (heb : 0 < eb) :
    binaryPrior wa wb < binaryPosterior wa wb ea eb ↔ eb < ea := by
  simp only [binaryPosterior, binaryPrior]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h
  · by_contra hn
    have := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (mul_pos hwa hwb).le
    nlinarith
  · have := mul_lt_mul_of_pos_left h (mul_pos hwa hwb)
    nlinarith

/- Positive habits affect masses but cancel from the likelihood-ratio direction. -/
theorem two_policy_direction {beta : ℝ} {E G F : TwoPolicy → ℝ}
    (hE : ∀ p, 0 < E p) (hG : G .a < G .b) :
    (F .a < F .b → expectedGChange beta E G F < 0) ∧
    (F .b < F .a → 0 < expectedGChange beta E G F) := by
  let wa := Real.exp (Real.log (E .a) - G .a / beta)
  let wb := Real.exp (Real.log (E .b) - G .b / beta)
  let ea := Real.exp (-F .a)
  let eb := Real.exp (-F .b)
  have hwa : 0 < wa := Real.exp_pos _
  have hwb : 0 < wb := Real.exp_pos _
  have hea : 0 < ea := Real.exp_pos _
  have heb : 0 < eb := Real.exp_pos _
  have pa : priorPolicy beta E G .a = binaryPrior wa wb := by
    simp [priorPolicy, softmax, sum_twoPolicy, binaryPrior, wa, wb]
  have qa : posteriorPolicy beta E G F .a = binaryPosterior wa wb ea eb := by
    simp only [posteriorPolicy, softmax, sum_twoPolicy, binaryPosterior, wa, wb, ea, eb]
    have ha : Real.exp (Real.log (E .a) - F .a - G .a / beta) =
        Real.exp (Real.log (E .a) - G .a / beta) * Real.exp (-F .a) := by
      rw [← Real.exp_add]; congr 1 <;> ring
    have hb : Real.exp (Real.log (E .b) - F .b - G .b / beta) =
        Real.exp (Real.log (E .b) - G .b / beta) * Real.exp (-F .b) := by
      rw [← Real.exp_add]; congr 1 <;> ring
    rw [ha, hb]
  have psum : priorPolicy beta E G .a + priorPolicy beta E G .b = 1 := by
    simp [priorPolicy, softmax, sum_twoPolicy]; field_simp
  have qsum : posteriorPolicy beta E G F .a + posteriorPolicy beta E G F .b = 1 := by
    simp [posteriorPolicy, softmax, sum_twoPolicy]; field_simp
  have change : expectedGChange beta E G F =
      (posteriorPolicy beta E G F .a - priorPolicy beta E G .a) * (G .a - G .b) := by
    simp only [expectedGChange, sum_twoPolicy]
    have hd : posteriorPolicy beta E G F .b - priorPolicy beta E G .b =
        -(posteriorPolicy beta E G F .a - priorPolicy beta E G .a) := by linarith
    rw [hd]
    ring
  rw [change, pa, qa]
  constructor
  · intro hf
    have he : eb < ea := Real.exp_lt_exp.mpr (by change -F .b < -F .a; linarith)
    exact mul_neg_of_pos_of_neg (sub_pos.mpr ((binaryPrior_lt_posterior_iff hwa hwb hea heb).2 he))
      (sub_neg.mpr hG)
  · intro hf
    have he : ea < eb := Real.exp_lt_exp.mpr (by change -F .a < -F .b; linarith)
    exact mul_pos_of_neg_of_neg (sub_neg.mpr ((binaryPosterior_lt_prior_iff hwa hwb hea heb).2 he))
      (sub_neg.mpr hG)

theorem favoured_observation_raises_precision {betaPrior beta : ℝ} {E G F : TwoPolicy → ℝ}
    (fixed : IsPosteriorTemperature betaPrior beta E G F) (hE : ∀ p, 0 < E p)
    (hG : G .a < G .b) (hF : F .a < F .b) : beta < betaPrior :=
  (posterior_temperature_direction_lt fixed).2 ((two_policy_direction hE hG).1 hF)

theorem against_favoured_lowers_precision {betaPrior beta : ℝ} {E G F : TwoPolicy → ℝ}
    (fixed : IsPosteriorTemperature betaPrior beta E G F) (hE : ∀ p, 0 < E p)
    (hG : G .a < G .b) (hF : F .b < F .a) : betaPrior < beta :=
  (posterior_temperature_direction_gt fixed).2 ((two_policy_direction hE hG).2 hF)

def finiteSurprisal (p : ℝ) : ℝ := -Real.log p
theorem lower_prediction_has_higher_surprisal {pa pb : ℝ} (ha : 0 < pa) (h : pa < pb) :
    finiteSurprisal pb < finiteSurprisal pa := by
  simp only [finiteSurprisal]; linarith [Real.strictMonoOn_log ha (lt_trans ha h) h]

theorem interoceptive_reading_lowers_precision {betaPrior beta : ℝ}
    {E G : TwoPolicy → ℝ} {pa pb : ℝ}
    (fixed : IsPosteriorTemperature betaPrior beta E G
      (fun p => if p = .a then finiteSurprisal pa else finiteSurprisal pb))
    (hE : ∀ p, 0 < E p) (hG : G .a < G .b) (ha : 0 < pa) (hp : pa < pb) :
    betaPrior < beta := by
  apply against_favoured_lowers_precision fixed hE hG
  simpa using lower_prediction_has_higher_surprisal ha hp

theorem zero_prediction_surprisal_top {Reading : Type*} [Fintype Reading] [DecidableEq Reading]
    (P : Reading → ℝ) (i : Reading) (h : P i = 0) : R20Interoception.surprisal P i = ⊤ :=
  R20Interoception.zero_mass_surprisal_top h

structure TickRecord (Policy : Type*) where
  E : Policy → ℝ
  G : Policy → ℝ
  F : Policy → ℝ
  prior : Policy → ℝ
  posterior : Policy → ℝ
  betaPrior : ℝ
  betaPosterior : ℝ

def Conforms (r : TickRecord Policy) : Prop :=
  (∀ p, 0 < r.E p) ∧ 0 < r.betaPrior ∧
  IsPosteriorTemperature r.betaPrior r.betaPosterior r.E r.G r.F ∧
  r.prior = priorPolicy r.betaPosterior r.E r.G ∧
  r.posterior = posteriorPolicy r.betaPosterior r.E r.G r.F

def ConformsWithin (tol : ℝ) (r : TickRecord Policy) : Prop :=
  (∀ p, 0 < r.E p) ∧ 0 < r.betaPrior ∧ 0 < r.betaPosterior ∧
  |precisionError r.betaPrior r.betaPosterior r.E r.G r.F| ≤ tol ∧
  r.prior = priorPolicy r.betaPosterior r.E r.G ∧
  r.posterior = posteriorPolicy r.betaPosterior r.E r.G r.F

theorem conformsWithin_zero_iff (r : TickRecord Policy) : ConformsWithin 0 r ↔ Conforms r := by
  constructor
  · rintro ⟨hE, hp, hb, herr, hprior, hpost⟩
    have hz : precisionError r.betaPrior r.betaPosterior r.E r.G r.F = 0 := by
      exact abs_eq_zero.mp (le_antisymm herr (abs_nonneg _))
    exact ⟨hE, hp, ⟨hb, hz⟩, hprior, hpost⟩
  · rintro ⟨hE, hp, ⟨hb, hz⟩, hprior, hpost⟩
    exact ⟨hE, hp, hb, by simp [hz], hprior, hpost⟩

theorem unchanged_discriminating_refused {E G F : TwoPolicy → ℝ} {beta : ℝ}
    (hE : ∀ p, 0 < E p) (hG : G .a < G .b) (hF : F .b < F .a) :
    ¬ IsPosteriorTemperature beta beta E G F := by
  intro fixed; exact (lt_irrefl beta) (against_favoured_lowers_precision fixed hE hG hF)

theorem omitted_habit_prior_refused {E G : TwoPolicy → ℝ} {beta : ℝ}
    (recorded : TwoPolicy → ℝ) (printed : recorded = printedPrior beta G)
    (different : printedPrior beta G ≠ priorPolicy beta E G) :
    recorded ≠ priorPolicy beta E G := fun h => different (printed.symm.trans h)

end
end DarkTower.WarMachine.PrecisionFromObservation
