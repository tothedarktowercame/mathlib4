import Mathlib
import DarkTower.WarMachine.PolicyRollout

/-!
# Categorical likelihood precision ζ of Parr, Pezzulo & Friston 2022 §B.2.4,
# stated

Joe's ruling P9 (2026-09-16): the War Machine is one categorical model, so the
`:precision` row is bound to the categorical likelihood precision ζ of Parr,
Pezzulo & Friston 2022, §B.2.4, eqs. B.14–B.19
(`refs/parr2022.txt:12720–12830`); the earlier Gaussian channel form
(`DarkTower.WarMachine.ChannelPrecision`, Buckley et al. 2017 eq. (84))
stays in the tree as legacy.

Domain: `A : S → O → ℝ` with every entry strictly positive (`0 < A s o`) —
required because `ln A` appears in eqs. B.18–B.19 — and each row summing to
one over `O`.
-/

namespace DarkTower.WarMachine.LikelihoodPrecision

open DarkTower.WarMachine.PolicyRollout

variable {S O U : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
  [Nonempty O]

/-! ### The precision-weighted likelihood (eq. B.18) -/

/-- The precision-weighted likelihood `o^ζ = σ(ζ ln A)`, column-wise
(Parr et al. 2022 eq. B.18, `refs/parr2022.txt:12820–12822`): the Gibbs
reweighting of `A` by the exponent `ζ`. -/
noncomputable def precisionLikelihood (ζ : ℝ) (A : S → O → ℝ) : S → O → ℝ :=
  fun s o => A s o ^ ζ / ∑ o', A s o' ^ ζ

/-- Eq. B.18 in softmax form: the reweighted column is
`exp (ζ · ln A) / Σ exp (ζ · ln A)`. -/
theorem precisionLikelihood_eq_softmax (ζ : ℝ) (A : S → O → ℝ)
    (Apos : ∀ s o, 0 < A s o) (s : S) (o : O) :
    precisionLikelihood ζ A s o
      = Real.exp (ζ * Real.log (A s o))
        / ∑ o', Real.exp (ζ * Real.log (A s o')) := by
  have h : ∀ o' : O, A s o' ^ ζ = Real.exp (ζ * Real.log (A s o')) := by
    intro o'
    rw [Real.rpow_def_of_pos (Apos s o') ζ, mul_comm]
  rw [precisionLikelihood, h o]
  congr 1
  exact Finset.sum_congr rfl (fun o' _ => h o')

theorem precisionLikelihood_pos (ζ : ℝ) (A : S → O → ℝ) (Apos : ∀ s o, 0 < A s o)
    (s : S) (o : O) : 0 < precisionLikelihood ζ A s o :=
  div_pos (Real.rpow_pos_of_pos (Apos s o) ζ)
    (Finset.sum_pos (fun o' _ => Real.rpow_pos_of_pos (Apos s o') ζ)
      Finset.univ_nonempty)

/-- Each reweighted row of `A` sums to one, for every real `ζ`. -/
theorem precisionLikelihood_sum (ζ : ℝ) (A : S → O → ℝ) (Apos : ∀ s o, 0 < A s o)
    (s : S) : ∑ o, precisionLikelihood ζ A s o = 1 := by
  have hden : 0 < ∑ o', A s o' ^ ζ :=
    Finset.sum_pos (fun o' _ => Real.rpow_pos_of_pos (Apos s o') ζ)
      Finset.univ_nonempty
  have key : ∑ o, A s o ^ ζ / ∑ o', A s o' ^ ζ = 1 := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hden)
  simpa only [precisionLikelihood] using key
/-- At `ζ = 1` the reweighting is the identity: `A_1 = A`. -/
theorem precisionLikelihood_one (A : S → O → ℝ) (Apos : ∀ s o, 0 < A s o)
    (hcol : ∀ s, ∑ o, A s o = 1) (s : S) (o : O) :
    precisionLikelihood 1 A s o = A s o := by
  have hden : ∑ o', A s o' ^ (1 : ℝ) = 1 := by
    simp only [Real.rpow_one]; exact hcol s
  simp only [precisionLikelihood, Real.rpow_one]
  rw [hcol s, div_one]

/-- At `ζ = 0` the reweighting is uniform: `1 / |O|` per entry. -/
theorem precisionLikelihood_zero (A : S → O → ℝ) (Apos : ∀ s o, 0 < A s o)
    (s : S) (o : O) :
    precisionLikelihood 0 A s o = 1 / (Fintype.card O : ℝ) := by
  simp only [precisionLikelihood, Real.rpow_zero, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

/-! ### Normalised predictions under the reweighted model -/

/-- A forward model whose likelihood matrix is the precision-weighted
`precisionLikelihood ζ A`; the transition `B` and initial belief `q₀` (with
their normalisation facts) are supplied by the caller. -/
noncomputable def preciseForwardModel (B : U → S → S → ℝ)
    (hBn : ∀ u s s', 0 ≤ B u s s') (hBs : ∀ u s, ∑ s', B u s s' = 1)
    (q₀ : S → ℝ) (hqn : ∀ s, 0 ≤ q₀ s) (hqs : ∑ s, q₀ s = 1)
    (ζ : ℝ) (A : S → O → ℝ) (Apos : ∀ s o, 0 < A s o) : ForwardModel S O U where
  B := B
  B_nonneg := hBn
  B_rowsum := hBs
  A := precisionLikelihood ζ A
  A_nonneg := fun s o => le_of_lt (precisionLikelihood_pos ζ A Apos s o)
  A_colsum := fun s => precisionLikelihood_sum ζ A Apos s
  q₀ := q₀
  q₀_nonneg := hqn
  q₀_sum := hqs

/-- Under `A_ζ`, the predictive outcome `Q(o|π)` is normalised
(`PolicyRollout.predictedOutcome_sum`). -/
theorem predictive_normalised (B : U → S → S → ℝ)
    (hBn : ∀ u s s', 0 ≤ B u s s') (hBs : ∀ u s, ∑ s', B u s s' = 1)
    (q₀ : S → ℝ) (hqn : ∀ s, 0 ≤ q₀ s) (hqs : ∑ s, q₀ s = 1)
    (ζ : ℝ) (A : S → O → ℝ) (Apos : ∀ s o, 0 < A s o)
    (π : ℕ → U) (n : ℕ) :
    ∑ o, predictedOutcome
        (preciseForwardModel B hBn hBs q₀ hqn hqs ζ A Apos) π n o = 1 :=
  predictedOutcome_sum _ π n

/-! ### The gamma prior and posterior over ζ (eqs. B.14, B.15, B.19) -/

/-- The gamma prior on a precision parameter, eq. B.14
(`refs/parr2022.txt:12750–12756`), parameterised by its rate `β > 0`. -/
structure PrecisionPrior where
  beta : ℝ
  beta_pos : 0 < beta

/-- The expected precision under the prior, eq. B.15
(`refs/parr2022.txt:12764–12766`): `ζ̄ = E_Q[ζ] = β_ζ⁻¹`. -/
noncomputable def expectedPrecision (p : PrecisionPrior) : ℝ := 1 / p.beta

theorem expectedPrecision_pos (p : PrecisionPrior) : 0 < expectedPrecision p :=
  one_div_pos.2 p.beta_pos

/-- Eq. B.19 (`refs/parr2022.txt:12824–12830`): the posterior sufficient
statistic at `∂_ζ F = 0`, with the index conventions of the equation made
explicit. The trial history is a finite `Fin T`-indexed family of pairs
`(o_τ, s_τ)` of an observed outcome vector `O → ℝ` and a predicted-state
vector `S → ℝ`; the precision-weighted prediction is
`o^ζ_τ o = Σ_s A_ζ s o · s_τ s` (eq. B.18), and the update is
`**β**_ζ = β_ζ + Σ_τ Σ_o Σ_s (o^ζ_τ o − o_τ o) · ln A s o · s_τ s`. -/
noncomputable def betaPosterior (prior : PrecisionPrior) (A : S → O → ℝ)
    {T : ℕ} (trial : Fin T → (O → ℝ) × (S → ℝ)) (ζ : ℝ) : ℝ :=
  prior.beta + ∑ τ : Fin T, ∑ o, ∑ s,
    ((∑ s', precisionLikelihood ζ A s' o * (trial τ).2 s') - (trial τ).1 o)
      * Real.log (A s o) * (trial τ).2 s

/-- An empty trial history (`T = 0`) leaves `β` unchanged. -/
theorem betaPosterior_nil (prior : PrecisionPrior) (A : S → O → ℝ) (ζ : ℝ) :
    betaPosterior prior A (T := 0) (fun _ => default) ζ = prior.beta := by
  simp [betaPosterior]

/-- If every observed outcome equals its precision-weighted prediction
(`o_τ = o^ζ_τ` at every trial and outcome), the surprise term vanishes and
`β` is unchanged. -/
theorem betaPosterior_no_surprise (prior : PrecisionPrior) (A : S → O → ℝ)
    {T : ℕ} (trial : Fin T → (O → ℝ) × (S → ℝ)) (ζ : ℝ)
    (h : ∀ τ, ∀ o, (∑ s', precisionLikelihood ζ A s' o * (trial τ).2 s')
      = (trial τ).1 o) :
    betaPosterior prior A trial ζ = prior.beta := by
  have hz : ∑ τ : Fin T, ∑ o, ∑ s,
      ((∑ s', precisionLikelihood ζ A s' o * (trial τ).2 s') - (trial τ).1 o)
        * Real.log (A s o) * (trial τ).2 s = 0 :=
    Finset.sum_eq_zero fun τ _ =>
      Finset.sum_eq_zero fun o _ =>
        Finset.sum_eq_zero fun s _ => by rw [h τ o]; ring
  rw [betaPosterior, hz, add_zero]

/-! ### Fixed-precision declaration -/

/-- A declared fixed precision: the model fixes `ζ = ζ₀` and never updates it
(no `betaPosterior` update is applied). -/
noncomputable def fixedLikelihood (ζ₀ : ℝ) (A : S → O → ℝ) : S → O → ℝ :=
  precisionLikelihood ζ₀ A
/-- A fixed precision of `ζ₀ = 1` is exactly the unweighted model `A`. -/
theorem fixedLikelihood_one (A : S → O → ℝ) (Apos : ∀ s o, 0 < A s o)
    (hcol : ∀ s, ∑ o, A s o = 1) : fixedLikelihood 1 A = A := by
  funext s o
  exact precisionLikelihood_one A Apos hcol s o

/-! ### Fixture (Bool/Bool, entries 3/4 and 1/4) -/

/-- A Boolean likelihood whose every row is `(1/4, 3/4)`. -/
noncomputable def fixtureA : Bool → Bool → ℝ := fun _ o => if o then 3 / 4 else 1 / 4

theorem fixtureA_pos (s o : Bool) : 0 < fixtureA s o := by
  rcases o <;> simp [fixtureA]

theorem fixtureA_colsum (s : Bool) : ∑ o, fixtureA s o = 1 := by
  simp [fixtureA]; norm_num

/-- At `ζ = 2` the reweighted column is exactly `(9/10, 1/10)`
((3/4)² = 9/16, (1/4)² = 1/16, total 10/16). -/
theorem fixture_precision_two (s : Bool) :
    precisionLikelihood 2 fixtureA s true = 9 / 10
      ∧ precisionLikelihood 2 fixtureA s false = 1 / 10 := by
  simp only [precisionLikelihood, fixtureA]
  norm_num

/-- At `ζ = 1` the fixture is unchanged. -/
theorem fixture_precision_one (s o : Bool) :
    precisionLikelihood 1 fixtureA s o = fixtureA s o :=
  precisionLikelihood_one fixtureA fixtureA_pos fixtureA_colsum s o

end DarkTower.WarMachine.LikelihoodPrecision
