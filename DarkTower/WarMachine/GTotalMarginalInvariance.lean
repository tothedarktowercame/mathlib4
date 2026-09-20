import DarkTower.WarMachine.MixtureJointSeparationWitness

/-!
# Total G under a point-mass state: risk/ambiguity cancellation

The A programme (futon2 `holes/labs/wm-contract/PLAN-a-programme-2026-09-20.md`,
point 4) records a control observed in the `coupling-sidebyside-2026-09-18`
enumeration: coupling increased risk and decreased ambiguity by the same
amount, so total G was unchanged — "a better A need not change every ranking."
This module proves the general fact behind that displayed-precision
coincidence, in the token-space vocabulary of the bounded enumeration route.

For a point-mass state belief the predicted observation law is the kernel row
`q = A(·|s₀)`, the ambiguity term is the entropy of `q`, and the risk term is
the Gibbs sum `∑ₒ q(o)·log(q(o)/C(o))`. Their sum telescopes to the cross
term `−∑ₒ q(o)·log C(o)`; when `C` is a PRODUCT over tokens, that cross term
depends only on `q`'s per-token marginals and total mass. Hence two
observation kernels with equal marginals — the coupled mixture and the
independent kernel of `MixtureJointSeparationWitness` in particular — yield
IDENTICAL total G against every positive product-form preference, while
splitting it into risk and ambiguity differently. Ranking invariance under
that hypothesis pair is legitimate, not vacuous; and per-token G sums remain
unlicensed for coupled kernels precisely because only the TOTAL enjoys this
invariance.

Queued-transcription item 1 (G under dependence: the cancellation control) of
`SPEC-a-model-conformance-2026-09-20.md`, first half. The dependence-correct
risk/ambiguity calculations for non-point-mass beliefs remain queued.
-/

namespace DarkTower.WarMachine.GTotalMarginalInvariance

open DarkTower.WarMachine.TokenObservation
open DarkTower.WarMachine.MixedTokenObservation
open DarkTower.WarMachine.MixtureJointSeparationWitness

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- Gibbs risk of an observation law `q` against preference `C` (finite
branch; `C` is assumed positive wherever used below). -/
def risk (q C : Finset V → ℝ) : ℝ :=
  ∑ o : Finset V, q o * Real.log (q o / C o)

/-- Shannon entropy of an observation law: the point-mass ambiguity term. -/
def entropy (q : Finset V → ℝ) : ℝ :=
  -∑ o : Finset V, q o * Real.log (q o)

/-- The probability that token `v` is reported PRESENT under law `q`. -/
def margIn (q : Finset V → ℝ) (v : V) : ℝ :=
  ∑ o : Finset V, if v ∈ o then q o else 0

/-- Pointwise telescope: `q·log(q/C) − q·log q = −q·log C` for nonnegative
`q` and positive `C` (both sides vanish at `q = 0`). -/
private theorem pointwise_telescope {q C : ℝ} (hq : 0 ≤ q) (hC : 0 < C) :
    q * Real.log (q / C) - q * Real.log q = -(q * Real.log C) := by
  rcases eq_or_lt_of_le hq with h | h
  · simp [← h]
  · rw [Real.log_div (ne_of_gt h) (ne_of_gt hC)]
    ring

/-- **Risk plus ambiguity is the cross term.** For a point-mass state the
total of risk and ambiguity against a positive preference is
`−∑ₒ q(o)·log C(o)` — the entropies cancel. -/
theorem risk_add_entropy (q C : Finset V → ℝ)
    (hq : ∀ o, 0 ≤ q o) (hC : ∀ o, 0 < C o) :
    risk q C + entropy q = -∑ o : Finset V, q o * Real.log (C o) := by
  unfold risk entropy
  calc ∑ o : Finset V, q o * Real.log (q o / C o)
        + -∑ o : Finset V, q o * Real.log (q o)
      = ∑ o : Finset V,
          (q o * Real.log (q o / C o) - q o * Real.log (q o)) := by
        rw [Finset.sum_sub_distrib]; ring
    _ = ∑ o : Finset V, -(q o * Real.log (C o)) :=
        Finset.sum_congr rfl fun o _ => pointwise_telescope (hq o) (hC o)
    _ = -∑ o : Finset V, q o * Real.log (C o) := by simp

/-- The cross term of a positive PRODUCT preference depends only on the
per-token marginals and the total mass of the observation law. -/
theorem cross_term_product (q : Finset V → ℝ) (cIn cOut : V → ℝ)
    (hIn : ∀ v, 0 < cIn v) (hOut : ∀ v, 0 < cOut v) :
    -∑ o : Finset V, q o * Real.log (∏ v, (if v ∈ o then cIn v else cOut v))
      = -∑ v : V, (margIn q v * Real.log (cIn v)
          + ((∑ o : Finset V, q o) - margIn q v) * Real.log (cOut v)) := by
  have hlog : ∀ o : Finset V,
      Real.log (∏ v, (if v ∈ o then cIn v else cOut v))
        = ∑ v : V, Real.log (if v ∈ o then cIn v else cOut v) := by
    intro o
    have hne : ∀ v ∈ (Finset.univ : Finset V),
        (if v ∈ o then cIn v else cOut v) ≠ 0 := by
      intro v _
      by_cases hv : v ∈ o
      · simpa [hv] using ne_of_gt (hIn v)
      · simpa [hv] using ne_of_gt (hOut v)
    exact Real.log_prod hne
  simp_rw [hlog, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  have hsplit : ∀ o : Finset V,
      q o * Real.log (if v ∈ o then cIn v else cOut v)
        = (if v ∈ o then q o else 0) * Real.log (cIn v)
          + (if v ∈ o then 0 else q o) * Real.log (cOut v) := by
    intro o
    by_cases hv : v ∈ o <;> simp [hv]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_mul]; simp [margIn]
  · rw [← Finset.sum_mul]
    congr 1
    unfold margIn
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun o _ => by by_cases hv : v ∈ o <;> simp [hv]

/-- **Total-G marginal invariance.** Two observation laws with equal total
mass and equal per-token marginals have identical risk-plus-ambiguity against
every positive product-form preference. The risk/ambiguity SPLIT may differ —
by exactly the entropy difference — but the total cannot. -/
theorem totalG_eq_of_marginals_eq (q₁ q₂ : Finset V → ℝ) (cIn cOut : V → ℝ)
    (hq₁ : ∀ o, 0 ≤ q₁ o) (hq₂ : ∀ o, 0 ≤ q₂ o)
    (hIn : ∀ v, 0 < cIn v) (hOut : ∀ v, 0 < cOut v)
    (hmass : ∑ o : Finset V, q₁ o = ∑ o : Finset V, q₂ o)
    (hmarg : ∀ v, margIn q₁ v = margIn q₂ v) :
    risk q₁ (fun o => ∏ v, (if v ∈ o then cIn v else cOut v)) + entropy q₁
      = risk q₂ (fun o => ∏ v, (if v ∈ o then cIn v else cOut v)) + entropy q₂ := by
  have hC : ∀ o : Finset V, 0 < ∏ v, (if v ∈ o then cIn v else cOut v) := by
    intro o
    refine Finset.prod_pos fun v _ => ?_
    by_cases hv : v ∈ o
    · simpa [hv] using hIn v
    · simpa [hv] using hOut v
  rw [risk_add_entropy q₁ _ hq₁ hC, risk_add_entropy q₂ _ hq₂ hC,
    cross_term_product q₁ cIn cOut hIn hOut,
    cross_term_product q₂ cIn cOut hIn hOut, hmass]
  simp_rw [hmarg]

/-! ## The witness pair: coupled and independent kernels, identical total G -/

/-- Present-marginals of the witness pair agree (its `marginalMiss` theorem,
turned around using equal total mass 1). -/
private theorem margIn_witness_eq (v : Fin 2) :
    margIn (mixtureLikelihood wMix rMix sBoth) v
      = margIn (tokenLikelihood rInd sBoth) v := by
  have hmix : ∑ o : Finset (Fin 2), mixtureLikelihood wMix rMix sBoth o = 1 :=
    mixtureLikelihood_colsum wMix rMix (by rw [Fintype.sum_bool]; norm_num [wMix]) sBoth
  have hind : ∑ o : Finset (Fin 2), tokenLikelihood rInd sBoth o = 1 :=
    tokenLikelihood_colsum rInd sBoth
  have key : ∀ L : Finset (Fin 2) → ℝ,
      margIn L v = (∑ o : Finset (Fin 2), L o) - marginalMiss L v := by
    intro L
    unfold margIn marginalMiss
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun o _ => by by_cases hv : v ∈ o <;> simp [hv]
  rw [key, key, hmix, hind, marginals_agree v]

/-- **The cancellation control, proven.** Against every positive product-form
preference, the coupled mixture and the independent kernel of the witness
yield identical total G (risk + ambiguity) — even though their joint laws
differ. A ranking by total G cannot distinguish them; only joint-sensitive
quantities can. -/
theorem witness_totalG_eq (cIn cOut : Fin 2 → ℝ)
    (hIn : ∀ v, 0 < cIn v) (hOut : ∀ v, 0 < cOut v) :
    risk (mixtureLikelihood wMix rMix sBoth)
        (fun o => ∏ v, (if v ∈ o then cIn v else cOut v))
      + entropy (mixtureLikelihood wMix rMix sBoth)
      = risk (tokenLikelihood rInd sBoth)
          (fun o => ∏ v, (if v ∈ o then cIn v else cOut v))
        + entropy (tokenLikelihood rInd sBoth) := by
  refine totalG_eq_of_marginals_eq _ _ cIn cOut
    (fun o => ?_) (fun o => tokenLikelihood_nonneg rInd sBoth o)
    hIn hOut ?_ margIn_witness_eq
  · exact Finset.sum_nonneg fun z _ =>
      mul_nonneg (by norm_num [wMix]) (tokenLikelihood_nonneg (rMix z) sBoth o)
  · rw [mixtureLikelihood_colsum wMix rMix (by rw [Fintype.sum_bool]; norm_num [wMix]) sBoth,
      tokenLikelihood_colsum rInd sBoth]

end

end DarkTower.WarMachine.GTotalMarginalInvariance

#print axioms DarkTower.WarMachine.GTotalMarginalInvariance.risk_add_entropy
#print axioms DarkTower.WarMachine.GTotalMarginalInvariance.cross_term_product
#print axioms DarkTower.WarMachine.GTotalMarginalInvariance.totalG_eq_of_marginals_eq
#print axioms DarkTower.WarMachine.GTotalMarginalInvariance.witness_totalG_eq
