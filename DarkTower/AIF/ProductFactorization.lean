import DarkTower.WarMachine.TokenObservation
import DarkTower.WarMachine.PolicyHorizon

/-!
# Product factorization — the acceptance instrument for the sparse
non-degenerate evaluator

The A kernel is a product of independent per-token Bernoullis
(`TokenObservation.tokenLikelihood`), so with real (non-zero) rates the
G quantities have linear-cost closed forms over the token universe:

* **Ambiguity**: the row entropy of the observation kernel is the sum of
  per-token binary entropies (`rowEntropy_tokenLikelihood`). claude-4
  checked this numerically against exact enumeration 2026-09-18
  (n = 3, 6, 10; deltas ≤ 2e-14); this module replaces the spot-check
  with a proof, valid for ALL rates in [0,1] — including the exact-0
  checkable class of the mixed kernel.
* **Risk**: the Gibbs sum between two product distributions is the sum
  of per-token Bernoulli KL terms (`klSum_product`), for an interior
  preference (every `c v` strictly between 0 and 1 — the `zeroed = ∅`
  precondition: `log-preference-fn` with empty zeroed IS such a product,
  `c v = σ(w_v)`). `prodB_pos` shows an interior product preference is
  everywhere positive, so `stepRisk`'s `⊤` guard is vacuous on this
  domain.

Enumeration over `2^|V|` observation sets appears in these statements
only as the LEFT-hand side; the right-hand sides are `O(|V|)` sums. This
is what discharges the `:judgement-rates-not-supported-at-scale` refusal:
the identity-A reduction was the cost of computing naively, not a
constraint of the model (audit ledger, observation-model declaration,
futon2 `ad2139a5`).
-/

namespace DarkTower.AIF

open Real
open DarkTower.WarMachine.TokenObservation
open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.PolicyHorizon

variable {V : Type*} [DecidableEq V]

/-- The product-Bernoulli mass of an observation set `s`, over the index
finset `F`: each token is reported with its own probability `p v`,
independently. `tokenLikelihood r s` is exactly this with
`p = obsP r s` and `F = univ`. -/
def prodB (p : V → ℝ) (F : Finset V) (s : Finset V) : ℝ :=
  ∏ v ∈ F, (if v ∈ s then p v else 1 - p v)

theorem prodB_nonneg {p : V → ℝ} {F : Finset V}
    (hp : ∀ v ∈ F, 0 ≤ p v ∧ p v ≤ 1) (s : Finset V) : 0 ≤ prodB p F s := by
  refine Finset.prod_nonneg fun v hv => ?_
  by_cases h : v ∈ s
  · simpa [h] using (hp v hv).1
  · simp only [if_neg h]
    linarith [(hp v hv).2]

/-- An interior product distribution is everywhere positive — with
`p = σ(w)` this is why an empty `zeroed` makes `stepRisk`'s infinite
guard vacuous. -/
theorem prodB_pos {p : V → ℝ} {F : Finset V}
    (hp : ∀ v ∈ F, 0 < p v ∧ p v < 1) (s : Finset V) : 0 < prodB p F s := by
  refine Finset.prod_pos fun v hv => ?_
  by_cases h : v ∈ s
  · simpa [h] using (hp v hv).1
  · simp only [if_neg h]
    linarith [(hp v hv).2]

private theorem prodB_insert_of_notMem {p : V → ℝ} {a : V} {F t : Finset V}
    (ha : a ∉ F) (hat : a ∉ t) :
    prodB p (insert a F) t = (1 - p a) * prodB p F t := by
  unfold prodB
  rw [Finset.prod_insert ha, if_neg hat]

private theorem prodB_insert_insert {p : V → ℝ} {a : V} {F t : Finset V}
    (ha : a ∉ F) :
    prodB p (insert a F) (insert a t) = p a * prodB p F t := by
  unfold prodB
  rw [Finset.prod_insert ha, if_pos (Finset.mem_insert_self a t)]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  simp [Finset.mem_insert, hva]

/-- Normalization: the product-Bernoulli masses over the powerset sum
to 1 — for any `p` (each factor contributes `p v + (1 − p v)`). -/
theorem sum_prodB (p : V → ℝ) (F : Finset V) :
    ∑ s ∈ F.powerset, prodB p F s = 1 := by
  induction F using Finset.induction_on with
  | empty => simp [prodB]
  | @insert a F ha ih =>
      rw [Finset.sum_powerset_insert ha]
      have h1 : ∀ t ∈ F.powerset,
          prodB p (insert a F) t = (1 - p a) * prodB p F t := fun t ht =>
        prodB_insert_of_notMem ha fun hat => ha (Finset.mem_powerset.mp ht hat)
      have h2 : ∀ t ∈ F.powerset,
          prodB p (insert a F) (insert a t) = p a * prodB p F t := fun t _ =>
        prodB_insert_insert ha
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2,
        ← Finset.mul_sum, ← Finset.mul_sum, ih]
      ring

private theorem negMulLog_mul' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog (x * y) = y * negMulLog x + x * negMulLog y := by
  rcases hx.eq_or_lt with h | hx0
  · simp [← h]
  rcases hy.eq_or_lt with h | hy0
  · simp [← h]
  unfold Real.negMulLog
  rw [Real.log_mul (ne_of_gt hx0) (ne_of_gt hy0)]
  ring

/-- **Entropy factorization**: the Shannon entropy of a product-Bernoulli
distribution is the sum of the per-token binary entropies. Valid on the
whole closed cube — boundary tokens (the checkable class, rates exactly
0) contribute `binEntropy ∈ {0}` and nothing else, so the mixed kernel
is covered. -/
theorem sum_negMulLog_prodB (p : V → ℝ) (F : Finset V)
    (hp : ∀ v ∈ F, 0 ≤ p v ∧ p v ≤ 1) :
    ∑ s ∈ F.powerset, negMulLog (prodB p F s) = ∑ v ∈ F, binEntropy (p v) := by
  revert hp
  induction F using Finset.induction_on with
  | empty => intro _; simp [prodB]
  | @insert a F ha ih =>
      intro hp
      have hpa := hp a (Finset.mem_insert_self a F)
      have hpF : ∀ v ∈ F, 0 ≤ p v ∧ p v ≤ 1 := fun v hv =>
        hp v (Finset.mem_insert_of_mem hv)
      have hw : ∀ t : Finset V, 0 ≤ prodB p F t := prodB_nonneg hpF
      rw [Finset.sum_powerset_insert ha]
      have h1 : ∀ t ∈ F.powerset,
          negMulLog (prodB p (insert a F) t)
            = prodB p F t * negMulLog (1 - p a)
              + (1 - p a) * negMulLog (prodB p F t) := by
        intro t ht
        rw [prodB_insert_of_notMem ha
            (fun hat => ha (Finset.mem_powerset.mp ht hat)),
          negMulLog_mul' (by linarith [hpa.2]) (hw t)]
      have h2 : ∀ t ∈ F.powerset,
          negMulLog (prodB p (insert a F) (insert a t))
            = prodB p F t * negMulLog (p a)
              + p a * negMulLog (prodB p F t) := by
        intro t _
        rw [prodB_insert_insert ha, negMulLog_mul' hpa.1 (hw t)]
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2,
        Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
        sum_prodB, ih hpF, Finset.sum_insert ha,
        binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      ring

/-- One Gibbs/KL summand, with the `0 · log 0 = 0` convention carried by
the multiplication. `klTerm p c + klTerm (1−p) (1−c)` is the KL
divergence of `Bernoulli p` from `Bernoulli c`. -/
noncomputable def klTerm (x y : ℝ) : ℝ := x * Real.log (x / y)

private theorem klTerm_mul {x a y b : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hy : 0 < y) (hb : 0 < b) :
    klTerm (x * a) (y * b) = a * klTerm x y + x * klTerm a b := by
  rcases hx.eq_or_lt with h | hx0
  · simp [klTerm, ← h]
  rcases ha.eq_or_lt with h | ha0
  · simp [klTerm, ← h]
  unfold klTerm
  rw [← div_mul_div_comm,
    Real.log_mul (ne_of_gt (div_pos hx0 hy)) (ne_of_gt (div_pos ha0 hb))]
  ring

/-- **Risk factorization** (generic form): the Gibbs sum between two
product-Bernoulli distributions is the sum of per-token Bernoulli KL
terms. `p` may touch the boundary (checkable tokens, point-mass
marginals); `q` must be interior — the `zeroed = ∅` precondition on C. -/
theorem sum_klTerm_prodB (p q : V → ℝ) (F : Finset V)
    (hp : ∀ v ∈ F, 0 ≤ p v ∧ p v ≤ 1) (hq : ∀ v ∈ F, 0 < q v ∧ q v < 1) :
    ∑ s ∈ F.powerset, klTerm (prodB p F s) (prodB q F s)
      = ∑ v ∈ F, (klTerm (p v) (q v) + klTerm (1 - p v) (1 - q v)) := by
  revert hp hq
  induction F using Finset.induction_on with
  | empty => intro _ _; simp [prodB, klTerm]
  | @insert a F ha ih =>
      intro hp hq
      have hpa := hp a (Finset.mem_insert_self a F)
      have hqa := hq a (Finset.mem_insert_self a F)
      have hpF : ∀ v ∈ F, 0 ≤ p v ∧ p v ≤ 1 := fun v hv =>
        hp v (Finset.mem_insert_of_mem hv)
      have hqF : ∀ v ∈ F, 0 < q v ∧ q v < 1 := fun v hv =>
        hq v (Finset.mem_insert_of_mem hv)
      have hw : ∀ t : Finset V, 0 ≤ prodB p F t := prodB_nonneg hpF
      have hz : ∀ t : Finset V, 0 < prodB q F t := prodB_pos hqF
      rw [Finset.sum_powerset_insert ha]
      have h1 : ∀ t ∈ F.powerset,
          klTerm (prodB p (insert a F) t) (prodB q (insert a F) t)
            = prodB p F t * klTerm (1 - p a) (1 - q a)
              + (1 - p a) * klTerm (prodB p F t) (prodB q F t) := by
        intro t ht
        have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
        rw [prodB_insert_of_notMem ha hat, prodB_insert_of_notMem ha hat,
          klTerm_mul (by linarith [hpa.2]) (hw t) (by linarith [hqa.2]) (hz t)]
      have h2 : ∀ t ∈ F.powerset,
          klTerm (prodB p (insert a F) (insert a t))
              (prodB q (insert a F) (insert a t))
            = prodB p F t * klTerm (p a) (q a)
              + p a * klTerm (prodB p F t) (prodB q F t) := by
        intro t _
        rw [prodB_insert_insert ha, prodB_insert_insert ha,
          klTerm_mul hpa.1 (hw t) hqa.1 (hz t)]
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2,
        Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
        sum_prodB, ih hpF hqF, Finset.sum_insert ha]
      ring

/-! ## Bridges to the deployed observation model -/

section Bridges

variable [Fintype V]

/-- The per-token report probability of the observation kernel at state
`s`: an established token is reported unless missed; an absent one only
if hallucinated. claude-4's `p_v` (2026-09-18). -/
def obsP (r : AdjudicationRates V) (s : Finset V) : V → ℝ :=
  fun v => if v ∈ s then 1 - r.falseNeg v else r.falsePos v

omit [Fintype V] in
theorem obsP_mem (r : AdjudicationRates V) (s : Finset V) (v : V) :
    0 ≤ obsP r s v ∧ obsP r s v ≤ 1 := by
  unfold obsP
  by_cases h : v ∈ s
  · have hm := Set.mem_Icc.mp (r.falseNeg_mem v)
    simp only [if_pos h]
    constructor <;> linarith [hm.1, hm.2]
  · have hm := Set.mem_Icc.mp (r.falsePos_mem v)
    simp only [if_neg h]
    exact hm

/-- The deployed kernel IS the product-Bernoulli form. -/
theorem tokenLikelihood_eq_prodB (r : AdjudicationRates V) (s o : Finset V) :
    tokenLikelihood r s o = prodB (obsP r s) Finset.univ o := by
  unfold tokenLikelihood prodB obsP
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hs : v ∈ s <;> by_cases ho : v ∈ o <;> simp [hs, ho]

private theorem rowEntropy_eq_sum_negMulLog {S O U : Type*}
    [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (M : ForwardModel S O U) (s : S) :
    rowEntropy M s = ∑ o, negMulLog (M.A s o) := by
  unfold rowEntropy Real.negMulLog
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun o _ => by ring

/-- **The ambiguity acceptance theorem**: for a forward model whose
likelihood is the token observation kernel, the row entropy is the sum
of per-token binary entropies — an `O(|V|)` closed form for the quantity
whose naive computation enumerates `2^|V|` observation sets. -/
theorem rowEntropy_tokenLikelihood {U : Type*}
    (M : ForwardModel (Finset V) (Finset V) U) (r : AdjudicationRates V)
    (hA : ∀ s o, M.A s o = tokenLikelihood r s o) (s : Finset V) :
    rowEntropy M s = ∑ v, binEntropy (obsP r s v) := by
  rw [rowEntropy_eq_sum_negMulLog]
  calc ∑ o, negMulLog (M.A s o)
      = ∑ o ∈ (Finset.univ : Finset V).powerset,
          negMulLog (prodB (obsP r s) Finset.univ o) := by
        rw [Finset.powerset_univ]
        exact Finset.sum_congr rfl fun o _ => by
          rw [hA, tokenLikelihood_eq_prodB]
    _ = ∑ v, binEntropy (obsP r s v) :=
        sum_negMulLog_prodB _ _ fun v _ => obsP_mem r s v

/-- Ambiguity at any horizon step factorizes accordingly: belief-support
× universe work, no enumeration. -/
theorem stepAmbiguity_tokenLikelihood {U : Type*}
    (M : ForwardModel (Finset V) (Finset V) U) (r : AdjudicationRates V)
    (hA : ∀ s o, M.A s o = tokenLikelihood r s o) (σ : ℕ → U) (n : ℕ) :
    stepAmbiguity M σ n
      = ∑ s, rolloutState M σ n s * ∑ v, binEntropy (obsP r s v) := by
  unfold stepAmbiguity
  exact Finset.sum_congr rfl fun s _ => by
    rw [rowEntropy_tokenLikelihood M r hA s]

/-- **The risk acceptance theorem** (product-form predicted outcome vs an
interior product-form C): the Gibbs sum is the sum of per-token Bernoulli
KLs. The interior hypothesis on `c` is the `zeroed = ∅` precondition;
with it, `prodB_pos` makes `stepRisk`'s `⊤` guard vacuous. -/
theorem klSum_product (p c : V → ℝ)
    (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (hc : ∀ v, 0 < c v ∧ c v < 1) :
    ∑ o : Finset V, klTerm (prodB p Finset.univ o) (prodB c Finset.univ o)
      = ∑ v, (klTerm (p v) (c v) + klTerm (1 - p v) (1 - c v)) := by
  rw [← Finset.powerset_univ]
  exact sum_klTerm_prodB p c Finset.univ (fun v _ => hp v) (fun v _ => hc v)

end Bridges

end DarkTower.AIF
