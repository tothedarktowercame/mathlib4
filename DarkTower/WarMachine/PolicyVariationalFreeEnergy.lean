import DarkTower.WarMachine.Holes

/-!
# Per-policy variational free energy F(π) (registry `:policy-free-energy`)

Parr et al. 2022 eqs. B.1–B.2
(`futon2/holes/labs/wm-contract/refs/parr2022.txt:12499–12514`):
B.1: `P(o|π) = Σ_s P(o|s) P(s|π)`;
B.2: `F(π) = E_{Q(s|π)}[ln Q(s|π) − ln P(o,s|π)] ≥ −ln P(o|π)`, with
equality at `Q(s|π) = P(s|o,π)`.

Stated over an arbitrary finite state type `S` (instantiating `S` with a
trajectory type gives the multi-step case). The likelihood of the fixed
observed outcome is `lik s = P(o|s)`; the prior over states under π is
`prior s = P(s|π)`; the approximate posterior is `q s = Q(s|π)`. The joint
is `P(o,s|π) = lik s * prior s`. Zeros are represented faithfully in
`EReal` (as in `OutcomeRiskKL.lean`): F(π) = ⊤ when some state has positive
posterior mass and zero joint probability. Terms with `q s = 0` contribute
nothing.
-/

namespace DarkTower.WarMachine.PolicyVariationalFreeEnergy

open scoped Classical

variable {S : Type*} [Fintype S]

noncomputable section

/-! ## Definitions -/

/-- Parr B.1 (`refs/parr2022.txt:12499–12514`): the evidence
`P(o|π) = Σ_s P(o|s) P(s|π)`. -/
def evidence (lik prior : S → ℝ) : ℝ := ∑ s, lik s * prior s

/-- The states carrying positive posterior mass: the support the B.2 sum
effectively runs over. -/
def qsupport (q : S → ℝ) : Finset S := Finset.univ.filter fun s => 0 < q s

/-- Parr B.2: `F(π) = E_{Q(s|π)}[ln Q(s|π) − ln P(o,s|π)]`, valued in
`EReal`: `⊤` when a state with `0 < q s` has `P(o,s|π) = 0` (the expectation
of the log is infinite); otherwise the real sum over the q-support. -/
def variationalFreeEnergy (lik prior q : S → ℝ) : EReal :=
  if ∃ s, 0 < q s ∧ lik s * prior s = 0 then ⊤
  else ↑(∑ s ∈ qsupport q, q s * (Real.log (q s) - Real.log (lik s * prior s)))

/-- The exact posterior `P(s|o,π) = P(o|s) P(s|π) / P(o|π)` (Bayes from
B.1): the equality case of B.2. -/
def posterior (lik prior : S → ℝ) : S → ℝ :=
  fun s => lik s * prior s / evidence lik prior

/-! ## Support sums -/

theorem qsupport_pos (q : S → ℝ) {s : S} (hs : s ∈ qsupport q) : 0 < q s := by
  simpa [qsupport] using (Finset.mem_filter.mp hs).2

theorem sum_qsupport_eq (q : S → ℝ) (f : S → ℝ) (h0 : ∀ s, ¬ 0 < q s → f s = 0) :
    ∑ s ∈ qsupport q, f s = ∑ s, f s := by
  unfold qsupport
  exact Finset.sum_subset (Finset.filter_subset _ _)
    (fun s _ hs => h0 s (fun h => hs (Finset.mem_filter.mpr ⟨Finset.mem_univ s, h⟩)))

theorem sum_qsupport_le (q : S → ℝ) (f : S → ℝ) (hf : ∀ s, 0 ≤ f s) :
    ∑ s ∈ qsupport q, f s ≤ ∑ s, f s :=
  Finset.sum_le_sum_of_subset_of_nonneg (fun _ hs => Finset.filter_subset _ _ hs)
    (fun s _ _ => hf s)

/-- A nonnegative distribution sums to one on its own support. -/
theorem sum_qsupport (q : S → ℝ) (hq0 : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1) :
    ∑ s ∈ qsupport q, q s = 1 :=
  (sum_qsupport_eq q q fun s h => le_antisymm (le_of_not_gt h) (hq0 s)).trans hq1

/-! ## Posterior facts -/

theorem posterior_nonneg (lik prior : S → ℝ) (hlik : ∀ s, 0 ≤ lik s)
    (hp0 : ∀ s, 0 ≤ prior s) (hZ : 0 < evidence lik prior) :
    ∀ s, 0 ≤ posterior lik prior s :=
  fun s => div_nonneg (mul_nonneg (hlik s) (hp0 s)) hZ.le

theorem posterior_sum (lik prior : S → ℝ)
    (hZ : 0 < evidence lik prior) : ∑ s, posterior lik prior s = 1 := by
  have hsplit : ∀ s : S, posterior lik prior s
      = lik s * prior s * (evidence lik prior)⁻¹ :=
    fun s => div_eq_mul_inv _ _
  rw [Finset.sum_congr rfl (fun s _ => hsplit s), ← Finset.sum_mul]
  show evidence lik prior * (evidence lik prior)⁻¹ = 1
  exact mul_inv_cancel₀ hZ.ne'

/-! ## Gibbs term lemmas -/

/-- `0 ≤ x · log x − x + 1` for `0 < x` (from `1 − 1/x ≤ log x`). -/
theorem psi_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ x * Real.log x - x + 1 := by
  have h2 : 1 - x⁻¹ ≤ Real.log x := Real.one_sub_inv_le_log_of_pos hx
  have h4 : x * Real.log x - x + 1 = x * (Real.log x - (1 - x⁻¹)) := by
    calc x * Real.log x - x + 1 = x * Real.log x - x + x * x⁻¹ := by
          rw [mul_inv_cancel₀ hx.ne']
      _ = x * (Real.log x - (1 - x⁻¹)) := by
          have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
          field_simp
          ring
  rw [h4]
  exact mul_nonneg hx.le (sub_nonneg.mpr h2)

/-- The bound is attained only at `x = 1`. -/
theorem psi_eq_zero_iff {x : ℝ} (hx : 0 < x) :
    x * Real.log x - x + 1 = 0 ↔ x = 1 := by
  constructor
  · intro h0
    by_contra hne
    have hy : 0 < x⁻¹ := by positivity
    have hne' : x⁻¹ ≠ 1 := fun h => hne (inv_eq_one.mp h)
    have h1 : Real.log x⁻¹ < x⁻¹ - 1 := Real.log_lt_sub_one_of_pos hy hne'
    rw [Real.log_inv] at h1
    have h2 : -(x:ℝ) * Real.log x < x * (x⁻¹ - 1) := by
      calc -(x:ℝ) * Real.log x = x * (-Real.log x) := by ring
        _ < x * (x⁻¹ - 1) := mul_lt_mul_of_pos_left h1 hx
    have h3 : x * (x⁻¹ - 1) = 1 - x := by field_simp
    rw [h3] at h2
    nlinarith
  · intro h1
    rw [h1, Real.log_one]
    ring

/-- Per-term KL: `0 ≤ q · log (q/r) − (q − r)` for two positive reals. -/
theorem klTerm_nonneg {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    0 ≤ q * Real.log (q / r) - (q - r) := by
  have hx : 0 < q / r := by positivity
  have h1 : q * Real.log (q / r) - (q - r)
      = r * ((q / r) * Real.log (q / r) - (q / r) + 1) := by
    field_simp
    ring
  rw [h1]
  exact mul_nonneg hr.le (psi_nonneg hx)

/-- Per-term KL equality forces `q = r`. -/
theorem klTerm_eq_zero_iff {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    q * Real.log (q / r) - (q - r) = 0 ↔ q = r := by
  have hx : 0 < q / r := by positivity
  have h1 : q * Real.log (q / r) - (q - r)
      = r * ((q / r) * Real.log (q / r) - (q / r) + 1) := by
    field_simp
    ring
  rw [h1, mul_eq_zero, psi_eq_zero_iff hx, or_iff_right hr.ne']
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    exact div_self hr.ne'

/-! ## The KL form of B.2 -/

/-- The KL divergence of `q` from `r` over the q-support. -/
def klSum (q r : S → ℝ) : ℝ :=
  ∑ s ∈ qsupport q, q s * Real.log (q s / r s)

/-- On the finite branch, F(π) splits as `KL(q ‖ P(s|o,π)) − ln P(o|π)`. -/
theorem vfeReal_eq (lik prior q : S → ℝ) (hZ : 0 < evidence lik prior)
    (hq0 : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1)
    (hf : ∀ s, 0 < q s → 0 < lik s * prior s) :
    (∑ s ∈ qsupport q, q s * (Real.log (q s) - Real.log (lik s * prior s)))
      = klSum q (posterior lik prior) - Real.log (evidence lik prior) := by
  have h2 : ∀ s ∈ qsupport q,
      Real.log (lik s * prior s)
        = Real.log (lik s * prior s / evidence lik prior)
          + Real.log (evidence lik prior) := by
    intro s hs
    have hlp : 0 < lik s * prior s := hf s (qsupport_pos q hs)
    have hprod' : lik s * prior s
        = lik s * prior s / evidence lik prior * evidence lik prior := by field_simp
    have hlog := Real.log_mul (div_pos hlp hZ).ne' hZ.ne'
    rw [← hprod'] at hlog
    exact hlog
  have h3 : ∀ s ∈ qsupport q,
      q s * (Real.log (q s) - Real.log (lik s * prior s))
      = q s * Real.log (q s / (lik s * prior s / evidence lik prior))
        - q s * Real.log (evidence lik prior) := by
    intro s hs
    have hq : 0 < q s := qsupport_pos q hs
    have hr : 0 < lik s * prior s / evidence lik prior :=
      div_pos (hf s hq) hZ
    rw [h2 s hs, Real.log_div hq.ne' hr.ne']
    ring
  rw [Finset.sum_congr rfl h3, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_qsupport q hq0 hq1, one_mul]
  rfl

/-- Gibbs' inequality: `KL(q ‖ r) ≥ 0` for normalized nonnegative `q`, `r`
with `r` positive wherever `q` is. -/
theorem klSum_nonneg (q r : S → ℝ) (hq0 : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1)
    (hr0 : ∀ s, 0 ≤ r s) (hr1 : ∑ s, r s = 1) (hsup : ∀ s, 0 < q s → 0 < r s) :
    0 ≤ klSum q r := by
  have hsum : ∑ s ∈ qsupport q, (q s - r s) ≤ klSum q r :=
    Finset.sum_le_sum (fun s hs =>
      sub_nonneg.mp (klTerm_nonneg (qsupport_pos q hs) (hsup s (qsupport_pos q hs))))
  have hq : ∑ s ∈ qsupport q, q s = 1 := sum_qsupport q hq0 hq1
  have hr : ∑ s ∈ qsupport q, r s ≤ 1 := (sum_qsupport_le q r hr0).trans_eq hr1
  have hsub : ∑ s ∈ qsupport q, (q s - r s)
      = ∑ s ∈ qsupport q, q s - ∑ s ∈ qsupport q, r s := Finset.sum_sub_distrib _ _
  rw [hsub, hq] at hsum
  have hpos : (0:ℝ) ≤ 1 - ∑ s ∈ qsupport q, r s := by linarith
  linarith

/-- `KL(q ‖ r) = 0` exactly when the two distributions coincide pointwise. -/
theorem klSum_eq_zero_iff (q r : S → ℝ) (hq0 : ∀ s, 0 ≤ q s)
    (hq1 : ∑ s, q s = 1) (hr0 : ∀ s, 0 ≤ r s) (hr1 : ∑ s, r s = 1)
    (hsup : ∀ s, 0 < q s → 0 < r s) :
    klSum q r = 0 ↔ ∀ s, q s = r s := by
  have hqsup : ∑ s ∈ qsupport q, q s = 1 := sum_qsupport q hq0 hq1
  have hslacknonneg : ∀ s ∈ qsupport q,
      0 ≤ q s * Real.log (q s / r s) - (q s - r s) := fun s hs =>
    klTerm_nonneg (qsupport_pos q hs) (hsup s (qsupport_pos q hs))
  have hsplit : klSum q r = ∑ s ∈ qsupport q, (q s - r s)
      + ∑ s ∈ qsupport q, (q s * Real.log (q s / r s) - (q s - r s)) := by
    unfold klSum
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  constructor
  · intro h
    have hdiffnonneg : 0 ≤ ∑ s ∈ qsupport q, (q s - r s) := by
      have hr : ∑ s ∈ qsupport q, r s ≤ 1 :=
        (sum_qsupport_le q r hr0).trans_eq hr1
      have hsub : ∑ s ∈ qsupport q, (q s - r s)
          = ∑ s ∈ qsupport q, q s - ∑ s ∈ qsupport q, r s :=
        Finset.sum_sub_distrib _ _
      rw [hsub, hqsup]
      linarith
    have hsumslack : 0 ≤ ∑ s ∈ qsupport q,
        (q s * Real.log (q s / r s) - (q s - r s)) :=
      Finset.sum_nonneg hslacknonneg
    rw [hsplit] at h
    have hz1 : ∑ s ∈ qsupport q, (q s - r s) = 0 := by linarith
    have hz2 : ∑ s ∈ qsupport q, (q s * Real.log (q s / r s) - (q s - r s)) = 0 := by
      linarith
    have hterms : ∀ s ∈ qsupport q, q s = r s := by
      intro s hs
      exact (klTerm_eq_zero_iff (qsupport_pos q hs)
        (hsup s (qsupport_pos q hs))).mp
        ((Finset.sum_eq_zero_iff_of_nonneg hslacknonneg).mp hz2 s hs)
    have hcompl : ∀ s, s ∉ qsupport q → r s = 0 := by
      intro s hs
      have hcomplsum : ∑ t ∈ (qsupport q)ᶜ, r t = 0 := by
        have hboth : ∑ t ∈ qsupport q, r t + ∑ t ∈ (qsupport q)ᶜ, r t
            = ∑ t, r t := Finset.sum_add_sum_compl (qsupport q) r
        have hsup1 : ∑ t ∈ qsupport q, r t = 1 := by
          rw [← hqsup, Finset.sum_congr rfl (fun t ht => hterms t ht)]
        rw [hr1, hsup1] at hboth
        linarith
      exact ((Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hr0 t)).mp
        hcomplsum) s (Finset.mem_compl.mpr hs)
    intro s
    by_cases hs : s ∈ qsupport q
    · exact hterms s hs
    · have hqs : q s = 0 :=
        le_antisymm (le_of_not_gt (fun h => hs (by
          simp only [qsupport, Finset.mem_filter, Finset.mem_univ, h, and_self])))
          (hq0 s)
      rw [hqs, hcompl s hs]
  · intro h
    have hfilter : ∀ s ∈ qsupport q, q s * Real.log (q s / r s) = 0 := by
      intro s hs
      rw [← h s, div_self (qsupport_pos q hs).ne', Real.log_one, mul_zero]
    unfold klSum
    rw [Finset.sum_congr rfl hfilter, Finset.sum_const_zero]

/-! ## The B.2 theorems -/

/-- The B.2 bound: `F(π) ≥ −ln P(o|π)` whenever the outcome is possible
under π (Gibbs' inequality). -/
theorem vfe_ge_neg_log_evidence (lik prior q : S → ℝ) (hlik : ∀ s, 0 ≤ lik s)
    (hp0 : ∀ s, 0 ≤ prior s) (_hp1 : ∑ s, prior s = 1) (hq0 : ∀ s, 0 ≤ q s)
    (hq1 : ∑ s, q s = 1) (hZ : 0 < evidence lik prior) :
    (↑(-Real.log (evidence lik prior)) : EReal) ≤ variationalFreeEnergy lik prior q := by
  unfold variationalFreeEnergy
  by_cases htop : ∃ s, 0 < q s ∧ lik s * prior s = 0
  · rw [if_pos htop]
    exact le_top
  · rw [if_neg htop]
    have hf : ∀ s, 0 < q s → 0 < lik s * prior s := by
      intro s hqs
      by_contra hc
      exact htop ⟨s, hqs, le_antisymm (le_of_not_gt hc)
        (mul_nonneg (hlik s) (hp0 s))⟩
    have hsup : ∀ s, 0 < q s → 0 < posterior lik prior s :=
      fun s h => div_pos (hf s h) hZ
    have hkl : 0 ≤ klSum q (posterior lik prior) :=
      klSum_nonneg q (posterior lik prior) hq0 hq1
        (posterior_nonneg lik prior hlik hp0 hZ)
        (posterior_sum lik prior hZ) hsup
    rw [vfeReal_eq lik prior q hZ hq0 hq1 hf]
    exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- Equality in B.2 at the exact posterior:
`F(π) = −ln P(o|π)` for `Q(s|π) = P(s|o,π)`. -/
theorem vfe_posterior_eq (lik prior : S → ℝ) (hlik : ∀ s, 0 ≤ lik s)
    (hp0 : ∀ s, 0 ≤ prior s) (_hp1 : ∑ s, prior s = 1)
    (hZ : 0 < evidence lik prior) :
    variationalFreeEnergy lik prior (posterior lik prior)
      = ↑(-Real.log (evidence lik prior)) := by
  have hlp_pos : ∀ s, 0 < posterior lik prior s → 0 < lik s * prior s := by
    intro s hpos
    have hsplit : lik s * prior s
        = posterior lik prior s * evidence lik prior := by
      unfold posterior
      field_simp
    rw [hsplit]
    exact mul_pos hpos hZ
  have htopneg : ¬ ∃ s, 0 < posterior lik prior s ∧ lik s * prior s = 0 := by
    rintro ⟨s, hpos, hzero⟩
    have hprod : lik s * prior s = posterior lik prior s * evidence lik prior := by
      unfold posterior
      field_simp
    rw [hzero] at hprod
    exact absurd hprod.symm (mul_pos hpos hZ).ne'
  unfold variationalFreeEnergy
  rw [if_neg htopneg]
  have hterm : ∀ s ∈ qsupport (posterior lik prior),
      posterior lik prior s * (Real.log (posterior lik prior s)
        - Real.log (lik s * prior s))
      = posterior lik prior s * (-Real.log (evidence lik prior)) := by
    intro s hs
    have hq : 0 < posterior lik prior s := qsupport_pos _ hs
    have hlp : 0 < lik s * prior s := hlp_pos s hq
    have hlogq : Real.log (posterior lik prior s)
        = Real.log (lik s * prior s) - Real.log (evidence lik prior) := by
      have hdef : posterior lik prior s
          = (lik s * prior s) / evidence lik prior := rfl
      rw [hdef, Real.log_div hlp.ne' hZ.ne']
    rw [hlogq]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    sum_qsupport (posterior lik prior) (posterior_nonneg lik prior hlik hp0 hZ)
      (posterior_sum lik prior hZ), one_mul]

/-- The equality characterization of B.2: `F(π) = −ln P(o|π)` if and only if
`Q(s|π)` is the exact posterior `P(s|o,π)` — the argmin statement. -/
theorem vfe_eq_neg_log_evidence_iff (lik prior q : S → ℝ)
    (hlik : ∀ s, 0 ≤ lik s) (hp0 : ∀ s, 0 ≤ prior s) (hp1 : ∑ s, prior s = 1)
    (hq0 : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1)
    (hZ : 0 < evidence lik prior) :
    variationalFreeEnergy lik prior q = ↑(-Real.log (evidence lik prior))
      ↔ ∀ s, q s = posterior lik prior s := by
  constructor
  · intro h
    have hfin : ¬ ∃ s, 0 < q s ∧ lik s * prior s = 0 := by
      intro htop
      rw [variationalFreeEnergy, if_pos htop] at h
      exact EReal.coe_ne_top _ h.symm
    have hf : ∀ s, 0 < q s → 0 < lik s * prior s := by
      intro s hqs
      by_contra hc
      exact hfin ⟨s, hqs, le_antisymm (le_of_not_gt hc)
        (mul_nonneg (hlik s) (hp0 s))⟩
    have hsup : ∀ s, 0 < q s → 0 < posterior lik prior s :=
      fun s hs => div_pos (hf s hs) hZ
    rw [variationalFreeEnergy, if_neg hfin] at h
    have hreal : (∑ s ∈ qsupport q,
        q s * (Real.log (q s) - Real.log (lik s * prior s)))
        = -Real.log (evidence lik prior) := EReal.coe_injective h
    have hklz : klSum q (posterior lik prior) = 0 := by
      have hd := vfeReal_eq lik prior q hZ hq0 hq1 hf
      rw [hd] at hreal
      linarith
    exact (klSum_eq_zero_iff q (posterior lik prior) hq0 hq1
      (posterior_nonneg lik prior hlik hp0 hZ)
      (posterior_sum lik prior hZ) hsup).mp hklz
  · intro h
    rw [show q = posterior lik prior from funext h]
    exact vfe_posterior_eq lik prior hlik hp0 hp1 hZ

/-- An impossible outcome: if `P(o|π) = 0` then F(π) = ⊤ for every
normalized posterior `q`. -/
theorem vfe_eq_top_of_impossible (lik prior q : S → ℝ) (hlik : ∀ s, 0 ≤ lik s)
    (hp0 : ∀ s, 0 ≤ prior s) (hq0 : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1)
    (hZ : evidence lik prior = 0) :
    variationalFreeEnergy lik prior q = ⊤ := by
  have hqpos : ∃ s, 0 < q s := by
    by_contra hall
    push Not at hall
    have hzs : ∑ s, q s = 0 :=
      Finset.sum_eq_zero (fun s _ => le_antisymm (hall s) (hq0 s))
    rw [hzs] at hq1
    exact zero_ne_one hq1
  obtain ⟨s, hqs⟩ := hqpos
  have hlp0 : lik s * prior s = 0 := by
    have hsum0 : ∑ t, lik t * prior t = 0 := hZ
    have hnonneg : ∀ t, 0 ≤ lik t * prior t :=
      fun t => mul_nonneg (hlik t) (hp0 t)
    exact ((Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hnonneg t)).mp
      hsum0) s (Finset.mem_univ s)
  rw [variationalFreeEnergy, if_pos ⟨s, hqs, hlp0⟩]

/-! ## Fixtures over Bool states -/

section Fixtures

/-- Fixture likelihood: the outcome is certain on `true`, impossible on
`false`. -/
def likF : Bool → ℝ := fun b => if b then 1 else 0

/-- Fixture prior: uniform on `{true, false}`. -/
def priorF : Bool → ℝ := fun _ => 1 / 2

theorem likF_nonneg : ∀ s, 0 ≤ likF s := by
  intro s; cases s <;> norm_num [likF]

theorem priorF_nonneg : ∀ s, 0 ≤ priorF s := by
  intro s; norm_num [priorF]

theorem priorF_sum : ∑ s, priorF s = 1 := by simp [priorF]

theorem evidenceF : evidence likF priorF = 1 / 2 := by
  simp [evidence, likF, priorF]

theorem evidenceF_pos : 0 < evidence likF priorF := by
  rw [evidenceF]; norm_num

/-- Fixture (a): evidence 1/2 and `q` = posterior give `F = ln 2`. -/
theorem fixtureF_posterior :
    variationalFreeEnergy likF priorF (posterior likF priorF)
      = ↑(Real.log 2) := by
  rw [vfe_posterior_eq likF priorF likF_nonneg priorF_nonneg priorF_sum
    evidenceF_pos, evidenceF,
    show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]

/-- Fixture (b): posterior mass on the impossible state `false`
(likelihood 0) gives `F = ⊤`. -/
theorem fixtureF_impossible :
    variationalFreeEnergy likF priorF (fun _ => 1 / 2) = ⊤ := by
  rw [variationalFreeEnergy, if_pos ⟨false, by norm_num,
    by norm_num [likF, priorF]⟩]

end Fixtures

end

end PolicyVariationalFreeEnergy
