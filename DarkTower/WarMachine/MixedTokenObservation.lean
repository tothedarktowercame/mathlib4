import DarkTower.WarMachine.TokenObservation

/-!
# Mixed checkable/judgement observation rates

When only a subset of tokens is checkable, the full observation can still be
noisy on the remaining judgement tokens.  This file proves that marginalising
over those judgement-token reports leaves an exact observation on the
checkable subset.
-/

namespace DarkTower.WarMachine.MixedTokenObservation

open DarkTower.WarMachine.TokenObservation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An observation with positive likelihood cannot disagree with the state on
a token whose false-negative and false-positive rates are both zero. -/
theorem tokenLikelihood_eq_zero_of_checkable_mismatch
    (r : AdjudicationRates V) (checkable s o : Finset V)
    (hfn : ∀ v ∈ checkable, r.falseNeg v = 0)
    (hfp : ∀ v ∈ checkable, r.falsePos v = 0)
    (hmismatch : o ∩ checkable ≠ s ∩ checkable) :
    tokenLikelihood r s o = 0 := by
  have hex : ∃ v : V, v ∈ checkable ∧ ((v ∈ s ∧ v ∉ o) ∨ (v ∉ s ∧ v ∈ o)) := by
    by_contra h
    apply hmismatch
    ext v
    simp only [Finset.mem_inter]
    by_cases hc : v ∈ checkable
    · have hs_iff_ho : v ∈ s ↔ v ∈ o := by
        constructor
        · intro hs
          by_contra ho
          exact h ⟨v, hc, Or.inl ⟨hs, ho⟩⟩
        · intro ho
          by_contra hs
          exact h ⟨v, hc, Or.inr ⟨hs, ho⟩⟩
      tauto
    · simp [hc]
  obtain ⟨v, hc, hv | hv⟩ := hex
  · exact Finset.prod_eq_zero (Finset.mem_univ v) (by
      simp only [if_pos hv.1, if_neg hv.2, hfn v hc])
  · exact Finset.prod_eq_zero (Finset.mem_univ v) (by
      simp only [if_neg hv.1, if_pos hv.2, hfp v hc])

/-- **Mixed-rates marginal theorem.**  Rates need vanish only on `checkable`;
they may be arbitrary on the judgement tokens outside it.  After summing over
all full observations with a fixed checkable restriction, that restriction is
the true checkable part of the state with probability one. -/
theorem tokenLikelihood_checkable_marginal
    (r : AdjudicationRates V) (checkable s reported : Finset V)
    (hfn : ∀ v ∈ checkable, r.falseNeg v = 0)
    (hfp : ∀ v ∈ checkable, r.falsePos v = 0) :
    (∑ o : Finset V, if o ∩ checkable = reported then tokenLikelihood r s o else 0)
      = if reported = s ∩ checkable then 1 else 0 := by
  by_cases hreported : reported = s ∩ checkable
  · subst reported
    have hterm : ∀ o : Finset V,
        (if o ∩ checkable = s ∩ checkable then tokenLikelihood r s o else 0)
          = tokenLikelihood r s o := by
      intro o
      by_cases ho : o ∩ checkable = s ∩ checkable
      · simp [ho]
      · simp [ho, tokenLikelihood_eq_zero_of_checkable_mismatch r checkable s o hfn hfp ho]
    simp only [hterm, tokenLikelihood_colsum]
    simp
  · have hzero : ∀ o : Finset V,
        (if o ∩ checkable = reported then tokenLikelihood r s o else 0) = 0 := by
      intro o
      by_cases ho : o ∩ checkable = reported
      · have hmismatch : o ∩ checkable ≠ s ∩ checkable := by
          intro heq
          apply hreported
          exact ho.symm.trans heq
        simp [ho, tokenLikelihood_eq_zero_of_checkable_mismatch r checkable s o hfn hfp hmismatch]
      · simp [ho]
    simp [hzero, hreported]

end DarkTower.WarMachine.MixedTokenObservation
