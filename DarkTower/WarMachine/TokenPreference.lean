import Mathlib

/-! P6 preference family member: C over observed token states.

Design: `wm-walkthroughs/build-loop/closure/PROPOSAL-wm-model-design-2026-09-16.md`
(P6, approved by Joe 2026-09-16); specification side:
`futon2:holes/labs/wm-contract/SPEC-cascade-policy-semantics-2026-09-15.md`.

Cτ(o) ∝ exp(uτ(o)): utility rises with want-signature coverage and with the
presence of evidence tokens (checkable witnesses), never with their content.
Mass is exactly 0 only on ruled-zero outcome sets; the scale `lam` (nats per
unit of coverage) is a declared named parameter, not derived.

This module is a mathematical model, not a correspondence claim about the
live machine. Parameter acquisition and outcome interpretation are external.
-/

namespace DarkTower.WarMachine.TokenPreference

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- Declared preference specification over observed token states. -/
structure PreferenceSpec (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Want-signature tokens. -/
  want : Finset V
  want_nonempty : want.Nonempty
  /-- Evidence tokens: checkable witnesses; their content is never scored. -/
  evidence : Finset V
  /-- Declared scale in nats per unit of coverage; not derived. -/
  lam : ℝ
  lam_pos : 0 < lam
  /-- Declared evidence-presence scale. -/
  mu : ℝ
  mu_nonneg : 0 ≤ mu
  /-- Ruled-zero outcome sets: mass exactly 0, never smoothed. -/
  zeroed : Finset (Finset V)
  zeroed_proper : zeroed ≠ Finset.univ

namespace PreferenceSpec

variable (c : PreferenceSpec V)

/-- Coverage plus evidence presence. Content-blind by construction. -/
def utility (c : PreferenceSpec V) (o : Finset V) : ℝ :=
  c.lam * ((c.want ∩ o).card / c.want.card) + c.mu * (c.evidence ∩ o).card

/-- Normalizer over the non-ruled-zero outcomes. -/
def Z (c : PreferenceSpec V) : ℝ :=
  ∑ o' ∈ Finset.univ \ c.zeroed, Real.exp (utility c o')

/-- The preference distribution on observed token states. -/
def preference (c : PreferenceSpec V) (o : Finset V) : ℝ :=
  if o ∈ c.zeroed then 0 else Real.exp (utility c o) / Z c

theorem Z_pos (c : PreferenceSpec V) : 0 < Z c := by
  have hne : (Finset.univ \ c.zeroed).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact c.zeroed_proper
      (Finset.eq_univ_of_forall (fun x => (Finset.sdiff_eq_empty_iff_subset.mp h)
        (Finset.mem_univ x)))
  unfold Z
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) hne

theorem preference_nonneg (c : PreferenceSpec V) (o : Finset V) :
    0 ≤ preference c o := by
  by_cases h : o ∈ c.zeroed
  · simp [preference, h]
  · simp only [preference, if_neg h]
    exact div_nonneg (Real.exp_pos _).le (Z_pos c).le

theorem preference_sum (c : PreferenceSpec V) :
    ∑ o ∈ (Finset.univ : Finset (Finset V)), preference c o = 1 := by
  classical
  have hs : c.zeroed ⊆ (Finset.univ : Finset (Finset V)) := Finset.subset_univ _
  have hsplit : ∑ o ∈ (Finset.univ : Finset (Finset V)), preference c o
      = ∑ o ∈ Finset.univ \ c.zeroed, preference c o
        + ∑ o ∈ c.zeroed, preference c o :=
    (Finset.sum_sdiff hs).symm
  have hz : ∑ o ∈ c.zeroed, preference c o = 0 := by
    refine Finset.sum_eq_zero fun o ho => ?_
    simp [preference, ho]
  have hd : ∑ o ∈ Finset.univ \ c.zeroed, preference c o = 1 := by
    have hval : ∀ o ∈ Finset.univ \ c.zeroed,
        preference c o = Real.exp (utility c o) / Z c := by
      intro o ho
      simp [preference, (Finset.mem_sdiff.mp ho).2]
    rw [Finset.sum_congr rfl hval]
    have hZsum : ∑ o ∈ Finset.univ \ c.zeroed, Real.exp (utility c o) = Z c := rfl
    rw [← Finset.sum_div, hZsum, div_self (ne_of_gt (Z_pos c))]
  rw [hsplit, hz, hd]
  norm_num

theorem preference_pos_iff (c : PreferenceSpec V) (o : Finset V) :
    0 < preference c o ↔ o ∉ c.zeroed := by
  by_cases h : o ∈ c.zeroed
  · simp [preference, h]
  · simp only [preference, if_neg h]
    exact iff_of_true (div_pos (Real.exp_pos _) (Z_pos c)) h

theorem preference_eq_zero_iff (c : PreferenceSpec V) (o : Finset V) :
    preference c o = 0 ↔ o ∈ c.zeroed := by
  by_cases h : o ∈ c.zeroed
  · simp [preference, h]
  · simp only [preference, h, ite_false]
    exact ⟨fun hc => absurd hc (div_ne_zero (Real.exp_ne_zero _) (ne_of_gt (Z_pos c))),
      False.elim⟩

theorem preference_lt_of_utility_lt (c : PreferenceSpec V) {o o' : Finset V}
    (ho : o ∉ c.zeroed) (ho' : o' ∉ c.zeroed)
    (h : utility c o < utility c o') : preference c o < preference c o' := by
  simp only [preference, if_neg ho, if_neg ho']
  rw [div_lt_div_iff₀ (Z_pos c) (Z_pos c)]
  exact mul_lt_mul_of_pos_right (Real.exp_lt_exp.mpr h) (Z_pos c)

/-- Monotone in coverage: with equal evidence-presence counts, strictly less
want-signature progress is strictly dispreferred (stalling is not cheap). -/
theorem preference_lt_of_want_lt (c : PreferenceSpec V) {o o' : Finset V}
    (ho : o ∉ c.zeroed) (ho' : o' ∉ c.zeroed)
    (he : (c.evidence ∩ o).card = (c.evidence ∩ o').card)
    (hw : (c.want ∩ o).card < (c.want ∩ o').card) :
    preference c o < preference c o' := by
  refine preference_lt_of_utility_lt c ho ho' ?_
  have hW : (0:ℝ) < c.want.card := by exact_mod_cast c.want_nonempty.card_pos
  have hw' : ((c.want ∩ o).card : ℝ) < (c.want ∩ o').card := by exact_mod_cast hw
  have he' : ((c.evidence ∩ o).card : ℝ) = (c.evidence ∩ o').card := by
    exact_mod_cast he
  have hdiv : ((c.want ∩ o).card : ℝ) / c.want.card
      < (c.want ∩ o').card / c.want.card := (div_lt_div_iff₀ hW hW).2 (mul_lt_mul_of_pos_right hw' hW)
  have hmul := mul_lt_mul_of_pos_left hdiv c.lam_pos
  simp only [utility, he']
  linarith

/-- Content-blind evidence: two non-ruled-zero outcomes with equal coverage
and evidence-presence counts get equal preference; token content never
enters. -/
theorem preference_congr (c : PreferenceSpec V) {o o' : Finset V}
    (hw : (c.want ∩ o).card = (c.want ∩ o').card)
    (he : (c.evidence ∩ o).card = (c.evidence ∩ o').card)
    (hz : o ∈ c.zeroed ↔ o' ∈ c.zeroed) :
    preference c o = preference c o' := by
  by_cases h : o ∈ c.zeroed
  · simp [preference, h, hz.mp h]
  · have h' : o' ∉ c.zeroed := fun hc => h (hz.mpr hc)
    simp only [preference, if_neg h, if_neg h']
    have hw' : ((c.want ∩ o).card : ℝ) = (c.want ∩ o').card := by exact_mod_cast hw
    have he' : ((c.evidence ∩ o).card : ℝ) = (c.evidence ∩ o').card := by
      exact_mod_cast he
    simp only [utility, hw', he']

end PreferenceSpec

/-! ### Fixture: `V = Fin 3`

want = {0,1}, evidence = {2}, lam = 1, mu = 1, zeroed = ∅. The preference
chain is strict along the coverage/evidence ladder, and the fixture sums to 1. -/

namespace Fixture

open scoped BigOperators
open PreferenceSpec

/-- The fixture specification over `Fin 3`. -/
def c0 : PreferenceSpec (Fin 3) where
  want := {0, 1}
  want_nonempty := by decide
  evidence := {2}
  lam := 1
  mu := 1
  lam_pos := by norm_num
  mu_nonneg := by norm_num
  zeroed := ∅
  zeroed_proper := by decide

private theorem u_full : utility c0 {0,1,2} = 2 := by
  have h1 : (({0,1} : Finset (Fin 3)) ∩ {0,1,2}).card = 2 := by decide
  have h2 : (({2} : Finset (Fin 3)) ∩ {0,1,2}).card = 1 := by decide
  have hw : ({0,1} : Finset (Fin 3)).card = 2 := by decide
  simp only [utility, c0, h1, h2, hw]
  norm_num

private theorem u_01 : utility c0 {0,1} = 1 := by
  have h1 : (({0,1} : Finset (Fin 3)) ∩ {0,1}).card = 2 := by decide
  have h2 : (({2} : Finset (Fin 3)) ∩ {0,1}).card = 0 := by decide
  have hw : ({0,1} : Finset (Fin 3)).card = 2 := by decide
  simp only [utility, c0, h1, h2, hw]
  norm_num

private theorem u_0 : utility c0 {0} = 1 / 2 := by
  have h1 : (({0,1} : Finset (Fin 3)) ∩ {0}).card = 1 := by decide
  have h2 : (({2} : Finset (Fin 3)) ∩ {0}).card = 0 := by decide
  have hw : ({0,1} : Finset (Fin 3)).card = 2 := by decide
  simp only [utility, c0, h1, h2, hw]
  norm_num

private theorem u_empty : utility c0 ∅ = 0 := by
  have h1 : (({0,1} : Finset (Fin 3)) ∩ (∅ : Finset (Fin 3))).card = 0 := by decide
  have h2 : (({2} : Finset (Fin 3)) ∩ (∅ : Finset (Fin 3))).card = 0 := by decide
  simp only [utility, c0, h1, h2]
  norm_num

private theorem not_zeroed (o : Finset (Fin 3)) : o ∉ c0.zeroed := by
  simp [c0]

theorem fixture_lt_1 : preference c0 {0,1} < preference c0 {0,1,2} :=
  preference_lt_of_utility_lt c0 (not_zeroed _) (not_zeroed _)
    (by rw [u_01, u_full]; norm_num)

theorem fixture_lt_2 : preference c0 {0} < preference c0 {0,1} :=
  preference_lt_of_utility_lt c0 (not_zeroed _) (not_zeroed _)
    (by rw [u_0, u_01]; norm_num)

theorem fixture_lt_3 : preference c0 ∅ < preference c0 {0} :=
  preference_lt_of_utility_lt c0 (not_zeroed _) (not_zeroed _)
    (by rw [u_empty, u_0]; norm_num)

theorem fixture_chain :
    preference c0 {0,1,2} > preference c0 {0,1}
      ∧ preference c0 {0,1} > preference c0 {0}
      ∧ preference c0 {0} > preference c0 ∅ :=
  ⟨fixture_lt_1, fixture_lt_2, fixture_lt_3⟩

theorem fixture_sum : ∑ o ∈ (Finset.univ : Finset (Finset (Fin 3))),
    preference c0 o = 1 :=
  preference_sum c0

end Fixture

end

end DarkTower.WarMachine.TokenPreference

#print axioms DarkTower.WarMachine.TokenPreference.PreferenceSpec.Z_pos
#print axioms DarkTower.WarMachine.TokenPreference.PreferenceSpec.preference_sum
#print axioms DarkTower.WarMachine.TokenPreference.PreferenceSpec.preference_pos_iff
#print axioms DarkTower.WarMachine.TokenPreference.PreferenceSpec.preference_eq_zero_iff
#print axioms DarkTower.WarMachine.TokenPreference.PreferenceSpec.preference_lt_of_want_lt
#print axioms DarkTower.WarMachine.TokenPreference.PreferenceSpec.preference_congr
#print axioms DarkTower.WarMachine.TokenPreference.Fixture.fixture_chain
#print axioms DarkTower.WarMachine.TokenPreference.Fixture.fixture_sum
