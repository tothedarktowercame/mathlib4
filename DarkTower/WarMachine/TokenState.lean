import Mathlib
import DarkTower.WarMachine.PolicyRollout

/-!
# WM-02: tactical token state and observed q0 (design P2 and P4)

For a target, `V` is a finite type of tokens: the want-signature tokens plus the
patterns' consumes (IF + HOWEVER) and produces (THEN) tokens. A tactical state
is the set of established tokens, `TokenState V := Finset V`.

`observedBelief s₀` is the point mass at the observed token state `s₀` from the
target's record. When the record fixes the state exactly, q₀ is this point
mass; the declared prior `D` is used only when there is no record (SPEC
§2: "after observed data, prediction begins with declared current inferred
beliefs q₀ (D only at initialization)").

`independentBelief p` is adjudication uncertainty: each token is established
independently with probability `p v`.

`coverage want s = |want ∩ s| / |want|` is want-signature coverage; target
discharge is `coverage = 1`, i.e. `want ⊆ s`.
-/

namespace DarkTower.WarMachine.TokenState

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A tactical state: the set of established tokens. -/
abbrev TokenState (V : Type*) [Fintype V] [DecidableEq V] := Finset V

/-- `Finset V` is a finite type (Mathlib instance). -/
example : Fintype (TokenState V) := inferInstance

/-! ## Observed belief: point mass at the observed token state -/

/-- The point mass at the observed token state `s₀`. -/
def observedBelief (s₀ : TokenState V) : TokenState V → ℝ :=
  fun s => if s = s₀ then 1 else 0

theorem observedBelief_nonneg (s₀ : TokenState V) (s : TokenState V) :
    0 ≤ observedBelief s₀ s := by
  unfold observedBelief
  by_cases h : s = s₀ <;> simp [h]

theorem observedBelief_sum (s₀ : TokenState V) :
    ∑ s : TokenState V, observedBelief s₀ s = (1:ℝ) := by
  simp [observedBelief]

/-! ## Want-signature coverage -/

/-- Want-signature coverage: the fraction of want tokens established in `s`.
Target discharge is `coverage = 1`. -/
noncomputable def coverage (want : Finset V) (hwant : want.Nonempty) (s : TokenState V) : ℝ :=
  (want ∩ s).card / want.card

theorem coverage_nonneg (want : Finset V) (hwant : want.Nonempty) (s : TokenState V) :
    0 ≤ coverage want hwant s :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem coverage_le_one (want : Finset V) (hwant : want.Nonempty) (s : TokenState V) :
    coverage want hwant s ≤ 1 := by
  refine (div_le_one (Nat.cast_pos.mpr hwant.card_pos)).mpr ?_
  exact Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)

theorem coverage_eq_one_iff (want : Finset V) (hwant : want.Nonempty) (s : TokenState V) :
    coverage want hwant s = 1 ↔ want ⊆ s := by
  rw [coverage, div_eq_iff (by positivity), one_mul]
  constructor
  · intro h
    have hcard : (want ∩ s).card = want.card := by exact_mod_cast h
    have hint : want ∩ s = want :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcard])
    intro v hv
    have h' : v ∈ want ∩ s := by rw [hint]; exact hv
    exact (Finset.mem_inter.mp h').2
  · intro hsub
    have hint : want ∩ s = want := by
      ext v
      rw [Finset.mem_inter]
      exact ⟨fun hv => hv.1, fun hv => ⟨hv, hsub hv⟩⟩
    rw [hint]

theorem coverage_mono (want : Finset V) (hwant : want.Nonempty) {s s' : TokenState V}
    (h : s ⊆ s') : coverage want hwant s ≤ coverage want hwant s' := by
  have hb : (0:ℝ) < want.card := by positivity
  have hsub2 : want ∩ s ⊆ want ∩ s' := by
    intro v hv
    have hv' := Finset.mem_inter.mp hv
    exact Finset.mem_inter.mpr ⟨hv'.1, h hv'.2⟩
  have h2 : ((want ∩ s).card : ℝ) ≤ ((want ∩ s').card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hsub2)
  have hrw : ((want ∩ s').card : ℝ)
      = ((want ∩ s).card : ℝ) + (((want ∩ s').card : ℝ) - ((want ∩ s).card : ℝ)) := by ring
  have hd : (0:ℝ) ≤ (((want ∩ s').card : ℝ) - ((want ∩ s).card : ℝ)) / want.card :=
    div_nonneg (sub_nonneg.mpr h2) hb.le
  rw [coverage, coverage, hrw, add_div]
  linarith

/-! ## Independent belief: adjudication uncertainty -/

/-- Adjudication uncertainty: each token is established independently with
probability `p v`; a state `s` has probability the product over tokens. -/
def independentBelief (p : V → ℝ) (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) : TokenState V → ℝ :=
  fun s => ∏ v, if v ∈ s then p v else 1 - p v

theorem independentBelief_nonneg (p : V → ℝ) (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (s : TokenState V) : 0 ≤ independentBelief p hp s := by
  refine Finset.prod_nonneg fun v _ => ?_
  by_cases hv : v ∈ s
  · simp only [independentBelief, if_pos hv]
    exact (hp v).1
  · simp only [independentBelief, if_neg hv]
    exact sub_nonneg.mpr (hp v).2

/-- Membership as a Boolean function, and its inverse: the bridge between
`tactical states` and `V → Bool`. -/
private def toBoolFun (s : Finset V) : V → Bool := fun v => decide (v ∈ s)

private def ofBoolFun (h : V → Bool) : Finset V := Finset.univ.filter (fun v => h v = true)

private theorem ofBoolFun_toBoolFun (s : Finset V) : ofBoolFun (toBoolFun s) = s := by
  ext v
  simp [ofBoolFun, toBoolFun]

private theorem toBoolFun_ofBoolFun (h : V → Bool) : toBoolFun (ofBoolFun h) = h := by
  funext v
  cases hv : h v <;> simp [toBoolFun, ofBoolFun, hv]

/-- Tactical states are in bijection with `V → Bool` membership functions. -/
private def stateBoolEquiv : Finset V ≃ (V → Bool) where
  toFun := toBoolFun
  invFun := ofBoolFun
  left_inv := ofBoolFun_toBoolFun
  right_inv := toBoolFun_ofBoolFun

theorem independentBelief_sum (p : V → ℝ) (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) :
    ∑ s : TokenState V, independentBelief p hp s = (1:ℝ) := by
  classical
  have key1 : ∑ s : TokenState V, independentBelief p hp s
      = ∑ h : V → Bool, ∏ v, if h v then p v else 1 - p v := by
    refine Fintype.sum_equiv stateBoolEquiv _ _ fun s => ?_
    show (∏ v, if v ∈ s then p v else 1 - p v)
        = ∏ x, if toBoolFun s x = true then p x else 1 - p x
    simp only [toBoolFun, decide_eq_true_eq]
  have step2 : (∑ h : V → Bool, ∏ v, if h v then p v else 1 - p v)
      = ∏ v, ∑ b : Bool, if b then p v else 1 - p v :=
    (Fintype.prod_sum (fun (v : V) (b : Bool) => if b then p v else 1 - p v)).symm
  rw [key1, step2]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [Fintype.sum_bool]
  simp

theorem independentBelief_eq_observedBelief (s₀ : TokenState V) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (hpp : ∀ v, p v = if v ∈ s₀ then 1 else 0)
    (s : TokenState V) : independentBelief p hp s = observedBelief s₀ s := by
  by_cases h : s = s₀
  · subst h
    have h1 : independentBelief p hp s = 1 := Finset.prod_eq_one fun v _ => by
      by_cases hv : v ∈ s <;> simp [independentBelief, hpp v, hv]
    rw [h1]
    simp [observedBelief]
  · have hdis : ∃ v : V, (v ∈ s ∧ v ∉ s₀) ∨ (v ∉ s ∧ v ∈ s₀) := by
      by_contra hcon
      apply h
      apply Finset.ext
      intro v
      by_cases h1 : v ∈ s <;> by_cases h2 : v ∈ s₀
      · exact ⟨fun _ => h2, fun _ => h1⟩
      · exact absurd ⟨v, Or.inl ⟨h1, h2⟩⟩ hcon
      · exact absurd ⟨v, Or.inr ⟨h1, h2⟩⟩ hcon
      · exact ⟨fun hv => absurd hv h1, fun hv => absurd hv h2⟩
    obtain ⟨v, hv | hv⟩ := hdis
    · have hz : independentBelief p hp s = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v) (by simp [independentBelief, hpp v, hv])
      rw [hz, observedBelief, if_neg h]
    · have hz : independentBelief p hp s = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v) (by simp [independentBelief, hpp v, hv])
      rw [hz, observedBelief, if_neg h]

/-! ## Fixture: V = Fin 3, concrete numbers -/

section Fixture

private def fwant : Finset (Fin 3) := {0, 1}

private def fne : Finset (Fin 3) := {1, 2}

theorem fixture_fwant_nonempty : fwant.Nonempty := by decide

theorem fixture_coverage_half : coverage fwant fixture_fwant_nonempty fne = 1 / 2 := by
  have h : fwant ∩ fne = {1} := by decide
  rw [coverage, h]
  norm_num [fwant]

theorem fixture_coverage_full : coverage fwant fixture_fwant_nonempty {0, 1} = 1 := by
  rw [coverage_eq_one_iff]
  intro v hv
  simp only [fwant, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  omega

theorem fixture_observedBelief :
    observedBelief fne fne = 1 ∧ observedBelief fne fwant = 0 := by
  constructor
  · simp [observedBelief, fne]
  · have hne : fwant ≠ fne := by decide
    simp [observedBelief, hne]

end Fixture

end DarkTower.WarMachine.TokenState
