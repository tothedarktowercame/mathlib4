import DarkTower.WarMachine.GTotalMarginalInvariance

/-!
# The target-grain G localises to the target's own tokens (PROOF-2a, H-G-target)

PROOF-2a (`futon2/holes/labs/wm-contract/PROOF-2a-THEOREM-draft-2026-09-24.md`,
Holes row H-G-target; packet `proof2/packets/H-G-TARGET-LEAN.md`) needs a
target-grain G for Clause T: the machine chooses a work target from a field
whose members have different token universes, so absolute G values across
targets are incommensurable. claude-10's read (futon2 99ee133e): take the
stack's universe to be the union of every target's tokens; an action on target
`t` changes only `t`'s part; every other target's terms are identical across
the actions and cancel; what remains is `ΔG_t`, the candidate's G against the
empty baseline, both over `t`'s own tokens.

This module states that claim with its hypotheses shown. Under a positive
PRODUCT-form preference the point-mass total G (risk + ambiguity) is a sum of
per-token terms (`GTotalMarginalInvariance.cross_term_product`). Partition the
tokens into the target's own `U` and the rest: an action that leaves the
rest's present-marginals at baseline changes only the `U` terms
(`deltaG_localises`), so two targets are comparable by their localised deltas
(`target_comparison`). The negative witness shows the localised delta is
WRONG by exactly the outside term when the action also moves a token outside
`U` — the receipt shape AR-40 exhibited, restated at target grain: a `:universe`
narrower than the tokens the action moved misreports the comparison.

Not in this module (recorded on the H-G-target row as open): a target with no
constructed candidate has no candidate law `q₁`, so its `ΔG` is a typed absence
on the record, not a number; and a prior over targets before any candidate
exists (part 2 of H-G-target) has no definition in any document.
-/

namespace DarkTower.WarMachine.Proof2.TargetGrainG

open DarkTower.WarMachine.GTotalMarginalInvariance

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- The product-form preference built from per-token present/absent weights. -/
def productPref (cIn cOut : V → ℝ) : Finset V → ℝ :=
  fun o => ∏ v, (if v ∈ o then cIn v else cOut v)

/-- Total mass of a law. -/
def mass (q : Finset V → ℝ) : ℝ := ∑ o : Finset V, q o

/-- The per-token term of the cross term: what token `v` contributes to
`−(risk + ambiguity)` under a product preference. -/
def tokenTerm (q : Finset V → ℝ) (cIn cOut : V → ℝ) (v : V) : ℝ :=
  margIn q v * Real.log (cIn v) + (mass q - margIn q v) * Real.log (cOut v)

/-- Point-mass total G: risk plus ambiguity against the product preference. -/
def totalG (q : Finset V → ℝ) (cIn cOut : V → ℝ) : ℝ :=
  risk q (productPref cIn cOut) + entropy q

/-- `ΔG` computed over a token set `U` ONLY: the candidate's tokens' terms
against the baseline's. This is what a constructor computes when it scores a
candidate and the empty baseline over the target's own `problem-tokens`. -/
def localDelta (U : Finset V) (q₁ q₂ : Finset V → ℝ) (cIn cOut : V → ℝ) : ℝ :=
  -∑ v ∈ U, (tokenTerm q₁ cIn cOut v - tokenTerm q₂ cIn cOut v)

theorem productPref_pos (cIn cOut : V → ℝ) (hIn : ∀ v, 0 < cIn v)
    (hOut : ∀ v, 0 < cOut v) (o : Finset V) : 0 < productPref cIn cOut o := by
  unfold productPref
  refine Finset.prod_pos fun v _ => ?_
  by_cases hv : v ∈ o
  · simpa [hv] using hIn v
  · simpa [hv] using hOut v

/-- **Total G is minus the sum of per-token terms** under a positive product
preference and a nonnegative law. -/
theorem totalG_eq_neg_sum_tokenTerm (q : Finset V → ℝ) (cIn cOut : V → ℝ)
    (hq : ∀ o, 0 ≤ q o) (hIn : ∀ v, 0 < cIn v) (hOut : ∀ v, 0 < cOut v) :
    totalG q cIn cOut = -∑ v : V, tokenTerm q cIn cOut v := by
  unfold totalG
  rw [risk_add_entropy q _ hq (productPref_pos cIn cOut hIn hOut)]
  unfold productPref
  rw [cross_term_product q cIn cOut hIn hOut]
  rfl

/-- **ΔG localises.** If the candidate law `q₁` and the baseline `q₂` have the
same total mass and the same present-marginal on every token OUTSIDE `U`, then
the difference of their total Gs is exactly the delta computed over `U`. The
outside terms are identical and cancel; nothing about them is assumed beyond
that equality. -/
theorem deltaG_localises (U : Finset V) (q₁ q₂ : Finset V → ℝ) (cIn cOut : V → ℝ)
    (hq₁ : ∀ o, 0 ≤ q₁ o) (hq₂ : ∀ o, 0 ≤ q₂ o)
    (hIn : ∀ v, 0 < cIn v) (hOut : ∀ v, 0 < cOut v)
    (hmass : mass q₁ = mass q₂)
    (hout : ∀ v, v ∉ U → margIn q₁ v = margIn q₂ v) :
    totalG q₁ cIn cOut - totalG q₂ cIn cOut = localDelta U q₁ q₂ cIn cOut := by
  rw [totalG_eq_neg_sum_tokenTerm q₁ cIn cOut hq₁ hIn hOut,
    totalG_eq_neg_sum_tokenTerm q₂ cIn cOut hq₂ hIn hOut]
  unfold localDelta
  have hsplit : ∀ q : Finset V → ℝ,
      ∑ v : V, tokenTerm q cIn cOut v
        = ∑ v ∈ U, tokenTerm q cIn cOut v + ∑ v ∈ Uᶜ, tokenTerm q cIn cOut v :=
    fun q => (Finset.sum_add_sum_compl U _).symm
  rw [hsplit q₁, hsplit q₂]
  have houtside : ∑ v ∈ Uᶜ, tokenTerm q₁ cIn cOut v = ∑ v ∈ Uᶜ, tokenTerm q₂ cIn cOut v := by
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv' : v ∉ U := Finset.mem_compl.mp hv
    unfold tokenTerm
    rw [hout v hv', hmass]
  rw [houtside, Finset.sum_sub_distrib]
  ring

/-- **Targets are comparable by their localised deltas.** Two targets with
token sets `U` and `U'`, actions `a` and `a'`, and one common baseline `b`:
when `a` leaves the marginals at `b`'s outside `U` and `a'` outside `U'`, the
difference of the actions' total Gs equals the difference of the two localised
deltas, each computed over its own target's tokens. This is the condition
under which Clause T may rank targets by `ΔG_t`. -/
theorem target_comparison (U U' : Finset V) (a a' b : Finset V → ℝ) (cIn cOut : V → ℝ)
    (ha : ∀ o, 0 ≤ a o) (ha' : ∀ o, 0 ≤ a' o) (hb : ∀ o, 0 ≤ b o)
    (hIn : ∀ v, 0 < cIn v) (hOut : ∀ v, 0 < cOut v)
    (hmass : mass a = mass b) (hmass' : mass a' = mass b)
    (hout : ∀ v, v ∉ U → margIn a v = margIn b v)
    (hout' : ∀ v, v ∉ U' → margIn a' v = margIn b v) :
    totalG a cIn cOut - totalG a' cIn cOut
      = localDelta U a b cIn cOut - localDelta U' a' b cIn cOut := by
  rw [← deltaG_localises U a b cIn cOut ha hb hIn hOut hmass hout,
    ← deltaG_localises U' a' b cIn cOut ha' hb hIn hOut hmass' hout']
  ring

/-! ## Negative witness: a delta over a universe narrower than what moved -/

/-- The general gap: whatever the marginals do, the true difference of total
Gs is the localised delta over `U` MINUS the outside tokens' term difference.
When the outside terms differ, `localDelta U` misreports by exactly that
amount. -/
theorem totalG_sub_eq_localDelta_sub_outside (U : Finset V) (q₁ q₂ : Finset V → ℝ)
    (cIn cOut : V → ℝ)
    (hq₁ : ∀ o, 0 ≤ q₁ o) (hq₂ : ∀ o, 0 ≤ q₂ o)
    (hIn : ∀ v, 0 < cIn v) (hOut : ∀ v, 0 < cOut v) :
    totalG q₁ cIn cOut - totalG q₂ cIn cOut
      = localDelta U q₁ q₂ cIn cOut
        - ∑ v ∈ Uᶜ, (tokenTerm q₁ cIn cOut v - tokenTerm q₂ cIn cOut v) := by
  rw [totalG_eq_neg_sum_tokenTerm q₁ cIn cOut hq₁ hIn hOut,
    totalG_eq_neg_sum_tokenTerm q₂ cIn cOut hq₂ hIn hOut]
  unfold localDelta
  rw [← Finset.sum_add_sum_compl U (tokenTerm q₁ cIn cOut),
    ← Finset.sum_add_sum_compl U (tokenTerm q₂ cIn cOut),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

/-- Baseline on two tokens: nothing present. -/
def bWit : Finset (Fin 2) → ℝ := fun o => if o = ∅ then 1 else 0

/-- An action declared on `U = {0}` that ALSO makes token 1 present: the law
puts all mass on `{0, 1}`. -/
def aWit : Finset (Fin 2) → ℝ := fun o => if o = Finset.univ then 1 else 0

theorem bWit_nonneg (o : Finset (Fin 2)) : 0 ≤ bWit o := by
  unfold bWit; split_ifs <;> norm_num

theorem aWit_nonneg (o : Finset (Fin 2)) : 0 ≤ aWit o := by
  unfold aWit; split_ifs <;> norm_num

theorem margIn_bWit (v : Fin 2) : margIn bWit v = 0 := by
  unfold margIn bWit
  refine Finset.sum_eq_zero fun o _ => ?_
  by_cases hv : v ∈ o
  · have hne : o ≠ ∅ := Finset.ne_empty_of_mem hv
    simp [hv, hne]
  · simp [hv]

theorem margIn_aWit (v : Fin 2) : margIn aWit v = 1 := by
  unfold margIn aWit
  rw [Finset.sum_eq_single Finset.univ]
  · simp
  · intro o _ ho
    simp [ho]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mass_bWit : mass bWit = 1 := by
  unfold mass bWit; simp

theorem mass_aWit : mass aWit = 1 := by
  unfold mass aWit; simp

/-- **The localised delta over `{0}` is wrong for the witness action**, by the
outside token's term: with `cIn 1 ≠ cOut 1` the action moved token 1 and the
delta over `{0}` does not see it. A receipt whose `:universe` is `{0}` for
this action would misreport its comparison against the baseline. -/
theorem localDelta_wrong_when_outside_moves (cIn cOut : Fin 2 → ℝ)
    (hIn : ∀ v, 0 < cIn v) (hOut : ∀ v, 0 < cOut v)
    (hne : cIn 1 ≠ cOut 1) :
    totalG aWit cIn cOut - totalG bWit cIn cOut ≠ localDelta {0} aWit bWit cIn cOut := by
  rw [totalG_sub_eq_localDelta_sub_outside {0} aWit bWit cIn cOut
    aWit_nonneg bWit_nonneg hIn hOut]
  intro h
  have hgap : ∑ v ∈ ({0} : Finset (Fin 2))ᶜ, (tokenTerm aWit cIn cOut v - tokenTerm bWit cIn cOut v) = 0 := by
    linarith
  have hcompl : (({0} : Finset (Fin 2))ᶜ) = {1} := by decide
  rw [hcompl, Finset.sum_singleton] at hgap
  unfold tokenTerm at hgap
  rw [margIn_aWit, margIn_bWit, mass_aWit, mass_bWit] at hgap
  have : Real.log (cIn 1) = Real.log (cOut 1) := by linarith
  exact hne (Real.log_injOn_pos (Set.mem_Ioi.mpr (hIn 1)) (Set.mem_Ioi.mpr (hOut 1)) this)

end

end DarkTower.WarMachine.Proof2.TargetGrainG
