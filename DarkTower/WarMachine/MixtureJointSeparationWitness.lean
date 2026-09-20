import DarkTower.WarMachine.MixedTokenObservation

/-!
# Witness: equal per-token marginals, distinct joint observation law

The A programme (futon2
`holes/labs/wm-contract/PLAN-a-programme-2026-09-20.md`, point 3) requires
WMC acceptance to test JOINT events, because a coupled and an independent
observation model can agree on every per-token marginal while disagreeing
on joint outcomes — the recorded enumeration run
(`coupling-sidebyside-2026-09-18`) exhibits a 469× joint gap at matched
marginals. This module proves the model-level fact behind that acceptance
rule on the smallest instance: two established tokens, an independent
kernel with per-token miss rate 1/2, and a half/half latent mixture of a
perfect observer and an always-miss observer. Both give every token a
marginal miss probability of 1/2; the probability that BOTH tokens are
missed is 1/4 under independence and 1/2 under the mixture. Matching
marginals therefore cannot certify an observation model; only joint
queries separate these two.
-/

namespace DarkTower.WarMachine.MixtureJointSeparationWitness

open DarkTower.WarMachine.TokenObservation
open DarkTower.WarMachine.MixedTokenObservation

noncomputable section

/-- Independent kernel: each token missed with probability 1/2, no false
positives. -/
def rInd : AdjudicationRates (Fin 2) where
  falseNeg := fun _ => (1 : ℝ) / 2
  falsePos := fun _ => 0
  falseNeg_mem := fun _ => ⟨by norm_num, by norm_num⟩
  falsePos_mem := fun _ => ⟨le_refl 0, by norm_num⟩

/-- Latent components: `true` is the perfect observer, `false` always
misses. No false positives in either component. -/
def rMix : Bool → AdjudicationRates (Fin 2) := fun z =>
  { falseNeg := fun _ => if z then 0 else 1
    falsePos := fun _ => 0
    falseNeg_mem := fun _ => by by_cases hz : z <;> simp [hz]
    falsePos_mem := fun _ => ⟨le_refl 0, by norm_num⟩ }

/-- Half/half mixing weight over the latent observer condition. -/
def wMix : Bool → ℝ := fun _ => (1 : ℝ) / 2

/-- Both tokens established. -/
def sBoth : Finset (Fin 2) := Finset.univ

/-- Marginal probability that token `v` is reported missing. -/
def marginalMiss (L : Finset (Fin 2) → ℝ) (v : Fin 2) : ℝ :=
  ∑ o : Finset (Fin 2), if v ∈ o then 0 else L o

private theorem ne_0_01 : ({0} : Finset (Fin 2)) ≠ ({0, 1} : Finset (Fin 2)) := by decide

private theorem ne_1_01 : ({1} : Finset (Fin 2)) ≠ ({0, 1} : Finset (Fin 2)) := by decide

private theorem univ_finset_fin2 :
    (Finset.univ : Finset (Finset (Fin 2)))
      = {∅, {0}, {1}, ({0, 1} : Finset (Fin 2))} := by decide

private theorem tokenLikelihood_fin2 (r : AdjudicationRates (Fin 2))
    (o : Finset (Fin 2)) :
    tokenLikelihood r sBoth o
      = (if (0 : Fin 2) ∈ o then 1 - r.falseNeg 0 else r.falseNeg 0)
        * (if (1 : Fin 2) ∈ o then 1 - r.falseNeg 1 else r.falseNeg 1) := by
  unfold tokenLikelihood sBoth
  rw [Fin.prod_univ_two]
  simp

/-- The independent law on the four outcomes: uniform 1/4. -/
theorem ind_values (o : Finset (Fin 2)) :
    tokenLikelihood rInd sBoth o = 1 / 4 := by
  rw [tokenLikelihood_fin2]
  by_cases h0 : (0 : Fin 2) ∈ o <;> by_cases h1 : (1 : Fin 2) ∈ o <;>
    simp [h0, h1, rInd] <;> norm_num

/-- The mixture law: mass 1/2 on all-missed, 1/2 on all-seen, 0 elsewhere. -/
theorem mix_values (o : Finset (Fin 2)) :
    mixtureLikelihood wMix rMix sBoth o
      = if o = ∅ then 1 / 2 else if o = ({0, 1} : Finset (Fin 2)) then 1 / 2 else 0 := by
  unfold mixtureLikelihood
  rw [Fintype.sum_bool]
  rw [tokenLikelihood_fin2, tokenLikelihood_fin2]
  have ho : o = ∅ ∨ o = {0} ∨ o = {1} ∨ o = ({0, 1} : Finset (Fin 2)) := by
    have := univ_finset_fin2 ▸ Finset.mem_univ o
    simpa using this
  rcases ho with h | h | h | h <;> subst h <;>
    simp [wMix, rMix, ne_0_01, ne_1_01]

/-- Equal marginals: every token is missed with probability 1/2 under both
laws. -/
theorem marginals_agree (v : Fin 2) :
    marginalMiss (mixtureLikelihood wMix rMix sBoth) v
      = marginalMiss (tokenLikelihood rInd sBoth) v := by
  unfold marginalMiss
  rw [univ_finset_fin2]
  fin_cases v <;>
    · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
      simp [mix_values, ind_values, ne_0_01, ne_1_01]
      norm_num

/-- Distinct joints: the all-missed outcome has probability 1/2 under the
mixture and 1/4 under independence. -/
theorem joints_differ :
    mixtureLikelihood wMix rMix sBoth ∅ ≠ tokenLikelihood rInd sBoth ∅ := by
  rw [mix_values, ind_values]
  norm_num

/-- **Joint separation at matched marginals.** There is a normalized latent
mixture and an independent kernel over the same tokens with identical
per-token miss marginals and different joint observation laws. Acceptance
criteria that compare only marginals cannot distinguish coupling from
independence. -/
theorem coupling_separates_only_jointly :
    (∀ v : Fin 2,
      marginalMiss (mixtureLikelihood wMix rMix sBoth) v
        = marginalMiss (tokenLikelihood rInd sBoth) v)
    ∧ mixtureLikelihood wMix rMix sBoth ∅ ≠ tokenLikelihood rInd sBoth ∅ :=
  ⟨marginals_agree, joints_differ⟩

end

end DarkTower.WarMachine.MixtureJointSeparationWitness

#print axioms DarkTower.WarMachine.MixtureJointSeparationWitness.coupling_separates_only_jointly
