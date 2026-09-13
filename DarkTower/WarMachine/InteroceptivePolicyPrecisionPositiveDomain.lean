import Mathlib
import DarkTower.WarMachine.MachineTemperature
import DarkTower.WarMachine.PolicyPosterior

/-!
# Positive-domain root ordering for proposed interoceptive policy precision

This module weakens the bounded refinement's all-real assumptions to the
domain the variational policy law actually admits: positive beta.  Definitions
are restated locally because the proposal module has no built olean; explicit
correspondence is proved where an imported canonical definition exists and is
otherwise pinned as source text by the companion specification receipt.
-/
namespace DarkTower.WarMachine.InteroceptivePolicyPrecisionPositiveDomain

open DarkTower.WarMachine.MachineTemperature

def PosteriorRoot (priorRate : ℝ) (evidenceDelta : ℝ → ℝ) (beta : ℝ) : Prop :=
  beta = priorRate + evidenceDelta beta

noncomputable def appliedGamma (beta : ℝ) : ℝ := 1 / beta

/-- The local reciprocal is definitionally the canonical machine gamma. -/
theorem appliedGamma_eq_machineGamma (beta : ℝ) :
    appliedGamma beta = machineGamma beta := rfl

/-- Positive-domain version of the conditional ordering theorem.  Boundedness
and continuity are required only on `beta > 0`; the IVT interval constructed
by the proof lies wholly inside that domain. -/
theorem increasedRateLowersGammaAtUniquePositiveRootOn
    {delta : ℝ → ℝ} {bound c1 c2 b1 : ℝ}
    (hcont : ContinuousOn delta (Set.Ioi 0))
    (hbound : ∀ b, 0 < b → |delta b| ≤ bound)
    (hb1pos : 0 < b1)
    (hb1root : PosteriorRoot c1 delta b1)
    (hrates : c1 < c2)
    (hunique : ∀ ⦃x y : ℝ⦄,
      0 < x → PosteriorRoot c2 delta x →
      0 < y → PosteriorRoot c2 delta y → x = y) :
    ∃ b2, PosteriorRoot c2 delta b2 ∧ b1 < b2 ∧
      appliedGamma b2 < appliedGamma b1 ∧
      ∀ ⦃b : ℝ⦄, 0 < b → PosteriorRoot c2 delta b → b = b2 := by
  let f : ℝ → ℝ := fun b => b - delta b
  let upper : ℝ := max (b1 + 1) (c2 + bound + 1)
  have hb1u : b1 ≤ upper := by
    have : b1 + 1 ≤ upper := le_max_left _ _
    linarith
  have hinterior : Set.Icc b1 upper ⊆ Set.Ioi (0 : ℝ) := by
    intro b hb
    exact lt_of_lt_of_le hb1pos hb.1
  have hfcont : ContinuousOn f (Set.Icc b1 upper) :=
    continuousOn_id.sub (hcont.mono hinterior)
  have hb1f : f b1 = c1 := by
    dsimp [f, PosteriorRoot] at hb1root ⊢
    linarith
  have hupperpos : 0 < upper := lt_of_lt_of_le hb1pos hb1u
  have hub : bound < upper - c2 := by
    have hle : c2 + bound + 1 ≤ upper := le_max_right _ _
    linarith
  have hdeltaUpper : delta upper ≤ bound :=
    le_trans (le_abs_self (delta upper)) (hbound upper hupperpos)
  have hfu : c2 < f upper := by
    dsimp [f]
    linarith
  have hc2mem : c2 ∈ Set.Icc (f b1) (f upper) := by
    constructor
    · rw [hb1f]
      exact hrates.le
    · exact hfu.le
  obtain ⟨b2, hb2mem, hb2f⟩ :=
    (intermediate_value_Icc hb1u hfcont) hc2mem
  have hb1b2le : b1 ≤ b2 := hb2mem.1
  have hb2root : PosteriorRoot c2 delta b2 := by
    dsimp [f] at hb2f
    dsimp [PosteriorRoot]
    linarith
  have hb1b2 : b1 < b2 := by
    refine lt_of_le_of_ne hb1b2le ?_
    intro heq
    subst b2
    have : c1 = c2 := by rw [← hb1f, hb2f]
    exact (ne_of_lt hrates) this
  have hb2pos : 0 < b2 := lt_trans hb1pos hb1b2
  refine ⟨b2, hb2root, hb1b2, one_div_lt_one_div_of_lt hb1pos hb1b2, ?_⟩
  intro b hbpos hbroot
  exact hunique hbpos hbroot hb2pos hb2root

#print axioms appliedGamma_eq_machineGamma
#print axioms increasedRateLowersGammaAtUniquePositiveRootOn

end DarkTower.WarMachine.InteroceptivePolicyPrecisionPositiveDomain
