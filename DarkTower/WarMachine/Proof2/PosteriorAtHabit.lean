import DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
import DarkTower.WarMachine.Proof2.EnactmentHabit

/-!
# The machine's posterior weights at the counted habit prior (W10, registry `:policy-posterior` ← `:enactment-habit`, R17→R6)

`PolicyPosteriorAtMachine.machineWeights` takes `habit : PolicyIndex → ℝ` as a free
binder. C4's `EnactmentHabit.habitPrior` (mathlib4 `8f5e11fe78`) is the counted E:
`(count + α)` normalised over the distinct menu entries, uniform with no data (through
`α = 1`), and a zero-count policy has mass `α / Z > 0`. Nothing applied the one to the
other, so the registry edge R17→R6 (E into the policy posterior) had the term in the
consumer's signature and no import behind it. This module is that application.

This is a sibling module and not an edit of `PolicyPosteriorAtMachine.lean`: that module
is W1/W1b's, already warranted and imported by W2–W5, and this one needs `EnactmentHabit`
(which imports `Holes`), which `PolicyPosteriorAtMachine` does not.

The menu is the policy list, `PolicyIndex := PolicyKey M P`. `habitPrior` needs a
non-empty menu (`hne`) and the Dirichlet concentration `α` (`Concentration`); both are
arguments here (the requisition's signature omitted `α`; `habitPrior` cannot be applied
without it). An EMPTY menu is `habitPrior`'s hypothesis failing (no distribution), so it
is an absence here (`HabitAbsence.emptyMenu`), not a default weight list.
-/

namespace DarkTower.WarMachine.Proof2.PosteriorAtHabit

open DarkTower.WarMachine
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
open DarkTower.WarMachine.Proof2.EnactmentHabit

noncomputable section

variable {M P : Type*} [DecidableEq M] [DecidableEq P]

/-- Why there are no weights at the counted habit. -/
inductive HabitAbsence where
  | emptyMenu

/-- E as a function of the policy: `habitPrior`'s mass at the key. -/
def habitAt (records : List (Record M P)) (c : Concentration)
    (menu : List (PolicyKey M P)) (hne : menu ≠ []) (k : PolicyKey M P) : ℝ :=
  (habitPrior records c menu hne).mass () k

open Classical in
/-- **The machine's posterior weights at the counted habit prior.** `machineWeights` with
`habit := habitAt records`, over the menu that is the policy list. An empty menu is an
absence. -/
def machineWeightsAtHabit (records : List (Record M P)) (c : Concentration)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue) (F : PolicyKey M P → EReal)
    (tau : ℝ) (policies : List (PolicyKey M P)) : Except HabitAbsence (List ℝ) :=
  if hne : policies = [] then .error .emptyMenu
  else .ok (machineWeights (habitAt records c policies hne) grade F tau policies)

/-- **The composition.** On the ok arm the weights ARE `machineWeights` at `habitPrior`'s
masses, for a non-empty menu. -/
theorem machineWeightsAtHabit_eq (records : List (Record M P)) (c : Concentration)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue) (F : PolicyKey M P → EReal)
    (tau : ℝ) (policies : List (PolicyKey M P)) (ws : List ℝ)
    (h : machineWeightsAtHabit records c grade F tau policies = .ok ws) :
    ∃ hne : policies ≠ [],
      ws = machineWeights (habitAt records c policies hne) grade F tau policies := by
  unfold machineWeightsAtHabit at h
  by_cases hne : policies = []
  · rw [dif_pos hne] at h; cases h
  · rw [dif_neg hne] at h
    exact ⟨hne, (Except.ok.inj h).symm⟩

/-- **An empty menu has no posterior**, reachable: the absence, not a default list. -/
theorem emptyMenuHasNoPosterior (records : List (Record M P)) (c : Concentration)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue) (F : PolicyKey M P → EReal)
    (tau : ℝ) :
    machineWeightsAtHabit records c grade F tau [] = .error .emptyMenu := by
  simp [machineWeightsAtHabit]

/-- Every menu policy has positive habit mass at the counted prior, so
`machineWeights`' carrier hypothesis `0 < habit π` is met on a non-empty menu. -/
theorem habitAt_pos (records : List (Record M P)) (c : Concentration)
    (menu : List (PolicyKey M P)) (hne : menu ≠ []) (k : PolicyKey M P) (hk : k ∈ menu) :
    0 < habitAt records c menu hne k :=
  habitPrior_pos records c menu hne k (List.mem_dedup.mpr hk)

/-- **`unenactedPolicyIsScored` — the bad case for anyone who takes zero count for zero
weight.** A policy with count `0` on the menu and a finite `F` gets the habit mass
`α / Z > 0`, so its posterior weight is the positive `(α / Z) · exp(−G/τ − F)`: it is
scored, not excluded. (Its `ln habit` is a real `ln (α/Z)`, not `Real.log 0 = 0` standing
in for a count of zero.) The weight appears in the machine's weights. -/
theorem unenactedPolicyIsScored (records : List (Record M P)) (c : Concentration)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue) (F : PolicyKey M P → EReal)
    (tau : ℝ) (policies : List (PolicyKey M P)) (hne : policies ≠ [])
    (k : PolicyKey M P) (hk : k ∈ policies) (h0 : habitCounts records k = 0)
    (hF : FiniteF F k) :
    habitAt records c policies hne k = c.alpha / EnactmentHabit.normaliser records c policies ∧
    0 < habitAt records c policies hne k ∧
    weight (habitAt records c policies hne) grade F tau k
      = habitAt records c policies hne k * Real.exp (-(grade k).value / tau - (F k).toReal) ∧
    0 < weight (habitAt records c policies hne) grade F tau k ∧
    (∃ ws, machineWeightsAtHabit records c grade F tau policies = .ok ws ∧
      weight (habitAt records c policies hne) grade F tau k
          / PolicyPosteriorAtMachine.normaliser (habitAt records c policies hne) grade F tau policies
        ∈ ws) := by
  have hpos := habitAt_pos records c policies hne k hk
  have hval : habitAt records c policies hne k
      = c.alpha / EnactmentHabit.normaliser records c policies := by
    unfold habitAt habitPrior
    show (if k ∈ policies.dedup then weightOf records c k / EnactmentHabit.normaliser records c policies
      else 0) = _
    rw [if_pos (List.mem_dedup.mpr hk)]
    simp [weightOf, h0]
  have hw : weight (habitAt records c policies hne) grade F tau k
      = habitAt records c policies hne k * Real.exp (-(grade k).value / tau - (F k).toReal) := by
    unfold weight
    have : Real.log (habitAt records c policies hne k) - (grade k).value / tau - (F k).toReal
        = Real.log (habitAt records c policies hne k) + (-(grade k).value / tau - (F k).toReal) := by
      ring
    rw [this, Real.exp_add, Real.exp_log hpos]
  refine ⟨hval, hpos, hw, ?_, ?_⟩
  · rw [hw]; exact mul_pos hpos (Real.exp_pos _)
  · refine ⟨machineWeights (habitAt records c policies hne) grade F tau policies, ?_, ?_⟩
    · simp [machineWeightsAtHabit, hne]
    · unfold machineWeights
      refine List.mem_map.mpr ⟨k, hk, ?_⟩
      simp [hF]

end

#print axioms HabitAbsence
#print axioms habitAt
#print axioms machineWeightsAtHabit
#print axioms machineWeightsAtHabit_eq
#print axioms emptyMenuHasNoPosterior
#print axioms habitAt_pos
#print axioms unenactedPolicyIsScored

end DarkTower.WarMachine.Proof2.PosteriorAtHabit
