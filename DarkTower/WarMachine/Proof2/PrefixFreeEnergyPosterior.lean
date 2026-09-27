import DarkTower.WarMachine.Proof2.PrefixFreeEnergyAtMachine
import DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

/-!
# W1b's weights at the executed-prefix free energy ([R8 R6])

This module composes the machine's executed-prefix F with its policy weights.
It is a sibling of the prefix and posterior modules: the posterior cannot
import the prefix module, because the prefix already reaches the posterior
through ObservationAtMachine → ActionAtMachine → PolicyPosteriorAtMachine
(W11-D §2). No policy carrier is rebound here.
-/

set_option linter.unusedSectionVars false

namespace DarkTower.WarMachine.Proof2.PrefixFreeEnergyPosterior

open DarkTower.WarMachine
open DarkTower.WarMachine.Proof2.CascadePolicySet (PolicyKey)
open DarkTower.WarMachine.Proof2.PrefixFreeEnergyAtMachine
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

noncomputable section

variable {M P S O : Type*} [DecidableEq M] [DecidableEq P] [Fintype S] [DecidableEq S]

/-! ## F into the posterior -/

section FPosterior

open Classical

/-- Why there are no posterior weights at the prefix F. -/
inductive PrefixWeightsAbsence (M P : Type*) where
  | notSupplied (π : PolicyKey M P)

/-- **The machine's posterior weights with `F` the observed-prefix free energy.**
`machineWeights` (W1/W1b) with `F π := prefixF π (steps π)`, `⊤` at a contradiction (weight
`0`). A policy on the menu with NO admitted history has no `F` and the weights are absent,
naming it: no `0` is stood in. -/
def machineWeightsAtPrefixF (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) : Except (PrefixWeightsAbsence M P) (List ℝ) :=
  match policies.find? (fun π => decide (prefixF π (steps π) = .error .noAdmittedSteps)) with
  | some π => .error (.notSupplied π)
  | none =>
    .ok (machineWeights habit grade
      (fun π => match prefixF π (steps π) with | .ok f => f | .error _ => ⊤) tau policies)

/-- **The composition.** On the ok arm every menu policy has an admitted history or a
contradiction, and the weights are `machineWeights` at that `F`. -/
theorem machineWeightsAtPrefixF_eq (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) (ws : List ℝ)
    (h : machineWeightsAtPrefixF habit grade steps tau policies = .ok ws) :
    (∀ π ∈ policies, prefixF π (steps π) ≠ .error .noAdmittedSteps) ∧
    ws = machineWeights habit grade
      (fun π => match prefixF π (steps π) with | .ok f => f | .error _ => ⊤) tau policies := by
  unfold machineWeightsAtPrefixF at h
  cases hf : policies.find? (fun π => decide (prefixF π (steps π) = .error .noAdmittedSteps)) with
  | some π => rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    refine ⟨fun π hπ hπ' => ?_, (Except.ok.inj h).symm⟩
    have := List.find?_eq_none.mp hf π hπ
    simp [hπ'] at this

/-- **A policy with no admitted history makes the weights absent**, naming a policy: reachable,
and no `F = 0` is stood in. -/
theorem notSuppliedIsAbsence (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) (π : PolicyKey M P) (hπ : π ∈ policies)
    (hn : prefixF π (steps π) = .error .noAdmittedSteps) :
    ∃ π', machineWeightsAtPrefixF habit grade steps tau policies = .error (.notSupplied π') := by
  unfold machineWeightsAtPrefixF
  cases hf : policies.find? (fun π => decide (prefixF π (steps π) = .error .noAdmittedSteps)) with
  | some π' => exact ⟨π', rfl⟩
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf π hπ
    simp [hn] at this

/-- **A policy whose prefix ended in a contradiction has weight zero.** `F = ⊤`, so W1b's
`infiniteFHasZeroWeight` applies: the code's `:zero-support`. -/
theorem contradictionHasZeroWeight (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) (ws : List ℝ)
    (h : machineWeightsAtPrefixF habit grade steps tau policies = .ok ws) :
    ∀ p ∈ policies.zip ws, prefixF p.1 (steps p.1) = .error .contradiction → p.2 = 0 := by
  obtain ⟨_, rfl⟩ := machineWeightsAtPrefixF_eq habit grade steps tau policies ws h
  intro p hp hc
  refine infiniteFHasZeroWeight habit grade _ tau policies p hp ?_
  intro hfin
  simp [FiniteF, hc] at hfin

end FPosterior

end

#print axioms machineWeightsAtPrefixF
#print axioms machineWeightsAtPrefixF_eq
#print axioms notSuppliedIsAbsence
#print axioms contradictionHasZeroWeight

end DarkTower.WarMachine.Proof2.PrefixFreeEnergyPosterior
