import DarkTower.WarMachine.MachineQ
import DarkTower.WarMachine.MachineTransition

namespace DarkTower.WarMachine.MachinePredictedStatePlan
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineBeliefState
open DarkTower.WarMachine.MachineTransition

noncomputable def predictedStateStep (q : Posterior) (a : Action) : Posterior :=
  fun s' => (Status.all.map fun s => q s * controlled.mass (s, a) s').sum

noncomputable def predictedStateTerminal : Posterior → List Action → Posterior
  | q, [] => q
  | q, a :: as => predictedStateTerminal (predictedStateStep q a) as

noncomputable def predictedStateSteps : Posterior → List Action → List Posterior
  | q, [] => [q]
  | q, a :: as => q :: predictedStateSteps (predictedStateStep q a) as

private theorem sumSwap {α β : Type*} (xs : List α) (ys : List β)
    (f : α → β → ℝ) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih, List.sum_map_add]

theorem zeroDepthIdentity (q : Posterior) : predictedStateTerminal q [] = q := rfl

theorem oneStepAgreement (q : Posterior) (a : Action) :
    predictedStateTerminal q [a] = predictedStateStep q a := rfl

theorem stepNonnegative (q : Posterior) (a : Action) (hq : ∀ s, 0 ≤ q s) :
    ∀ s, 0 ≤ predictedStateStep q a s := by
  intro s'
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨s, _, rfl⟩ := hx
  exact mul_nonneg (hq s) (controlled.nonnegative (s, a) s')

theorem stepNormalised (q : Posterior) (a : Action) (hq : Normalised q) :
    Normalised (predictedStateStep q a) := by
  unfold Normalised predictedStateStep
  rw [sumSwap Status.all Status.all
      (fun s' s => q s * controlled.mass (s, a) s')]
  simp only [List.sum_map_mul_left, controlled.normalised, mul_one]
  exact hq

theorem terminalNormalised (q : Posterior) (actions : List Action)
    (hn : ∀ s, 0 ≤ q s) (hq : Normalised q) :
    Normalised (predictedStateTerminal q actions) := by
  induction actions generalizing q with
  | nil => exact hq
  | cons a as ih =>
      exact ih (predictedStateStep q a) (stepNonnegative q a hn)
        (stepNormalised q a hq)

theorem everyRetainedStepNormalised (q : Posterior) (actions : List Action)
    (hn : ∀ s, 0 ≤ q s) (hq : Normalised q) :
    ∀ r ∈ predictedStateSteps q actions, Normalised r := by
  induction actions generalizing q with
  | nil => simpa [predictedStateSteps] using hq
  | cons a as ih =>
      intro r hr
      simp only [predictedStateSteps, List.mem_cons] at hr
      cases hr with
      | inl h => simpa [h] using hq
      | inr h =>
          exact (ih (predictedStateStep q a) (stepNonnegative q a hn)
            (stepNormalised q a hq) r h)

theorem equalFullPlansGiveEqualPrediction (q : Posterior) (p₁ p₂ : List Action)
    (h : p₁ = p₂) : predictedStateTerminal q p₁ = predictedStateTerminal q p₂ := by
  subst p₂
  rfl

end DarkTower.WarMachine.MachinePredictedStatePlan
