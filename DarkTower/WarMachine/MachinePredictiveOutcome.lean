import DarkTower.WarMachine.MachinePredictedStatePlan
import DarkTower.WarMachine.MachineQ
import DarkTower.WarMachine.MachineModelSpec

namespace DarkTower.WarMachine.MachinePredictiveOutcome
noncomputable section
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineBeliefState
open DarkTower.WarMachine.MachineTransition
open DarkTower.WarMachine.MachinePredictedStatePlan

/-- The machine A is explicitly over tagged outcomes and carries its declared
authority; it is not the lifecycle-event likelihood. -/
structure MachineA (Obs : Vertex → Type) where
  kernel : ProbabilityKernel Status (Outcome Obs)
  outcomes : List (Outcome Obs)
  supportExact : ∀ s, kernel.support s = outcomes
  authority : DarkTower.WarMachine.MachineModelSpec.Authority
  declared : authority.isDeclared

private theorem sumSwap' {α β : Type*} (xs : List α) (ys : List β)
    (f : α → β → ℝ) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih, List.sum_map_add]

theorem terminalNonnegative (q : Posterior) (plan : List Action)
    (hn : ∀ s, 0 ≤ q s) : ∀ s, 0 ≤ predictedStateTerminal q plan s := by
  induction plan generalizing q with
  | nil => exact hn
  | cons a as ih => exact ih (predictedStateStep q a) (stepNonnegative q a hn)

def fullPlanOutcomeMass (a : MachineA Obs) (q : Posterior)
    (plan : List Action) (o : Outcome Obs) : ℝ :=
  (Status.all.map fun s => predictedStateTerminal q plan s * a.kernel.mass s o).sum

noncomputable def fullPlanOutcomeKernel (a : MachineA Obs) (q : Posterior)
    (hn : ∀ s, 0 ≤ q s) (hq : Normalised q) :
    ProbabilityKernel (List Action) (Outcome Obs) where
  support _ := a.outcomes
  mass plan o := fullPlanOutcomeMass a q plan o
  nonnegative := by
    intro plan o
    apply List.sum_nonneg
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨s, _, rfl⟩ := hx
    exact mul_nonneg (terminalNonnegative q plan hn s) (a.kernel.nonnegative s o)
  normalised := by
    intro plan
    have hT := terminalNormalised q plan hn hq
    unfold fullPlanOutcomeMass
    rw [sumSwap' a.outcomes Status.all
      (fun o s => predictedStateTerminal q plan s * a.kernel.mass s o)]
    have hA : ∀ s, (a.outcomes.map (a.kernel.mass s)).sum = 1 := by
      intro s; rw [← a.supportExact s]; exact a.kernel.normalised s
    simp only [List.sum_map_mul_left, hA, mul_one]
    exact hT

theorem fullPlanEquation (a : MachineA Obs) (q : Posterior)
    (hn : ∀ s, 0 ≤ q s) (hq : Normalised q) (plan : List Action) (o : Outcome Obs) :
    (fullPlanOutcomeKernel a q hn hq).mass plan o =
      (Status.all.map fun s => predictedStateTerminal q plan s * a.kernel.mass s o).sum := rfl

theorem exactSupport (a : MachineA Obs) (q : Posterior)
    (hn : ∀ s, 0 ≤ q s) (hq : Normalised q) (plan : List Action) :
    (fullPlanOutcomeKernel a q hn hq).support plan = a.outcomes := rfl

/-- Required row-9 bridge: under a QReading whose action projection and belief
coordinates are the actual ones, its one-step mass is the row-9 step. -/
theorem predictedStateStep_agrees_machinePredictedStateKernel
    (model : GenerativeModel Obs Status Action Action)
    (reading : DarkTower.WarMachine.MachineQ.QReading model)
    (b : BeliefState) (q : Posterior) (a : Action)
    (hs : reading.states = Status.all)
    (hp : reading.plan a = a)
    (hb : ∀ s, reading.beliefMass b s = q s)
    (ht : ∀ s s', model.transition.mass (s, a) s' = controlled.mass (s, a) s') :
    ∀ s', (DarkTower.WarMachine.MachineQ.machinePredictedStateKernel model reading b).mass a s'
      = predictedStateStep q a s' := by
  intro s'
  simp [DarkTower.WarMachine.MachineQ.machinePredictedStateKernel,
    DarkTower.WarMachine.MachineQ.predictedStateMass, predictedStateStep, hs, hp, hb, ht]

end
end DarkTower.WarMachine.MachinePredictiveOutcome
