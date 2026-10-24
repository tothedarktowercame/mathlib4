import DarkTower.WarMachine.PatternTheta
import DarkTower.WarMachine.CascadeCoApplyG

/-!
# A learned pattern theta changes the canonical cascade prediction

This module is an explicitly synthetic, single-occurrence control.  It composes
the existing `PatternTheta.interpretWithTheta`, co-application transition,
prediction, and observation push.  The reading and admitted history remain
parameters.  No claim is made about runtime witness authority, selection, G
monotonicity, or the still-missing binding from this occurrence and full class
prediction to an `R20Run.Click` and its scalar `reach`.
-/

namespace DarkTower.WarMachine.ThetaPredictionConsumer

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.CascadeEFE
open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.CascadeCoApplyG
open DarkTower.WarMachine.CTauClassPreference
open DarkTower.WarMachine.Proof2.CoApplicationKernel
open DarkTower.WarMachine.Proof2.ContainmentOrder

noncomputable section

/-- The one synthetic occurrence produces the token `true`. -/
def pattern (r : PatternTheta.ThetaReading) (xs : List Bool) :
    Unit → InterpretedPattern Bool := fun _ =>
  PatternTheta.interpretWithTheta ∅ {true} ∅ r xs

/-- A deterministic observation that distinguishes the produced token from the
unchanged empty state. -/
def observation : ProbabilityKernel (Finset Bool) EndingClass :=
  finiteKernel
    (fun s ending => if ending = (if true ∈ s then .focused else .stopTheLine) then 1 else 0)
    (by intros; split_ifs <;> norm_num)
    (by intro s; by_cases h : true ∈ s <;> simp [h])

/-- The actual canonical one-step class prediction for this occurrence. -/
def oneStep (r : PatternTheta.ThetaReading) (xs : List Bool) :
    ProbabilityKernel Unit EndingClass :=
  push (prediction (point (∅ : Finset Bool)) (coKernel (pattern r xs)) 1) observation

theorem frontier_eq (r : PatternTheta.ThetaReading) (xs : List Bool) :
    enabledFrontier (pattern r xs) (containmentOrder (pattern r xs)) ∅ = {()} := by
  have noEdge : ∀ a b : Unit, ¬ containmentOrder (pattern r xs) a b := by
    intro a b h
    exact h.1 (Subsingleton.elim _ _)
  have noReach : ∀ a b : Unit, ¬ Reach (containmentOrder (pattern r xs)) a b :=
    fun _ _ => not_reach_of_empty noEdge
  ext p
  simp only [enabledFrontier, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro _
    simp
  · intro _
    constructor
    · simp [pattern, PatternTheta.interpretWithTheta, CascadeTransition.guard]
    · intro q _
      exact noReach p q

/-- Exact consumer equation: the focused mass after one canonical co-application
step and observation push is the learned posterior mean theta. -/
theorem oneStep_focused_eq_theta (r : PatternTheta.ThetaReading) (xs : List Bool) :
    (oneStep r xs).mass () .focused = (PatternTheta.thetaOf r xs : ℝ) := by
  classical
  have hk (s' : Finset Bool) : (coKernel (pattern r xs)).mass ∅ s' =
      patternKernel (pattern r xs ()) ∅ s' := by
    exact coApplyKernel_of_singletonFrontier (frontier_eq r xs) s'
  simp [oneStep, prediction, push, point, finiteKernel, observation, hk, pattern,
    PatternTheta.interpretWithTheta, patternKernel,
    show (Finset.univ : Finset (Finset Bool)) = {∅, {false}, {true}, {false, true}} by decide]
  rw [Finset.sum_pair (by decide : ({true} : Finset Bool) ≠ {false, true})]
  simp

/-- Appending one already-admitted success strictly raises the observed produced
effect probability through the canonical prediction consumer. -/
theorem admitted_success_raises_prediction (r : PatternTheta.ThetaReading) (xs : List Bool) :
    (oneStep r xs).mass () .focused < (oneStep r (xs ++ [true])).mass () .focused := by
  rw [oneStep_focused_eq_theta, oneStep_focused_eq_theta]
  exact_mod_cast PatternTheta.success_raises r xs

/-- Frozen theta yields the same prediction; it cannot support the strict
learning conclusion. -/
theorem frozen_theta_prediction_eq (r : PatternTheta.ThetaReading) (xs : List Bool) :
    (oneStep r xs).mass () .focused = (oneStep r xs).mass () .focused := rfl

theorem frozen_theta_not_strict (r : PatternTheta.ThetaReading) (xs : List Bool) :
    ¬ (oneStep r xs).mass () .focused < (oneStep r xs).mass () .focused := lt_irrefl _

#print axioms oneStep_focused_eq_theta
#print axioms admitted_success_raises_prediction
#print axioms frozen_theta_not_strict

end
end DarkTower.WarMachine.ThetaPredictionConsumer
