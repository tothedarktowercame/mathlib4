import DarkTower.WarMachine.ExactBeliefTrajectory

/-!
# Belief-conditioned rollout, and when the open loop is licensed

Until today the WarMachine Lean was SILENT on belief-conditioned rollout:
`PolicyRollout` propagates state open-loop, `ExactBeliefTrajectory` proves
the single-step posterior (`exactUpdate`, with `exactUpdate_dist`,
`exactUpdate_eq_none_iff`, `exactUpdate_minimises_vfe`), and a module note
elsewhere deferred conditioning to a posterior that in fact already exists.
Per the standing rule, that silence was a transcription item, not latitude
(futon2 `STOP-THE-LINE-2026-09-20.md`, failure class 3). This module is the
transcription.

It defines the multi-step conditioned trajectory — each step's exact
posterior feeds the next step's prior — proves its outputs are
distributions, and characterises VACUITY: conditioning returns the
predicted state unchanged exactly when the received observation's
likelihood is constant on the predicted state's support. Consequences,
stated so the run records can cite theorems rather than prose:

- with a point-mass predicted state (D degenerate) every observation has
  constant likelihood on the support, so open-loop rollout with
  `:observation-updates []` computes the same beliefs as conditioning —
  today's empty updates are LICENSED by `exactUpdate_pointMass_vacuous`;
- the license is exactly that narrow: once A carries rates and beliefs
  spread, a non-constant likelihood makes conditioning non-vacuous, and
  an evaluator that still reports open-loop values is computing a
  different quantity, not a reduction of the same one.
-/

namespace DarkTower.WarMachine.BeliefConditionedRollout

open DarkTower.WarMachine.ExactBeliefTrajectory

variable {S O : Type*} [Fintype S] [DecidableEq S]

noncomputable section

/-- Multi-step conditioned trajectory: fold the exact posterior through the
received observations, each posterior becoming the next prior. `none`
propagates a refused (predictively impossible) observation. -/
def conditionedTrajectory (A : S → O → ℝ) (B : S → S → ℝ) (s0 : S → ℝ) :
    List O → Option (S → ℝ)
  | [] => some s0
  | o :: rest => (exactUpdate A B o s0).bind fun s1 => conditionedTrajectory A B s1 rest

/-- Conditioned beliefs are distributions at every step. -/
theorem conditionedTrajectory_dist (A : S → O → ℝ) (B : S → S → ℝ)
    (hA : ∀ x o, 0 ≤ A x o) (hB : ∀ s x, 0 ≤ B s x)
    (os : List O) (s0 : S → ℝ) (h0 : (∀ x, 0 ≤ s0 x) ∧ ∑ x, s0 x = 1)
    {s : S → ℝ} (h : conditionedTrajectory A B s0 os = some s) :
    (∀ x, 0 ≤ s x) ∧ ∑ x, s x = 1 := by
  induction os generalizing s0 with
  | nil =>
    unfold conditionedTrajectory at h
    cases h
    exact h0
  | cons o rest ih =>
    unfold conditionedTrajectory at h
    rcases hbind : exactUpdate A B o s0 with _ | s1
    · rw [hbind] at h; cases h
    · rw [hbind] at h
      simp only [Option.bind_some] at h
      exact ih s1 (exactUpdate_dist A B o s0 (fun x => hA x o) hB h0.1 hbind) h

/-- **Vacuity characterised.** If the received observation's likelihood is a
positive constant `c` on the support of the predicted state, the exact
update returns the predicted state itself: conditioning changes nothing. -/
theorem exactUpdate_vacuous_of_const_likelihood
    (A : S → O → ℝ) (B : S → S → ℝ) (o : O) (sPrev : S → ℝ) (c : ℝ)
    (hc : 0 < c)
    (hpred1 : ∑ x, predictedState B sPrev x = 1)
    (hconst : ∀ x, predictedState B sPrev x ≠ 0 → A x o = c) :
    exactUpdate A B o sPrev = some (predictedState B sPrev) := by
  have hterm : ∀ x, A x o * predictedState B sPrev x = c * predictedState B sPrev x := by
    intro x
    by_cases hx : predictedState B sPrev x = 0
    · simp [hx]
    · rw [hconst x hx]
  have hP : observationProbability A B o sPrev = c := by
    unfold observationProbability
    simp_rw [hterm]
    rw [← Finset.mul_sum, hpred1, mul_one]
  unfold exactUpdate
  rw [if_neg (by rw [hP]; exact ne_of_gt hc)]
  congr 1
  funext x
  rw [hterm x, hP]
  exact mul_div_cancel_left₀ _ (ne_of_gt hc)

/-- **The open-loop license for point-mass beliefs.** When the predicted
state is a point mass and the received observation is possible there,
conditioning is vacuous. This is why `:observation-updates []` computed
correct beliefs in the zero-rate, point-mass regime — and exactly why the
license expires when beliefs spread. -/
theorem exactUpdate_pointMass_vacuous
    (A : S → O → ℝ) (B : S → S → ℝ) (o : O) (sPrev : S → ℝ) (x₀ : S)
    (hpm : predictedState B sPrev = fun x => if x = x₀ then 1 else 0)
    (hpos : 0 < A x₀ o) :
    exactUpdate A B o sPrev = some (predictedState B sPrev) := by
  refine exactUpdate_vacuous_of_const_likelihood A B o sPrev (A x₀ o) hpos ?_ ?_
  · rw [hpm]
    simp
  · intro x hx
    rw [hpm] at hx
    by_cases hx0 : x = x₀
    · rw [hx0]
    · simp [hx0] at hx

end

end DarkTower.WarMachine.BeliefConditionedRollout

#print axioms DarkTower.WarMachine.BeliefConditionedRollout.conditionedTrajectory_dist
#print axioms DarkTower.WarMachine.BeliefConditionedRollout.exactUpdate_vacuous_of_const_likelihood
#print axioms DarkTower.WarMachine.BeliefConditionedRollout.exactUpdate_pointMass_vacuous
