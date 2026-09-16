import DarkTower.WarMachine.PolicyRollout
import DarkTower.WarMachine.TokenObservation

/-!
# The observation boundary: `o_t` from the world after `u_{t−1}`

Row `:observe` (audit A2 §1). Registry formal:
`o_t <- structured observation of the world after action u_{t-1}`. The audit found
no world, action or time relation in the old binding. Friston et al. 2017 separate
the generative *process* R(õ, s̃, ũ), which produces outcomes from hidden states and
action (`refs/friston2017.txt:227–245`), from the generative *model*, whose
categorical form is eq. 2.1 (`:323–334`): `P(o_t | s_t) = Cat(A)`,
`P(s_{t+1} | s_t, π) = Cat(B(u = π(t)))`. The source does not give R in that form.

**Declared stack assumption:** the world is taken to be a finite categorical process
of the same form as eq. 2.1, on the model's carriers (under P5, established-token
sets). The process and the agent's model are identified only where a theorem says so.

So, from the world state `s_{t−1}` and the action `u_{t−1}`, the observation
distribution is `P(o_t | s_{t−1}, u_{t−1}) = Σ_{s_t} B(s_t | s_{t−1}, u_{t−1}) A(o_t | s_t)`.
The world's own state is used here, not a belief. Under the approved observation
design P5 (`TokenObservation`), the world state is the established-token set, and
only when every adjudication rate is zero does the observation report that set
exactly; with a nonzero rate the reported set is not the world state.
-/

namespace DarkTower.WarMachine.ObservationProcess

open DarkTower.WarMachine.PolicyRollout

variable {S O U : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- `P(o_t | s_{t−1}, u_{t−1}) = Σ_{s_t} B(s_t | s_{t−1}, u_{t−1}) A(o_t | s_t)`. -/
noncomputable def observationAfter (M : ForwardModel S O U) (sPrev : S) (u : U) (o : O) : ℝ :=
  ∑ s, M.B u sPrev s * M.A s o

theorem observationAfter_nonneg (M : ForwardModel S O U) (sPrev : S) (u : U) (o : O) :
    0 ≤ observationAfter M sPrev u o :=
  Finset.sum_nonneg fun s _ => mul_nonneg (M.B_nonneg u sPrev s) (M.A_nonneg s o)

theorem observationAfter_sum (M : ForwardModel S O U) (sPrev : S) (u : U) :
    ∑ o, observationAfter M sPrev u o = 1 := by
  unfold observationAfter
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, M.A_colsum, mul_one, M.B_rowsum]

/-- The observation depends on the action only through the transition row it
selects: actions with the same `B` row from `s_{t−1}` give the same distribution. -/
theorem observationAfter_eq_of_rows (M : ForwardModel S O U) (sPrev : S) (u u' : U)
    (h : ∀ s, M.B u sPrev s = M.B u' sPrev s) (o : O) :
    observationAfter M sPrev u o = observationAfter M sPrev u' o := by
  simp only [observationAfter, h]

/-- The model started from a known world state (a point mass at `s_{t−1}`). Under P5
the state is known from its observation only when every adjudication rate is zero. -/
noncomputable def fromKnownState (M : ForwardModel S O U) (sPrev : S) : ForwardModel S O U :=
  { M with
    q₀ := fun s => if s = sPrev then 1 else 0
    q₀_nonneg := fun s => by split_ifs <;> norm_num
    q₀_sum := by simp }

/-- **Hypothesis: the agent's model is the process.** Started from the known previous
world state, the one-step predicted outcome is exactly the process's observation
distribution. -/
theorem predictedOutcome_fromKnownState (M : ForwardModel S O U) (sPrev : S) (π : ℕ → U)
    (o : O) :
    predictedOutcome (fromKnownState M sPrev) π 1 o = observationAfter M sPrev (π 0) o := by
  rw [predictedOutcome_one]
  simp only [fromKnownState, observationAfter]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp

/-! ## Under the approved observation design (P5) -/

open DarkTower.WarMachine.TokenObservation in
/-- With every token checkable (zero adjudication rates), the observation after an
action is the distribution of the next established-token set itself. -/
theorem observationAfter_checkable {V : Type*} [Fintype V] [DecidableEq V]
    (r : AdjudicationRates V) (hfn : ∀ v, r.falseNeg v = 0) (hfp : ∀ v, r.falsePos v = 0)
    (M : ForwardModel (Finset V) (Finset V) U) (hA : M.A = tokenLikelihood r)
    (sPrev : Finset V) (u : U) (o : Finset V) :
    observationAfter M sPrev u o = M.B u sPrev o := by
  simp only [observationAfter, hA, tokenLikelihood_checkable r hfn hfp]
  rw [Finset.sum_eq_single o]
  · simp
  · intro x _ hx
    rw [if_neg (fun hc => hx hc.symm), mul_zero]
  · intro ho
    exact absurd (Finset.mem_univ o) ho

open DarkTower.WarMachine.TokenObservation in
/-- A deterministic application that establishes `s'` from `s_{t−1}`, observed with
checkable tokens, reports `s'` with probability one. -/
theorem observationAfter_deterministic {V : Type*} [Fintype V] [DecidableEq V]
    (r : AdjudicationRates V) (hfn : ∀ v, r.falseNeg v = 0) (hfp : ∀ v, r.falsePos v = 0)
    (M : ForwardModel (Finset V) (Finset V) U) (hA : M.A = tokenLikelihood r)
    (sPrev s' : Finset V) (u : U) (hB : ∀ s, M.B u sPrev s = if s = s' then 1 else 0)
    (o : Finset V) :
    observationAfter M sPrev u o = if o = s' then 1 else 0 := by
  rw [observationAfter_checkable r hfn hfp M hA, hB]

/-! ## Fixture: the action changes what is observed -/

private noncomputable def fxModel : ForwardModel Bool Bool Bool where
  B := fun u s s' => if u then (if s' = !s then 1 else 0) else (if s' = s then 1 else 0)
  B_nonneg := by intro u s s'; split_ifs <;> norm_num
  B_rowsum := by intro u s; cases u <;> cases s <;> simp
  A := fun s o => if s = o then 9 / 10 else 1 / 10
  A_nonneg := by intro s o; split_ifs <;> norm_num
  A_colsum := by intro s; cases s <;> simp <;> norm_num
  q₀ := fun s => if s then 0 else 1
  q₀_nonneg := by intro s; split_ifs <;> norm_num
  q₀_sum := by simp

/-- From world state `false`, keeping yields observation `true` with 1/10;
flipping yields it with 9/10. -/
theorem fixture_action_changes_observation :
    observationAfter fxModel false false true = 1 / 10 ∧
      observationAfter fxModel false true true = 9 / 10 := by
  constructor <;> simp [observationAfter, fxModel, Fintype.sum_bool]

end DarkTower.WarMachine.ObservationProcess
