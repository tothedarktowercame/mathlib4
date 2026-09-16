import DarkTower.WarMachine.BeliefTrajectory
import DarkTower.WarMachine.PolicyVariationalFreeEnergy

/-!
# The stored belief as the exact categorical posterior (design P12)

Rows `:belief-state` (R1) and `:state-belief-update` (R3). Joe approved P12 on
2026-09-16 ("Let's try your proposal in this implementation so we can proceed"):
the stored belief and its update are the exact categorical posterior

  `s_t(x) = A(o_t|x) · (B s_{t−1})(x) / P(o_t)`, `P(o_t) = Σ_y A(o_t|y) · (B s_{t−1})(y)`,

and Parr et al. 2022 eq. 4.13 remains the stated inference scheme
(`StatePredictionError`). The reasons the choice rests on are theorems here:

* it is the unique minimiser of the variational free energy of Parr eq. B.2
  (`exactUpdate_minimises_vfe`, via `PolicyVariationalFreeEnergy`): perception
  minimises `F`, and `F` is minimised exactly at the posterior;
* it refuses only an observation of predictive probability zero
  (`exactUpdate_eq_none_iff`), whereas the mean-field update can refuse an observation
  exact Bayes allows (`BeliefTrajectory.fixture_meanField_refuses_possible`,
  and `fixture_exact_accepts` below on the same input);
* it coincides with the mean-field stationary belief when the previous state is
  known exactly (`exactUpdate_eq_meanField_observed`), which is P4's observed `q₀`.

The alternatives not taken (mean-field 4.13 as the stored update with declared
refusals; flooring `B` as in SPM practice) are recorded in the plop-2026 paper.
-/

namespace DarkTower.WarMachine.ExactBeliefTrajectory

variable {S O : Type*} [Fintype S] [DecidableEq S]

/-- The prior predictive state `(B s_prev)(x) = Σ_{s₀} P(x|s₀) s_prev(s₀)`. -/
def predictedState (B : S → S → ℝ) (sPrev : S → ℝ) (x : S) : ℝ :=
  ∑ s₀, B s₀ x * sPrev s₀

/-- The predictive probability of the observation, `P(o) = Σ_x A(o|x) (B s_prev)(x)`. -/
def observationProbability (A : S → O → ℝ) (B : S → S → ℝ) (o : O) (sPrev : S → ℝ) : ℝ :=
  ∑ x, A x o * predictedState B sPrev x

open Classical in
/-- The exact update, or `none` when the observation has predictive probability `0`. -/
noncomputable def exactUpdate (A : S → O → ℝ) (B : S → S → ℝ) (o : O) (sPrev : S → ℝ) :
    Option (S → ℝ) :=
  if observationProbability A B o sPrev = 0 then none
  else some fun x => A x o * predictedState B sPrev x / observationProbability A B o sPrev

section

variable (A : S → O → ℝ) (B : S → S → ℝ) (o : O) (sPrev : S → ℝ)

theorem predictedState_nonneg (hB : ∀ s x, 0 ≤ B s x) (hp : ∀ s, 0 ≤ sPrev s) (x : S) :
    0 ≤ predictedState B sPrev x :=
  Finset.sum_nonneg fun s₀ _ => mul_nonneg (hB s₀ x) (hp s₀)

theorem predictedState_sum (hB1 : ∀ s, ∑ x, B s x = 1) (hp1 : ∑ s, sPrev s = 1) :
    ∑ x, predictedState B sPrev x = 1 := by
  unfold predictedState
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hB1, one_mul, hp1]

/-- A returned belief is a distribution. -/
theorem exactUpdate_dist (hA : ∀ x, 0 ≤ A x o) (hB : ∀ s x, 0 ≤ B s x) (hp : ∀ s, 0 ≤ sPrev s)
    {s : S → ℝ} (h : exactUpdate A B o sPrev = some s) : (∀ x, 0 ≤ s x) ∧ ∑ x, s x = 1 := by
  unfold exactUpdate at h
  split_ifs at h with hz
  cases h
  have hnn : 0 ≤ observationProbability A B o sPrev :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hA x) (predictedState_nonneg B sPrev hB hp x)
  refine ⟨fun x => div_nonneg (mul_nonneg (hA x) (predictedState_nonneg B sPrev hB hp x)) hnn, ?_⟩
  rw [← Finset.sum_div]
  exact div_self hz

/-- **The exact update refuses only an impossible observation**: exactly when its
predictive probability is zero. -/
theorem exactUpdate_eq_none_iff :
    exactUpdate A B o sPrev = none ↔ observationProbability A B o sPrev = 0 := by
  unfold exactUpdate
  split_ifs with hz <;> simp [hz]

/-- **The exact update is the unique minimiser of the variational free energy** of
Parr eq. B.2, with likelihood `A(o|·)` and prior `B s_prev`: a belief `q` attains
`F = −ln P(o)` iff it is the exact update. -/
theorem exactUpdate_minimises_vfe (hA : ∀ x, 0 ≤ A x o) (hB : ∀ s x, 0 ≤ B s x)
    (hB1 : ∀ s, ∑ x, B s x = 1) (hp : ∀ s, 0 ≤ sPrev s) (hp1 : ∑ s, sPrev s = 1)
    (hZ : 0 < observationProbability A B o sPrev) (q : S → ℝ) (hq0 : ∀ x, 0 ≤ q x)
    (hq1 : ∑ x, q x = 1) :
    PolicyVariationalFreeEnergy.variationalFreeEnergy (fun x => A x o) (predictedState B sPrev) q
        = ↑(-Real.log (observationProbability A B o sPrev))
      ↔ exactUpdate A B o sPrev = some q := by
  have hev : PolicyVariationalFreeEnergy.evidence (fun x => A x o) (predictedState B sPrev)
      = observationProbability A B o sPrev := rfl
  have key := PolicyVariationalFreeEnergy.vfe_eq_neg_log_evidence_iff (fun x => A x o)
    (predictedState B sPrev) q hA (predictedState_nonneg B sPrev hB hp)
    (predictedState_sum B sPrev hB1 hp1) hq0 hq1 (by rw [hev]; exact hZ)
  rw [hev] at key
  rw [key]
  unfold exactUpdate
  rw [if_neg hZ.ne']
  constructor
  · intro h
    congr 1
    funext x
    rw [h x]
    rfl
  · intro h x
    have := congrFun (Option.some.inj h) x
    rw [← this]
    rfl

end

/-- **Agreement with eq. 4.13 at a known state.** From a point mass at `s₀` the exact
update equals the mean-field stationary belief of `BeliefTrajectory`. -/
theorem exactUpdate_eq_meanField_observed (A : S → O → ℝ) (B : S → S → ℝ) (o : O) (s₀ : S) :
    exactUpdate A B o (fun s => if s = s₀ then 1 else 0)
      = BeliefTrajectory.beliefUpdate A B o (fun s => if s = s₀ then 1 else 0) := by
  have hpred : ∀ x, predictedState B (fun s => if s = s₀ then 1 else 0) x = B s₀ x := fun x => by
    simp [predictedState]
  have hobs : observationProbability A B o (fun s => if s = s₀ then 1 else 0)
      = ∑ y, A y o * B s₀ y := by
    simp only [observationProbability, hpred]
  by_cases hZ : ∑ y, A y o * B s₀ y = 0
  · have h1 : exactUpdate A B o (fun s => if s = s₀ then 1 else 0) = none := by
      rw [exactUpdate_eq_none_iff, hobs, hZ]
    have hw : ∀ x, BeliefTrajectory.stateWeight A B o (fun s => if s = s₀ then 1 else 0) x
        = A x o * B s₀ x := fun x => by
      have hf : Finset.univ.filter (fun s => 0 < (if s = s₀ then (1 : ℝ) else 0)) = {s₀} := by
        ext s
        by_cases h : s = s₀ <;> simp [h]
      rw [BeliefTrajectory.stateWeight, hf, Finset.prod_singleton, if_pos rfl, Real.rpow_one]
    have h2 : BeliefTrajectory.beliefUpdate A B o (fun s => if s = s₀ then 1 else 0) = none := by
      unfold BeliefTrajectory.beliefUpdate
      simp only [hw]
      rw [if_pos hZ]
    rw [h1, h2]
  · rw [BeliefTrajectory.beliefUpdate_observed A B o s₀ hZ]
    unfold exactUpdate
    rw [hobs, if_neg hZ]
    simp only [hpred]

/-! ## The stored trajectory -/

/-- `μ_0 = q₀`; `μ_{t+1}` is the exact update of `μ_t` by the transition of action `u_t`
and the observation `o_{t+1}`. A refusal (an impossible observation) is carried forward. -/
noncomputable def exactBeliefAt {U : Type*} (A : S → O → ℝ) (B : U → S → S → ℝ) (q₀ : S → ℝ)
    (u : ℕ → U) (o : ℕ → O) : ℕ → Option (S → ℝ)
  | 0 => some q₀
  | t + 1 => (exactBeliefAt A B q₀ u o t).bind fun s => exactUpdate A (B (u t)) (o (t + 1)) s

theorem exactBeliefAt_succ {U : Type*} (A : S → O → ℝ) (B : U → S → S → ℝ) (q₀ : S → ℝ)
    (u : ℕ → U) (o : ℕ → O) (t : ℕ) :
    exactBeliefAt A B q₀ u o (t + 1)
      = (exactBeliefAt A B q₀ u o t).bind fun s => exactUpdate A (B (u t)) (o (t + 1)) s := rfl

/-- Every stored belief is a distribution. -/
theorem exactBeliefAt_dist {U : Type*} (A : S → O → ℝ) (B : U → S → S → ℝ) (q₀ : S → ℝ)
    (u : ℕ → U) (o : ℕ → O) (hA : ∀ x o, 0 ≤ A x o) (hB : ∀ u s x, 0 ≤ B u s x)
    (hq0 : ∀ x, 0 ≤ q₀ x) (hq1 : ∑ x, q₀ x = 1) :
    ∀ t {s : S → ℝ}, exactBeliefAt A B q₀ u o t = some s → (∀ x, 0 ≤ s x) ∧ ∑ x, s x = 1
  | 0, s, h => by
    simp only [exactBeliefAt, Option.some.injEq] at h
    subst h
    exact ⟨hq0, hq1⟩
  | t + 1, s, h => by
    rw [exactBeliefAt_succ, Option.bind_eq_some_iff] at h
    obtain ⟨s', hs', hs⟩ := h
    exact exactUpdate_dist A (B (u t)) (o (t + 1)) s' (fun x => hA x _) (hB (u t))
      (exactBeliefAt_dist A B q₀ u o hA hB hq0 hq1 t hs').1 hs

/-- The belief at `t` depends only on the actions before `t` and the observations up to `t`. -/
theorem exactBeliefAt_congr {U : Type*} (A : S → O → ℝ) (B : U → S → S → ℝ) (q₀ : S → ℝ)
    {u u' : ℕ → U} {o o' : ℕ → O} :
    ∀ t, (∀ m < t, u m = u' m) → (∀ m ≤ t, o m = o' m) →
      exactBeliefAt A B q₀ u o t = exactBeliefAt A B q₀ u' o' t
  | 0, _, _ => rfl
  | t + 1, hu, ho => by
    rw [exactBeliefAt_succ, exactBeliefAt_succ,
      exactBeliefAt_congr A B q₀ t (fun m hm => hu m (Nat.lt_succ_of_lt hm))
        (fun m hm => ho m (Nat.le_succ_of_le hm)),
      hu t (Nat.lt_succ_self t), ho (t + 1) le_rfl]

/-! ## Fixture: the input on which mean-field refused -/

/-- **Exact Bayes accepts the observation mean-field refused.** A uniform belief through
the deterministic flip, observed `true` with the noisy likelihood: the exact update is
`true` with probability 9/10 (compare `BeliefTrajectory.fixture_meanField_refuses_possible`). -/
theorem fixture_exact_accepts :
    exactUpdate BeliefTrajectory.fxAnoisy (BeliefTrajectory.fxB true) true (fun _ => 1 / 2)
      = some fun x => if x = true then 9 / 10 else 1 / 10 := by
  unfold exactUpdate
  have hobs : observationProbability BeliefTrajectory.fxAnoisy (BeliefTrajectory.fxB true) true
      (fun _ => (1 : ℝ) / 2) = 1 / 2 := by
    simp [observationProbability, predictedState, BeliefTrajectory.fxAnoisy,
      BeliefTrajectory.fxB, Fintype.sum_bool]
    norm_num
  rw [hobs, if_neg (by norm_num)]
  congr 1
  funext x
  cases x <;> simp [predictedState, BeliefTrajectory.fxAnoisy, BeliefTrajectory.fxB,
    Fintype.sum_bool] <;> norm_num

end DarkTower.WarMachine.ExactBeliefTrajectory
