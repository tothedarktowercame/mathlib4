import DarkTower.WarMachine.CascadeScoringExamples
import DarkTower.WarMachine.Proof2.CoApplicationKernel

/-!
# Scoring the same cascades with the co-application kernel

`CascadeScoringExamples` scored cascades with `CascadeEFE.scoreCascade`, whose
transition is the first-enabled list kernel: one pattern fires per epoch. That
is not the cascade's transition. PROOF-2a Clause 0 replaced it by
co-application (`Proof2.CoApplicationKernel.coApplyKernel`): every enabled
pattern with no enabled pattern above it in the descent order fires at once,
and the list kernel agrees with it only on a chain
(`coApplyKernel_eq_cascadeKernel_of_chain`).

Here the same G (`CascadeEFE.totalG`: risk + ambiguity per epoch) is computed
with the co-application kernel over the containment order. With `θ = 1` a
frontier of patterns all fire, so an epoch adds the products of the whole
frontier (`coApply_one`).

| cascade | list kernel: goal at epoch | co-application: goal at epoch |
|---|---|---|
| chain of three | 3 | 3 |
| join of three | 3 | 2 |
| seven agent patterns (m40 G7) | 7 | 6 |

So the join now scores better than the chain (`join_beats_chain`), and the
agent cascade's co-applied pair (evidence and trail, both on the dispatch)
takes one epoch, not two. The semilattice shape reaches G through the kernel.
-/

namespace DarkTower.WarMachine.CascadeCoScoringExamples

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.CascadeEFE
open DarkTower.WarMachine.CascadeTransition

open DarkTower.WarMachine.Proof2.ContainmentOrder
open DarkTower.WarMachine.Proof2.CoApplicationKernel
open DarkTower.WarMachine.CascadeScoringExamples
open scoped BigOperators

noncomputable section

variable {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- The co-application kernel as a probability kernel on states. -/
def coK (pat : ι → InterpretedPattern V) (r : ι → ι → Prop) :
    ProbabilityKernel (Finset V) (Finset V) :=
  finiteKernel (coApplyKernel pat r) (coApplyKernel_nonneg pat r) (coApplyKernel_rowsum pat r)

/-- The state after one epoch of co-application with `θ = 1`. -/
def fCo (pat : ι → InterpretedPattern V) (r : ι → ι → Prop) (s : Finset V) : Finset V :=
  s ∪ (enabledFrontier pat r s).biUnion fun p => (pat p).produces

/-- With every `θ = 1`, the whole frontier fires: only the subset equal to the
frontier has weight. -/
theorem coApply_one (pat : ι → InterpretedPattern V) (r : ι → ι → Prop)
    (one : ∀ p, (pat p).theta = 1) (s s' : Finset V) :
    (coK pat r).mass s s' = if s' = fCo pat r s then 1 else 0 := by
  show coApplyKernel pat r s s' = _
  unfold coApplyKernel
  rw [Finset.sum_eq_single (enabledFrontier pat r s)]
  · simp [one, fCo]
  · intro S hS hne
    have sub : S ⊆ enabledFrontier pat r s := Finset.mem_powerset.mp hS
    obtain ⟨p, hpF, hpS⟩ : ∃ p ∈ enabledFrontier pat r s, p ∉ S := by
      by_contra h
      push Not at h
      exact hne (Finset.Subset.antisymm sub h)
    have zero : ∏ q ∈ enabledFrontier pat r s \ S, (1 - (pat q).theta) = 0 :=
      Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hpF, hpS⟩) (by simp [one])
    simp [zero]
  · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h

/-- The decidable step: the products of every enabled pattern. -/
def nextCo (pat : ι → InterpretedPattern V) (s : Finset V) : Finset V :=
  s ∪ (Finset.univ.filter fun p => guard (pat p) s).biUnion fun p => (pat p).produces

/-- When no enabled pattern is above another, the frontier is every enabled
pattern. -/
theorem fCo_eq_nextCo (pat : ι → InterpretedPattern V) (r : ι → ι → Prop) (s : Finset V)
    (anti : ∀ p q, guard (pat p) s → guard (pat q) s → ¬ Reach r p q) :
    fCo pat r s = nextCo pat s := by
  have : enabledFrontier pat r s = Finset.univ.filter fun p => guard (pat p) s := by
    ext p
    simp only [enabledFrontier, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.1, fun h => ⟨h, fun q hq => anti p q h hq⟩⟩
  simp [fCo, nextCo, this]

theorem iterate_agree {f g : Finset V → Finset V} (x : Finset V) (n : ℕ)
    (h : ∀ k < n, f (g^[k] x) = g (g^[k] x)) : f^[n] x = g^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (fun k hk => h k (by omega)),
      h n (by omega)]

/-- G of a cascade under co-application, with `θ = 1`, is the sum of `-log C`
along its trajectory, provided no enabled pattern is above another on the
trajectory's first `T` states. -/
theorem coScore (pat : ι → InterpretedPattern V) (r : ι → ι → Prop)
    (one : ∀ p, (pat p).theta = 1) (start : Finset V) (goal : V) (c : ℝ) (h0 : 0 < c)
    (h1 : c < 1) (T : ℕ)
    (anti : ∀ k ≤ T, ∀ p q, guard (pat p) ((nextCo pat)^[k] start) →
      guard (pat q) ((nextCo pat)^[k] start) → ¬ Reach r p q)
    (adm : ∀ t : Fin T, PreferenceRiskSeparation.riskAdmissible
      (push (prediction (point start) (coK pat r) (t.val + 1)) (obsK goal))
      (prefK c h0.le h1.le)) :
    totalG (point start) (coK pat r) (obsK goal) T (fun _ => prefK c h0.le h1.le) adm =
      ∑ t : Fin T, -Real.log ((prefK c h0.le h1.le).mass ()
        (decide (goal ∈ (nextCo pat)^[t.val + 1] start))) := by
  unfold totalG
  refine Finset.sum_congr rfl fun t _ => ?_
  have traj : (fCo pat r)^[t.val + 1] start = (nextCo pat)^[t.val + 1] start :=
    iterate_agree start _ fun k hk => fCo_eq_nextCo pat r _ (anti k (by omega))
  rw [stepG_point goal c h0 h1 _ _ (prediction_det (fCo pat r) (coApply_one pat r one) start _),
    traj]

/-! ## Excluding reach between enabled patterns -/

/-- If every successor of `x` lies in a set closed under successors, so does
everything `x` reaches. -/
theorem reach_mem_of_closed {r : ι → ι → Prop} (S : Finset ι) {x y : ι}
    (hx : ∀ b, r x b → b ∈ S) (closed : ∀ a ∈ S, ∀ b, r a b → b ∈ S) (h : Reach r x y) :
    y ∈ S := by
  induction h with
  | single e => exact hx _ e
  | tail _ e ih => exact closed _ ih _ e

/-- Descendant sets checked closed (both conditions decidable) turn "no
enabled pattern reaches another" into a decidable check at each state. -/
theorem anti_of_desc {pat : ι → InterpretedPattern V} {r : ι → ι → Prop} (desc : ι → Finset ι)
    (hsucc : ∀ x b, r x b → b ∈ desc x) (hclosed : ∀ x, ∀ a ∈ desc x, ∀ b, r a b → b ∈ desc x)
    {s : Finset V} (h : ∀ p q, guard (pat p) s → guard (pat q) s → q ∉ desc p) :
    ∀ p q, guard (pat p) s → guard (pat q) s → ¬ Reach r p q :=
  fun p q hp hq reach => h p q hp hq (reach_mem_of_closed (desc p) (hsucc p) (hclosed p) reach)

theorem adm_all {pat : ι → InterpretedPattern V} {r : ι → ι → Prop} (start : Finset V) (goal : V)
    (T : ℕ) : ∀ t : Fin T, PreferenceRiskSeparation.riskAdmissible
      (push (prediction (point start) (coK pat r) (t.val + 1)) (obsK goal))
      (prefK (9 / 10) (by norm_num) (by norm_num)) :=
  fun _ _ d _ _ => prefK_pos (9 / 10) (by norm_num) (by norm_num) d

instance : DecidableRel (containmentOrder chain3) := fun _ _ => by
  unfold containmentOrder; infer_instance
instance : DecidableRel (containmentOrder join3) := fun _ _ => by
  unfold containmentOrder; infer_instance
instance : DecidableRel (containmentOrder agentPats) := fun _ _ => by
  unfold containmentOrder; infer_instance

/-! ## Chain and join of three -/

def descChain : Fin 3 → Finset (Fin 3)
  | 0 => {1, 2} | 1 => {2} | 2 => ∅

def descJoin : Fin 3 → Finset (Fin 3)
  | 0 => {2} | 1 => {2} | 2 => ∅

/-- The chain: one pattern enabled at each state, so co-application is the
list kernel here. Goal at epoch 3. -/
theorem chain3_co :
    totalG (point ∅) (coK chain3 (containmentOrder chain3)) (obsK 3) 3
        (fun _ => prefK (9 / 10) (by norm_num) (by norm_num)) (adm_all ∅ 3 3) =
      2 * Real.log 10 + Real.log (10 / 9) := by
  rw [coScore chain3 _ (fun i => by fin_cases i <;> rfl) ∅ 3 (9 / 10) (by norm_num) (by norm_num) 3
    (fun k hk => anti_of_desc descChain (by decide) (by decide) (by
      interval_cases k <;> decide))]
  have t1 : (nextCo chain3)^[1] (∅ : Finset Tok) = {0} := by decide
  have t2 : (nextCo chain3)^[2] (∅ : Finset Tok) = {0, 1} := by decide
  have t3 : (nextCo chain3)^[3] (∅ : Finset Tok) = {0, 1, 3} := by decide
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, t1, t2, t3]
  simp [prefK, finiteKernel, log_inv_c, log_inv_1c]
  ring

/-- The join: `a` and `b` are both enabled at the start and neither is above
the other, so both fire in epoch 1. Goal at epoch 2. -/
theorem join3_co :
    totalG (point ∅) (coK join3 (containmentOrder join3)) (obsK 3) 3
        (fun _ => prefK (9 / 10) (by norm_num) (by norm_num)) (adm_all ∅ 3 3) =
      Real.log 10 + 2 * Real.log (10 / 9) := by
  rw [coScore join3 _ (fun i => by fin_cases i <;> rfl) ∅ 3 (9 / 10) (by norm_num) (by norm_num) 3
    (fun k hk => anti_of_desc descJoin (by decide) (by decide) (by
      interval_cases k <;> decide))]
  have t1 : (nextCo join3)^[1] (∅ : Finset Tok) = {0, 1} := by decide
  have t2 : (nextCo join3)^[2] (∅ : Finset Tok) = {0, 1, 3} := by decide
  have t3 : (nextCo join3)^[3] (∅ : Finset Tok) = {0, 1, 3} := by decide
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, t1, t2, t3]
  simp [prefK, finiteKernel, log_inv_c, log_inv_1c]
  ring

/-- Under co-application the join scores better than the chain. -/
theorem join_beats_chain :
    Real.log 10 + 2 * Real.log (10 / 9) < 2 * Real.log 10 + Real.log (10 / 9) := by
  have : Real.log (10 / 9) < Real.log 10 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-! ## The seven agent patterns (m40 G7) -/

def descAgent : Fin 7 → Finset (Fin 7)
  | 0 => {1, 2, 3, 4, 5, 6} | 1 => {2, 3, 4, 5, 6} | 2 => {3, 4, 5, 6}
  | 3 => {4, 6} | 4 => {6} | 5 => {6} | 6 => ∅

theorem agent_co_trajectory (k : Fin 8) :
    decide ((6 : AgentTok) ∈ (nextCo agentPats)^[k.val + 1] ∅) = decide (5 ≤ k.val) := by
  revert k; decide

/-- Evidence and trail, both on the dispatch, fire in the same epoch: the goal
is reached at epoch 6 (7 under the list kernel). -/
theorem agent_co :
    totalG (point ∅) (coK agentPats (containmentOrder agentPats)) (obsK 6) 8
        (fun _ => prefK (9 / 10) (by norm_num) (by norm_num)) (adm_all ∅ 6 8) =
      5 * Real.log 10 + 3 * Real.log (10 / 9) := by
  rw [coScore agentPats _ (fun i => by fin_cases i <;> rfl) ∅ 6 (9 / 10) (by norm_num)
    (by norm_num) 8 (fun k hk => anti_of_desc descAgent (by decide) (by decide) (by
      interval_cases k <;> decide))]
  simp only [agent_co_trajectory]
  simp [Fin.sum_univ_succ, prefK, finiteKernel, log_inv_1c]
  rw [← log_inv_c]
  ring

end
end DarkTower.WarMachine.CascadeCoScoringExamples
