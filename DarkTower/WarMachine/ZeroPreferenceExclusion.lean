import DarkTower.WarMachine.TokenPreference
import DarkTower.WarMachine.PolicyHorizon
import DarkTower.WarMachine.PolicySelection

/-!
# Zero preference excludes a policy: a consequence of the model, proved

Design P6 (`p4ng/wm-walkthroughs/build-loop/closure/PROPOSAL-wm-model-design-2026-09-16.md`):
ruled-zero outcomes carry preference mass exactly `0`, and a policy that predicts
such an outcome with positive mass must receive posterior probability `0`. This
module proves that from the model, by composing the existing theorems and adding
no hypothesis that assumes any link of the chain:

1. `TokenPreference.PreferenceSpec.preference_eq_zero_iff`: `o ∈ zeroed` gives `C_τ(o) = 0`;
2. `PolicyHorizon.stepRisk`: positive predicted mass on it gives risk `⊤` at `τ`;
3. `PolicyHorizon.horizonEFE_eq_top_iff`: so `G(π) = ⊤` over the horizon;
4. `PolicySelection.selectionWeight_top`: so `π` has posterior `0` at every `γ > 0`.

`PolicyHorizon.horizonEFE` already has the extended-real type `PolicySelection` takes
for `G`, so no bridge lemma is needed between steps 3 and 4.
-/

namespace DarkTower.WarMachine.ZeroPreferenceExclusion

open DarkTower.WarMachine.PolicyRollout DarkTower.WarMachine.PolicyHorizon
  DarkTower.WarMachine.PolicySelection DarkTower.WarMachine.PolicyPrecision
  DarkTower.WarMachine.TokenPreference

variable {S V U ι : Type*} [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] [Fintype ι]

/-- A step whose preference is a `PreferenceSpec` and whose predicted outcome puts
positive mass on a ruled-zero outcome has infinite risk. -/
theorem stepRisk_top_of_zeroed (M : ForwardModel S (Finset V) U) (σ : ℕ → U) (n : ℕ)
    (spec : PreferenceSpec V) (o : Finset V) (ho : o ∈ spec.zeroed)
    (hmass : 0 < predictedOutcome M σ n o) :
    stepRisk M σ n (PreferenceSpec.preference spec) = ⊤ := by
  rw [stepRisk, if_pos ⟨o, hmass, (PreferenceSpec.preference_eq_zero_iff spec o).mpr ho⟩]

/-- **Zero preference excludes the policy.** Let each candidate `π` be a depth-`T`
plan scored by `G(π) = horizonEFE` with a step-indexed preference `C`. If at some step
`τ ≤ T` the preference is a `PreferenceSpec` and `π₀`'s predicted outcome there puts
positive mass on a ruled-zero outcome, then `π₀` has posterior probability `0` at every
temperature. The other steps' preferences are arbitrary distributions. -/
theorem selectionPosterior_eq_zero_of_zeroed (M : ForwardModel S (Finset V) U) {T : ℕ}
    (hT : 0 < T) (plan : ι → Fin T → U) (C : ℕ → Finset V → ℝ)
    (hC0 : ∀ n o, 0 ≤ C n o) (hC1 : ∀ n, ∑ o, C n o = 1)
    (spec : PreferenceSpec V) (i : Fin T) (hCi : C (i.val + 1) = PreferenceSpec.preference spec)
    (π₀ : ι) (o : Finset V) (ho : o ∈ spec.zeroed)
    (hmass : 0 < predictedOutcome M (policySeq hT (plan π₀)) (i.val + 1) o)
    (t : PolicyTemperature) (habit F : ι → ℝ) :
    selectionPosterior t habit F (fun π => horizonEFE M hT (plan π) C) π₀ = 0 := by
  have hrisk : stepRisk M (policySeq hT (plan π₀)) (i.val + 1) (C (i.val + 1)) = ⊤ := by
    rw [hCi]
    exact stepRisk_top_of_zeroed M _ _ spec o ho hmass
  have hG : horizonEFE M hT (plan π₀) C = ⊤ :=
    (horizonEFE_eq_top_iff M hT (plan π₀) C hC0 hC1).mpr ⟨i, hrisk⟩
  rw [selectionPosterior, selectionWeight_top t habit F _ π₀ hG, ENNReal.zero_div]

/-- The usual way to supply `C`: the `PreferenceSpec` at step `τ`, any other
distribution family elsewhere. It meets the distribution hypotheses. -/
noncomputable def preferenceAt (spec : PreferenceSpec V) (τ : ℕ) (D : ℕ → Finset V → ℝ) :
    ℕ → Finset V → ℝ :=
  fun n => if n = τ then PreferenceSpec.preference spec else D n

theorem preferenceAt_nonneg (spec : PreferenceSpec V) (τ : ℕ) (D : ℕ → Finset V → ℝ)
    (hD0 : ∀ n o, 0 ≤ D n o) (n : ℕ) (o : Finset V) : 0 ≤ preferenceAt spec τ D n o := by
  unfold preferenceAt
  split_ifs
  · exact PreferenceSpec.preference_nonneg spec o
  · exact hD0 n o

theorem preferenceAt_sum (spec : PreferenceSpec V) (τ : ℕ) (D : ℕ → Finset V → ℝ)
    (hD1 : ∀ n, ∑ o, D n o = 1) (n : ℕ) : ∑ o, preferenceAt spec τ D n o = 1 := by
  unfold preferenceAt
  split_ifs
  · exact PreferenceSpec.preference_sum spec
  · exact hD1 n

/-! ## Fixture: Fin 3 tokens, the outcome `{2}` ruled zero -/

namespace Fixture

/-- The P6 fixture specification with `{2}` ruled zero. -/
def c1 : PreferenceSpec (Fin 3) where
  want := {0, 1}
  want_nonempty := by decide
  evidence := {2}
  lam := 1
  mu := 1
  lam_pos := by norm_num
  mu_nonneg := by norm_num
  zeroed := {{2}}
  zeroed_proper := by decide

/-- Action `true` establishes token `2`; `false` changes nothing. Observation is exact.
The present state is `∅`. -/
noncomputable def model : ForwardModel (Finset (Fin 3)) (Finset (Fin 3)) Bool where
  B := fun u s s' => if s' = (if u then s ∪ {2} else s) then 1 else 0
  B_nonneg := by intro u s s'; split_ifs <;> norm_num
  B_rowsum := by intro u s; simp
  A := fun s o => if o = s then 1 else 0
  A_nonneg := by intro s o; split_ifs <;> norm_num
  A_colsum := by intro s; simp
  q₀ := fun s => if s = ∅ then 1 else 0
  q₀_nonneg := by intro s; split_ifs <;> norm_num
  q₀_sum := by simp

/-- Two one-step candidates: `true` establishes token `2`, `false` does nothing. -/
def plan : Bool → Fin 1 → Bool := fun b _ => b

theorem establish_predicts_zeroed :
    0 < predictedOutcome model (policySeq Nat.one_pos (plan true)) 1 {2} := by
  rw [predictedOutcome_one]
  rw [Finset.sum_eq_single ({2} : Finset (Fin 3))]
  · rw [Finset.sum_eq_single (∅ : Finset (Fin 3))]
    · simp [model, policySeq, plan]
    · intro b _ hb
      simp [model, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    have : (if ({2} : Finset (Fin 3)) = b then (1 : ℝ) else 0) = 0 := if_neg (Ne.symm hb)
    simp only [model]
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The candidate that establishes the ruled-zero outcome has posterior 0**, at
every temperature, with the preference `c1` at the single step. -/
theorem fixture_excluded (t : PolicyTemperature) (habit F : Bool → ℝ) :
    selectionPosterior t habit F
      (fun π => horizonEFE model Nat.one_pos (plan π) (fun _ => PreferenceSpec.preference c1))
      true = 0 :=
  selectionPosterior_eq_zero_of_zeroed model Nat.one_pos plan _
    (fun _ o => PreferenceSpec.preference_nonneg c1 o)
    (fun _ => PreferenceSpec.preference_sum c1) c1 0 rfl true {2} (by simp [c1])
    establish_predicts_zeroed t habit F

end Fixture

end DarkTower.WarMachine.ZeroPreferenceExclusion
