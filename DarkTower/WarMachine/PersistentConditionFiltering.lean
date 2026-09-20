import DarkTower.WarMachine.ExactBeliefTrajectory

/-!
# Persistent-condition filtering: the z that does not re-draw

The adopted A declaration (futon2 `ADOPTION-a-declaration-2026-09-20.md`)
carries `:z-semantics :per-step-redraw`, declared-as-such because Lean was
silent on the alternative. This module is that transcription: filtering when
the latent condition `z` (the "bad window") is drawn once and PERSISTS.

No new update machinery is defined. Persistent-z filtering is exactly
`ExactBeliefTrajectory.exactUpdate` on the product state space `S × Z` with

- the lifted kernel `liftKernel A (s, z) o = A z s o` (each condition has its
  own observation kernel), and
- the z-diagonal transition `persistTransition B` (states move by `B`, the
  condition stays put),

so `exactUpdate_dist`, `exactUpdate_eq_none_iff` and
`exactUpdate_minimises_vfe` apply verbatim to the joint belief — restated
below as named corollaries so records can cite them.

The other half is `observationProbability_product_belief`: when the joint
belief FACTORS as `q ⊗ w` — state belief times a fixed condition weight, the
situation the runner recreates whenever it re-initializes the z-belief each
step — the predictive observation probability is the `w`-mixture of the
per-condition predictions. That is precisely the computation the
per-step-redraw consumption performs with the marginalized kernel. So:
today's declared semantics computes the persistent model's predictions
exactly as long as nothing carries the z-posterior forward; what
per-step-redraw CANNOT do is learn the condition — after an observation the
joint posterior's z-marginal shifts, and re-drawing discards that shift. A
constructed two-observation witness of the difference is queued; nothing
below depends on it.
-/

namespace DarkTower.WarMachine.PersistentConditionFiltering

open DarkTower.WarMachine.ExactBeliefTrajectory

variable {S O Z : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]

noncomputable section

/-- Each condition `z` carries its own observation kernel. -/
def liftKernel (A : Z → S → O → ℝ) : (S × Z) → O → ℝ :=
  fun p o => A p.2 p.1 o

/-- States move by `B`; the condition persists. -/
def persistTransition (B : S → S → ℝ) : (S × Z) → (S × Z) → ℝ :=
  fun p q => if q.2 = p.2 then B p.1 q.1 else 0

theorem liftKernel_nonneg (A : Z → S → O → ℝ) (hA : ∀ z s o, 0 ≤ A z s o) :
    ∀ p o, 0 ≤ liftKernel A p o :=
  fun p o => hA p.2 p.1 o

theorem persistTransition_nonneg (B : S → S → ℝ) (hB : ∀ s x, 0 ≤ B s x) :
    ∀ (p q : S × Z), 0 ≤ persistTransition B p q := by
  intro p q
  unfold persistTransition
  rcases eq_or_ne q.2 p.2 with h | h
  · simpa [h] using hB p.1 q.1
  · simp [h]

/-- The z-diagonal transition is row-stochastic when `B` is. -/
theorem persistTransition_rowsum (B : S → S → ℝ) (hB1 : ∀ s, ∑ x, B s x = 1) :
    ∀ p : S × Z, ∑ q : S × Z, persistTransition B p q = 1 := by
  intro p
  unfold persistTransition
  rw [Fintype.sum_prod_type]
  calc ∑ x : S, ∑ z : Z, (if z = p.2 then B p.1 x else 0)
      = ∑ x : S, B p.1 x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp
    _ = 1 := hB1 p.1

/-- **Prior prediction factors.** Under a product belief `q ⊗ w` the joint
prior-predictive state is the product of the `B`-pushed state belief and the
unchanged condition weight. -/
theorem predictedState_product_belief (B : S → S → ℝ) (q : S → ℝ) (w : Z → ℝ)
    (x : S) (z : Z) :
    predictedState (persistTransition B) (fun p => q p.1 * w p.2) (x, z)
      = predictedState B q x * w z := by
  unfold predictedState persistTransition
  rw [Fintype.sum_prod_type]
  calc ∑ s₀ : S, ∑ z₀ : Z, (if z = z₀ then B s₀ x else 0) * (q s₀ * w z₀)
      = ∑ s₀ : S, B s₀ x * (q s₀ * w z) := by
        refine Finset.sum_congr rfl fun s₀ _ => ?_
        simp_rw [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp
    _ = (∑ s₀ : S, B s₀ x * q s₀) * w z := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s₀ _ => by ring

/-- **What `:per-step-redraw` computes.** Under a product belief `q ⊗ w`, the
persistent model's predictive observation probability is the `w`-mixture of
per-condition predictions — exactly the marginalized-kernel computation the
per-step-redraw consumption performs. The two semantics agree whenever the
z-belief is re-initialized to `w` each step; they differ only in whether the
z-POSTERIOR is carried forward. -/
theorem observationProbability_product_belief (A : Z → S → O → ℝ)
    (B : S → S → ℝ) (o : O) (q : S → ℝ) (w : Z → ℝ) :
    observationProbability (liftKernel A) (persistTransition B) o
        (fun p => q p.1 * w p.2)
      = ∑ z : Z, w z * ∑ x : S, A z x o * predictedState B q x := by
  unfold observationProbability
  rw [Fintype.sum_prod_type]
  calc ∑ x : S, ∑ z : Z, liftKernel A (x, z) o
          * predictedState (persistTransition B) (fun p => q p.1 * w p.2) (x, z)
      = ∑ x : S, ∑ z : Z, A z x o * (predictedState B q x * w z) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
        rw [predictedState_product_belief]
        rfl
    _ = ∑ z : Z, ∑ x : S, A z x o * (predictedState B q x * w z) := Finset.sum_comm
    _ = ∑ z : Z, w z * ∑ x : S, A z x o * predictedState B q x := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring

/-! ## Inherited update theorems, named for citation -/

/-- The persistent-z posterior is a distribution (inherits `exactUpdate_dist`
on `S × Z`). -/
theorem persistentUpdate_dist (A : Z → S → O → ℝ) (B : S → S → ℝ) (o : O)
    (b : S × Z → ℝ)
    (hA : ∀ z s o, 0 ≤ A z s o) (hB : ∀ s x, 0 ≤ B s x) (hb : ∀ p, 0 ≤ b p)
    {b' : S × Z → ℝ}
    (h : exactUpdate (liftKernel A) (persistTransition B) o b = some b') :
    (∀ p, 0 ≤ b' p) ∧ ∑ p, b' p = 1 :=
  exactUpdate_dist (liftKernel A) (persistTransition B) o b
    (fun p => liftKernel_nonneg A hA p o) (persistTransition_nonneg B hB) hb h

/-- Persistent-z filtering refuses exactly a predictively impossible
observation (inherits `exactUpdate_eq_none_iff`). -/
theorem persistentUpdate_eq_none_iff (A : Z → S → O → ℝ) (B : S → S → ℝ)
    (o : O) (b : S × Z → ℝ) :
    exactUpdate (liftKernel A) (persistTransition B) o b = none
      ↔ observationProbability (liftKernel A) (persistTransition B) o b = 0 :=
  exactUpdate_eq_none_iff (liftKernel A) (persistTransition B) o b

end

end DarkTower.WarMachine.PersistentConditionFiltering

#print axioms DarkTower.WarMachine.PersistentConditionFiltering.persistTransition_rowsum
#print axioms DarkTower.WarMachine.PersistentConditionFiltering.observationProbability_product_belief
#print axioms DarkTower.WarMachine.PersistentConditionFiltering.persistentUpdate_dist
