import DarkTower.WarMachine.GTotalMarginalInvariance

/-!
# Total G for general state beliefs: the mutual-information decomposition

Completes the queued transcription "dependence-correct risk/ambiguity for
non-point-mass beliefs" (futon2 `SPEC-a-model-conformance-2026-09-20.md`),
extending `GTotalMarginalInvariance` beyond point masses.

For a state belief `b` and observation kernel `A`, the predicted observation
law is `q(o) = ∑ₛ b(s)·A(o|s)`, the ambiguity term is the expected
conditional entropy `∑ₛ b(s)·H[A(·|s)]`, and the risk term is the Gibbs sum
of `q` against the preference `C`. Then

  risk + ambiguity = crossTerm(q, C) − MI(b, A)

where `MI(b,A) = H[q] − ∑ₛ b(s)·H[A(·|s)]` is the mutual information between
state and observation under the joint `b(s)·A(o|s)`. Consequences proved
here:

- the point-mass case has `MI = 0`, recovering the cancellation of
  `GTotalMarginalInvariance` exactly;
- against a positive product-form preference, two (belief, kernel) pairs
  whose predicted observation laws match in total mass and per-token
  marginals differ in total G by EXACTLY the difference of their mutual
  informations. Dependence enters total G through MI and nowhere else —
  which is the precise content of "per-token G sums are unlicensed for
  coupled kernels": a per-token sum cannot see MI.

Not proved here (honestly queued): `MI ≥ 0` (Jensen/concavity), which would
give the sign of the coupling effect; nothing below depends on it.
-/

namespace DarkTower.WarMachine.GNonPointMassDecomposition

open DarkTower.WarMachine.GTotalMarginalInvariance

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- Predicted observation law of belief `b` through kernel `A`. -/
def predObs (b : Finset V → ℝ) (A : Finset V → Finset V → ℝ) :
    Finset V → ℝ :=
  fun o => ∑ s : Finset V, b s * A s o

/-- Ambiguity: expected conditional entropy of the observation given the
state, under belief `b`. -/
def ambiguity (b : Finset V → ℝ) (A : Finset V → Finset V → ℝ) : ℝ :=
  ∑ s : Finset V, b s * entropy (A s)

/-- Mutual information between state and observation under the joint
`b(s)·A(o|s)`: predicted-law entropy minus expected conditional entropy. -/
def mutualInfo (b : Finset V → ℝ) (A : Finset V → Finset V → ℝ) : ℝ :=
  entropy (predObs b A) - ambiguity b A

/-- **The general decomposition.** For any belief, kernel, and preference
positive on all outcomes:
`risk(q,C) + ambiguity(b,A) = −∑ₒ q(o)·log C(o) − MI(b,A)`. -/
theorem risk_add_ambiguity (b : Finset V → ℝ) (A : Finset V → Finset V → ℝ)
    (C : Finset V → ℝ)
    (hq : ∀ o, 0 ≤ predObs b A o) (hC : ∀ o, 0 < C o) :
    risk (predObs b A) C + ambiguity b A
      = (-∑ o : Finset V, predObs b A o * Real.log (C o))
        - mutualInfo b A := by
  have h := risk_add_entropy (V := V) (predObs b A) C hq hC
  unfold mutualInfo
  linarith [h]

/-- A point mass at `s₀`. -/
def pointMass (s₀ : Finset V) : Finset V → ℝ :=
  fun s => if s = s₀ then 1 else 0

theorem predObs_pointMass (s₀ : Finset V) (A : Finset V → Finset V → ℝ) :
    predObs (pointMass s₀) A = A s₀ := by
  funext o
  unfold predObs pointMass
  rw [Finset.sum_eq_single s₀]
  · simp
  · intro s _ hs; simp [hs]
  · intro h; exact absurd (Finset.mem_univ s₀) h

theorem ambiguity_pointMass (s₀ : Finset V) (A : Finset V → Finset V → ℝ) :
    ambiguity (pointMass s₀) A = entropy (A s₀) := by
  unfold ambiguity pointMass
  rw [Finset.sum_eq_single s₀]
  · simp
  · intro s _ hs; simp [hs]
  · intro h; exact absurd (Finset.mem_univ s₀) h

/-- **Point masses carry zero mutual information**, so the general
decomposition collapses to the `GTotalMarginalInvariance` cancellation. -/
theorem mutualInfo_pointMass (s₀ : Finset V) (A : Finset V → Finset V → ℝ) :
    mutualInfo (pointMass s₀) A = 0 := by
  unfold mutualInfo
  rw [predObs_pointMass, ambiguity_pointMass]
  ring

/-- **Dependence enters total G through MI and nowhere else.** Against a
positive product-form preference, if two (belief, kernel) pairs produce
predicted laws with equal total mass and equal per-token marginals, their
total-G difference is exactly the difference of their mutual informations. -/
theorem totalG_sub_eq_mutualInfo_sub
    (b₁ b₂ : Finset V → ℝ) (A₁ A₂ : Finset V → Finset V → ℝ)
    (cIn cOut : V → ℝ)
    (hq₁ : ∀ o, 0 ≤ predObs b₁ A₁ o) (hq₂ : ∀ o, 0 ≤ predObs b₂ A₂ o)
    (hIn : ∀ v, 0 < cIn v) (hOut : ∀ v, 0 < cOut v)
    (hmass : ∑ o : Finset V, predObs b₁ A₁ o = ∑ o : Finset V, predObs b₂ A₂ o)
    (hmarg : ∀ v, margIn (predObs b₁ A₁) v = margIn (predObs b₂ A₂) v) :
    (risk (predObs b₁ A₁) (fun o => ∏ v, (if v ∈ o then cIn v else cOut v))
        + ambiguity b₁ A₁)
      - (risk (predObs b₂ A₂) (fun o => ∏ v, (if v ∈ o then cIn v else cOut v))
          + ambiguity b₂ A₂)
      = mutualInfo b₂ A₂ - mutualInfo b₁ A₁ := by
  have hC : ∀ o : Finset V, 0 < ∏ v, (if v ∈ o then cIn v else cOut v) := by
    intro o
    refine Finset.prod_pos fun v _ => ?_
    by_cases hv : v ∈ o
    · simpa [hv] using hIn v
    · simpa [hv] using hOut v
  have h₁ := risk_add_ambiguity b₁ A₁ _ hq₁ hC
  have h₂ := risk_add_ambiguity b₂ A₂ _ hq₂ hC
  have hcross :
      -∑ o : Finset V, predObs b₁ A₁ o
          * Real.log (∏ v, (if v ∈ o then cIn v else cOut v))
        = -∑ o : Finset V, predObs b₂ A₂ o
            * Real.log (∏ v, (if v ∈ o then cIn v else cOut v)) := by
    rw [cross_term_product (predObs b₁ A₁) cIn cOut hIn hOut,
      cross_term_product (predObs b₂ A₂) cIn cOut hIn hOut, hmass]
    simp_rw [hmarg]
  linarith [h₁, h₂, hcross]

end

end DarkTower.WarMachine.GNonPointMassDecomposition

#print axioms DarkTower.WarMachine.GNonPointMassDecomposition.risk_add_ambiguity
#print axioms DarkTower.WarMachine.GNonPointMassDecomposition.mutualInfo_pointMass
#print axioms DarkTower.WarMachine.GNonPointMassDecomposition.totalG_sub_eq_mutualInfo_sub
