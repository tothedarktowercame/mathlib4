import DarkTower.WarMachine.ScanLearning

/-!
# Adopted-channel shadow update

The shadow applies integrated likelihoods only for keys in both the tick's
used set and the predecessor's adopted set (PROOF-2a decision 6B-8).
-/

namespace DarkTower.WarMachine.ScanShadow

open scoped BigOperators
open DarkTower.WarMachine.DirichletLearning
open DarkTower.WarMachine.ExactBeliefTrajectory
open DarkTower.WarMachine.ScanLearning

noncomputable section

variable {K O S : Type*}

/-- Identity transition: the shadow starts from this tick's already-filtered
`mu-excl`, so `scan_shadow.clj:55-89` performs no further prediction. -/
def identityTransition [DecidableEq S] (previous next : S) : ℝ :=
  if previous = next then 1 else 0

/-- `scan_shadow.clj:55-89`, `shadow-row`: exact normalization of `mu-excl`
times the integrated likelihood from used-and-adopted keys only. -/
def scanShadow [Fintype K] [DecidableEq K] [Fintype O] [Nonempty O] [Fintype S] [DecidableEq S]
    (muExcl : S → ℝ) (used adopted : Finset K)
    (alpha : K → DirichletParams O S) (counts : K → O → ℕ) : Option (S → ℝ) :=
  exactUpdate
    (fun s (_ : Unit) => Real.exp (scanStatusLogLikelihood (used ∩ adopted) alpha counts s))
    identityTransition () muExcl

/-- Prediction through the identity transition returns the supplied belief. -/
theorem predictedState_identity [Fintype S] [DecidableEq S]
    (mu : S → ℝ) (s : S) : predictedState identityTransition mu s = mu s := by
  simp [predictedState, identityTransition]

/-- `scan_shadow.clj:63`: with no used adopted key, a normalized nonnegative
row is returned identically. The runtime's unchanged map is explicitly assumed
to be a probability row. -/
theorem scanShadow_empty [Fintype K] [DecidableEq K] [Fintype O] [Nonempty O]
    [Fintype S] [DecidableEq S]
    (muExcl : S → ℝ) (used adopted : Finset K)
    (alpha : K → DirichletParams O S) (counts : K → O → ℕ)
    (hempty : used ∩ adopted = ∅) (hnonneg : ∀ s, 0 ≤ muExcl s)
    (hsum : ∑ s, muExcl s = 1) :
    scanShadow muExcl used adopted alpha counts = some muExcl := by
  unfold scanShadow exactUpdate observationProbability
  simp [hempty, scanStatusLogLikelihood, predictedState_identity, hsum]

/-- `scan_shadow.clj:77-89`: zero prior mass remains zero after a successful
shadow update. -/
theorem scanShadow_zero [Fintype K] [DecidableEq K] [Fintype O] [Nonempty O]
    [Fintype S] [DecidableEq S]
    (muExcl : S → ℝ) (used adopted : Finset K)
    (alpha : K → DirichletParams O S) (counts : K → O → ℕ) (q : S → ℝ)
    (h : scanShadow muExcl used adopted alpha counts = some q)
    (s : S) (hz : muExcl s = 0) : q s = 0 := by
  unfold scanShadow exactUpdate at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    subst q
    simp [predictedState_identity, hz]

/-- `scan_shadow.clj:74-81` and decision 6B-8(i): changing any parameters or
counts outside `used ∩ adopted` (including tied and unadopted keys) cannot
change the shadow. -/
theorem scanShadow_ignores_unadopted [Fintype K] [DecidableEq K] [Fintype O] [Nonempty O]
    [Fintype S] [DecidableEq S]
    (muExcl : S → ℝ) (used adopted : Finset K)
    (alpha alpha' : K → DirichletParams O S) (counts counts' : K → O → ℕ)
    (ha : ∀ k ∈ used ∩ adopted, alpha k = alpha' k)
    (hc : ∀ k ∈ used ∩ adopted, counts k = counts' k) :
    scanShadow muExcl used adopted alpha counts =
      scanShadow muExcl used adopted alpha' counts' := by
  apply congrArg (fun likelihood => exactUpdate likelihood identityTransition () muExcl)
  funext s u
  congr 1
  unfold scanStatusLogLikelihood
  apply Finset.sum_congr rfl
  intro k hk
  simpa [ha k hk, hc k hk]

/-- `scan_shadow.clj:74-89`: closed normalized form of every successful
shadow row. -/
theorem scanShadow_some [Fintype K] [DecidableEq K] [Fintype O] [Nonempty O]
    [Fintype S] [DecidableEq S]
    (muExcl : S → ℝ) (used adopted : Finset K)
    (alpha : K → DirichletParams O S) (counts : K → O → ℕ) (q : S → ℝ)
    (h : scanShadow muExcl used adopted alpha counts = some q) (s : S) :
    q s = muExcl s * Real.exp (scanStatusLogLikelihood (used ∩ adopted) alpha counts s) /
      ∑ t, muExcl t * Real.exp (scanStatusLogLikelihood (used ∩ adopted) alpha counts t) := by
  unfold scanShadow exactUpdate at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    subst q
    simp only [predictedState_identity]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro t ht
      simp [predictedState_identity, mul_comm]

/-- `scan_shadow.clj:82-85`: refusal is exactly a zero normalizer in the real
model. The runtime additionally refuses non-finite machine doubles; Lean reals
have no NaN/infinity values. -/
theorem scanShadow_none_iff [Fintype K] [DecidableEq K] [Fintype O] [Nonempty O]
    [Fintype S] [DecidableEq S]
    (muExcl : S → ℝ) (used adopted : Finset K)
    (alpha : K → DirichletParams O S) (counts : K → O → ℕ) :
    scanShadow muExcl used adopted alpha counts = none ↔
      (∑ t, muExcl t * Real.exp
        (scanStatusLogLikelihood (used ∩ adopted) alpha counts t)) = 0 := by
  unfold scanShadow
  rw [exactUpdate_eq_none_iff]
  unfold observationProbability
  simp only [predictedState_identity]
  constructor <;> intro h
  · simpa [mul_comm] using h
  · simpa [mul_comm] using h

#print axioms predictedState_identity
#print axioms scanShadow_empty
#print axioms scanShadow_zero
#print axioms scanShadow_ignores_unadopted
#print axioms scanShadow_some
#print axioms scanShadow_none_iff

end

end DarkTower.WarMachine.ScanShadow
