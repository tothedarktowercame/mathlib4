import Mathlib
import DarkTower.WarMachine.PolicyRollout

/-!
# WM-04 (design P5): observation model `A` over token states

One observation follows each application. `A` reports the established-token
state: checkable tokens whose class token is an artefact fact (a file exists,
a commit exists) are observed exactly; for tests, what is observed exactly is
only the C8 record-shaped token — the test registry holds a warrant for the
named namespace whose pinned code-path and test-path shas equal current
content, postcheck matched, zero failures and zero errors (observation
contract `resources/wm/observation-contract.edn` `:C8`; H-A-CONSUMER-D, futon2
`6059ecbc`) — not the bare proposition "the tests pass", which the contract's
`:stated-conditions-rule` assigns to class J. Tokens needing judgement carry
an adjudication error rate (`falseNeg`/`falsePos`). With all rates zero the
kernel is the identity on
`Finset V`, so the predicted observation distribution coincides with the
predicted state distribution of `PolicyRollout.ForwardModel`.

Design: `p4ng/wm-walkthroughs/build-loop/closure/PROPOSAL-wm-model-design-2026-09-16.md`
(P5, approved 2026-09-16). Specification:
`futon2/holes/labs/wm-contract/SPEC-cascade-policy-semantics-2026-09-15.md`.

This module imports `PolicyRollout` only; it does not touch `Holes.lean`
(frozen) or `TokenState.lean` (owned by WM-02).
-/

namespace DarkTower.WarMachine.TokenObservation

open DarkTower.WarMachine.PolicyRollout

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjudication rates for judgement-needing tokens: `falseNeg v` is the
probability that an established token `v` is missed; `falsePos v` the
probability that a non-established token `v` is reported. Each lies in `[0,1]`. -/
structure AdjudicationRates (V : Type*) where
  falseNeg : V → ℝ
  falsePos : V → ℝ
  falseNeg_mem : ∀ v, falseNeg v ∈ Set.Icc (0 : ℝ) 1
  falsePos_mem : ∀ v, falsePos v ∈ Set.Icc (0 : ℝ) 1

/-- The token observation kernel: `A(o | s)`, a product of independent
per-token adjudication probabilities. Checkable tokens correspond to rate 0. -/
def tokenLikelihood (r : AdjudicationRates V) (s o : Finset V) : ℝ :=
  ∏ v, (if v ∈ s then (if v ∈ o then 1 - r.falseNeg v else r.falseNeg v)
        else (if v ∈ o then r.falsePos v else 1 - r.falsePos v))

theorem tokenLikelihood_nonneg (r : AdjudicationRates V) (s o : Finset V) :
    0 ≤ tokenLikelihood r s o := by
  refine Finset.prod_nonneg fun v _ => ?_
  by_cases hs : v ∈ s
  · by_cases ho : v ∈ o
    · simp only [tokenLikelihood, if_pos hs, if_pos ho]
      exact sub_nonneg.mpr (r.falseNeg_mem v).2
    · simp only [tokenLikelihood, if_pos hs, if_neg ho]
      exact (r.falseNeg_mem v).1
  · by_cases ho : v ∈ o
    · simp only [tokenLikelihood, if_neg hs, if_pos ho]
      exact (r.falsePos_mem v).1
    · simp only [tokenLikelihood, if_neg hs, if_neg ho]
      exact sub_nonneg.mpr (r.falsePos_mem v).2

/-! ## Bijection with membership functions (route of `TokenState.independentBelief_sum`,
mathlib4 `17fb61d038`) -/

private def toBoolFun (o : Finset V) : V → Bool := fun v => decide (v ∈ o)

private def ofBoolFun (h : V → Bool) : Finset V := Finset.univ.filter (fun v => h v = true)

private theorem ofBoolFun_toBoolFun (o : Finset V) : ofBoolFun (toBoolFun o) = o := by
  ext v
  simp [ofBoolFun, toBoolFun]

private theorem toBoolFun_ofBoolFun (h : V → Bool) : toBoolFun (ofBoolFun h) = h := by
  funext v
  cases hv : h v <;> simp [toBoolFun, ofBoolFun, hv]

private def obsBoolEquiv : Finset V ≃ (V → Bool) where
  toFun := toBoolFun
  invFun := ofBoolFun
  left_inv := ofBoolFun_toBoolFun
  right_inv := toBoolFun_ofBoolFun

/-- Per-token factor as a function of the Boolean membership report. -/
private def tokenFac (r : AdjudicationRates V) (s : Finset V) (v : V) (b : Bool) : ℝ :=
  if v ∈ s then (if b then 1 - r.falseNeg v else r.falseNeg v)
  else (if b then r.falsePos v else 1 - r.falsePos v)

theorem tokenLikelihood_colsum (r : AdjudicationRates V) (s : Finset V) :
    ∑ o : Finset V, tokenLikelihood r s o = 1 := by
  classical
  have key1 : ∑ o : Finset V, tokenLikelihood r s o
      = ∑ h : V → Bool, ∏ v, tokenFac r s v (h v) := by
    refine Fintype.sum_equiv obsBoolEquiv _ _ fun o => ?_
    show (∏ v, (if v ∈ s then (if v ∈ o then 1 - r.falseNeg v else r.falseNeg v)
          else (if v ∈ o then r.falsePos v else 1 - r.falsePos v)))
        = ∏ v, tokenFac r s v (toBoolFun o v)
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [toBoolFun, decide_eq_true_eq, tokenFac]
  have step2 : (∑ h : V → Bool, ∏ v, tokenFac r s v (h v))
      = ∏ v, ∑ b : Bool, tokenFac r s v b :=
    (Fintype.prod_sum (fun (v : V) (b : Bool) => tokenFac r s v b)).symm
  have per : ∀ v : V, ∑ b : Bool, tokenFac r s v b = 1 := by
    intro v
    by_cases hv : v ∈ s
    · simp only [tokenFac, if_pos hv, Fintype.sum_bool]
      simp
    · simp only [tokenFac, if_neg hv, Fintype.sum_bool]
      simp
  rw [key1, step2, Finset.prod_eq_one fun v _ => per v]

/-! ## Checkable tokens -/

theorem tokenLikelihood_checkable (r : AdjudicationRates V)
    (hfn : ∀ v, r.falseNeg v = 0) (hfp : ∀ v, r.falsePos v = 0) (s o : Finset V) :
    tokenLikelihood r s o = if o = s then 1 else 0 := by
  by_cases h : o = s
  · subst h
    have h1 : tokenLikelihood r o o = 1 := by
      unfold tokenLikelihood
      refine Finset.prod_eq_one fun v _ => ?_
      by_cases hv : v ∈ o
      · simp [hfn v, hv]
      · simp [hfp v, hv]
    rw [h1]
    simp
  · have hdis : ∃ v : V, (v ∈ s ∧ v ∉ o) ∨ (v ∉ s ∧ v ∈ o) := by
      by_contra hcon
      apply h
      apply Finset.ext
      intro v
      by_cases h1 : v ∈ s <;> by_cases h2 : v ∈ o
      · exact ⟨fun _ => h1, fun _ => h2⟩
      · exact absurd ⟨v, Or.inl ⟨h1, h2⟩⟩ hcon
      · exact absurd ⟨v, Or.inr ⟨h1, h2⟩⟩ hcon
      · exact ⟨fun hv => absurd hv h2, fun hv => absurd hv h1⟩
    obtain ⟨v, hv | hv⟩ := hdis
    · have hz : tokenLikelihood r s o = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v) (by
          simp only [tokenLikelihood, if_pos hv.1, if_neg hv.2, hfn v])
      rw [hz, if_neg h]
    · have hz : tokenLikelihood r s o = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v) (by
          simp only [tokenLikelihood, if_neg hv.1, if_pos hv.2, hfp v])
      rw [hz, if_neg h]

/-! ## Rollout compatibility -/

/-- `tokenLikelihood` satisfies the two kernel obligations of
`PolicyRollout.ForwardModel`'s `A` field, so it can be supplied as `A`. -/
def observationKernelOK (r : AdjudicationRates V) :
    (∀ s o : Finset V, 0 ≤ tokenLikelihood r s o)
      ∧ ∀ s : Finset V, ∑ o : Finset V, tokenLikelihood r s o = 1 :=
  ⟨fun s o => tokenLikelihood_nonneg r s o, fun s => tokenLikelihood_colsum r s⟩

variable {U : Type*}

/-- With zero adjudication rates (all tokens checkable) the kernel is the
identity, so for any `ForwardModel` on `Finset V` states and observations whose
`A` is `tokenLikelihood r`, the predicted observation distribution equals the
predicted state distribution. -/
theorem predictedOutcome_eq_rolloutState (r : AdjudicationRates V)
    (hfn : ∀ v, r.falseNeg v = 0) (hfp : ∀ v, r.falsePos v = 0)
    (M : ForwardModel (Finset V) (Finset V) U) (hA : M.A = tokenLikelihood r)
    (π : ℕ → U) (n : ℕ) (o : Finset V) :
    predictedOutcome M π n o = rolloutState M π n o := by
  simp only [predictedOutcome, hA, tokenLikelihood_checkable r hfn hfp]
  rw [Finset.sum_eq_single o]
  · simp
  · intro x _ hx
    rw [if_neg (fun hc => hx (hc.symm))]
    ring
  · intro ho
    exact absurd ho (fun h => h (Finset.mem_univ o))

/-! ## Fixtures on `V = Fin 2` -/

private def zeroRates : AdjudicationRates (Fin 2) where
  falseNeg := fun _ => 0
  falsePos := fun _ => 0
  falseNeg_mem := fun _ => by simp
  falsePos_mem := fun _ => by simp

theorem tokenLikelihood_zeroRates_identity (s o : Finset (Fin 2)) :
    tokenLikelihood zeroRates s o = if o = s then 1 else 0 :=
  tokenLikelihood_checkable zeroRates (fun _ => rfl) (fun _ => rfl) s o

private noncomputable def noisyRates : AdjudicationRates (Fin 2) where
  falseNeg := fun v => if v = 0 then 1 / 10 else 0
  falsePos := fun _ => 0
  falseNeg_mem := by
    intro v
    by_cases hv : v = 0
    · simp only [hv, if_pos rfl]
      norm_num
    · simp only [hv, if_neg]
      norm_num
  falsePos_mem := fun _ => by simp

theorem tokenLikelihood_noisy_miss :
    tokenLikelihood noisyRates {0} (∅ : Finset (Fin 2)) = 1 / 10 := by
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  simp only [tokenLikelihood, hu, Finset.prod_insert, Finset.prod_singleton,
    Finset.mem_singleton, noisyRates]
  norm_num

theorem tokenLikelihood_noisy_hit :
    tokenLikelihood noisyRates {0} ({0} : Finset (Fin 2)) = 9 / 10 := by
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  simp only [tokenLikelihood, hu, Finset.prod_insert, Finset.prod_singleton,
    Finset.mem_singleton, noisyRates]
  norm_num

end DarkTower.WarMachine.TokenObservation
