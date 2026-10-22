import DarkTower.WarMachine.LikelihoodPrecision
import DarkTower.WarMachine.MachineBeliefUpdate

/-!
# Normalised likelihood-tempered machine belief update

Parr, Pezzulo and Friston introduce likelihood precision as Gibbs
reweighting: the partition function is the sum of powered likelihood entries
(`refs/parr2022.txt:12720-12735`, `refs/parr2022.txt:12774-12797`).  Their
equation B.18 writes the precision-weighted prediction using
`sigma (zeta ln A)` (`refs/parr2022.txt:12789-12797`).  Friston et al. state
the categorical observation model as `P(o_t | s_t) = Cat(A)`
(`refs/friston2017.txt:323-334`).  These are source claims; they do not choose
the program's refusal representation or its event-weight-to-precision law.

Our modelling choices are: normalize the powered likelihood over outcomes
separately for each hidden state, then perform an exact Bayes update over
states; represent an invalid update by `Except`; and use
`MachineBeliefUpdate.kappa w = log2 (1 + w)` when the input is an event
weight.  This specifies futon2 commit `5df5853ea` (2026-10-19), semantics
`:wm/likelihood-tempering-semantics-v2`, operator
`:power-then-normalise-over-outcomes-per-state`.

Lean's `Real` contains no NaN or infinity, so the runtime's non-finite-kappa
refusal has no inhabitant here.  `invalidKappa` is the formal refusal for a
negative real kappa; the Clojure boundary additionally rejects non-finite
machine numbers before embedding them as reals.
-/

namespace DarkTower.WarMachine.MachineBeliefUpdateNormalised

open scoped BigOperators
open DarkTower.WarMachine

variable {S O : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype O] [DecidableEq O] [Nonempty O]

/-- Typed failures of the normalised categorical update. -/
inductive UpdateError
  | invalidKappa
  | zeroTemperedColumn
  | zeroEvidence
  deriving DecidableEq, Repr

/-- A finite probability distribution. -/
def IsDistribution (q : S → ℝ) : Prop :=
  (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1

/-- Exact Bayes conditioning for a supplied likelihood model.  The caller is
responsible for establishing nonzero evidence. -/
noncomputable def exactBayesUpdate (L : S → O → ℝ) (prior : S → ℝ) (o : O) : S → ℝ :=
  fun s => L s o * prior s / ∑ s', L s' o * prior s'

/-- Power-normalise `A` over outcomes for each state, then condition the prior
on `o`.  Refuse negative kappa, a zero powered column, or zero observation
evidence. -/
noncomputable def normalisedUpdate (kappa : ℝ) (A : S → O → ℝ)
    (prior : S → ℝ) (o : O) : Except UpdateError (S → ℝ) :=
  if hk : 0 ≤ kappa then
    if hcol : ∀ s, (∑ o', A s o' ^ kappa) ≠ 0 then
      let L := LikelihoodPrecision.precisionLikelihood kappa A
      let evidence := ∑ s, L s o * prior s
      if he : evidence = 0 then
        .error .zeroEvidence
      else
        .ok (fun s => L s o * prior s / evidence)
    else
      .error .zeroTemperedColumn
  else
    .error .invalidKappa

private theorem powered_nonneg (A : S → O → ℝ) (kappa : ℝ)
    (hA : ∀ s o, 0 ≤ A s o) (s : S) (o : O) :
    0 ≤ A s o ^ kappa := by
  exact Real.rpow_nonneg (hA s o) _

/-- Every successful update is a probability distribution. -/
theorem normalisedUpdate_isDistribution (kappa : ℝ) (A : S → O → ℝ)
    (prior : S → ℝ) (o : O) (hA : ∀ s o, 0 ≤ A s o)
    (hprior : IsDistribution prior) {q : S → ℝ}
    (h : normalisedUpdate kappa A prior o = .ok q) :
    IsDistribution q := by
  simp only [normalisedUpdate] at h
  split at h <;> rename_i hk
  · split at h <;> rename_i hcol
    · split at h <;> rename_i he
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst q
        let L := LikelihoodPrecision.precisionLikelihood kappa A
        let evidence := ∑ s, L s o * prior s
        have hden_nonneg (s : S) : 0 ≤ ∑ o', A s o' ^ kappa :=
          Finset.sum_nonneg fun o' _ => powered_nonneg A kappa hA s o'
        have hden_pos (s : S) : 0 < ∑ o', A s o' ^ kappa :=
          lt_of_le_of_ne (hden_nonneg s) (Ne.symm (hcol s))
        have hL (s : S) : 0 ≤ L s o := by
          exact div_nonneg (powered_nonneg A kappa hA s o) (hden_nonneg s)
        have hterm (s : S) : 0 ≤ L s o * prior s :=
          mul_nonneg (hL s) (hprior.1 s)
        have hev_nonneg : 0 ≤ evidence := Finset.sum_nonneg fun s _ => hterm s
        have hev_pos : 0 < evidence := lt_of_le_of_ne hev_nonneg (Ne.symm he)
        constructor
        · intro s
          exact div_nonneg (hterm s) (le_of_lt hev_pos)
        · rw [← Finset.sum_div]
          exact div_self he
    · simp at h
  · simp at h

/-- On success, `normalisedUpdate` is exactly Bayes conditioning with the
precision-normalised likelihood model. -/
theorem normalisedUpdate_eq_exactBayes (kappa : ℝ) (A : S → O → ℝ)
    (prior : S → ℝ) (o : O) {q : S → ℝ}
    (h : normalisedUpdate kappa A prior o = .ok q) :
    q = exactBayesUpdate (LikelihoodPrecision.precisionLikelihood kappa A) prior o := by
  simp only [normalisedUpdate] at h
  split at h
  · split at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst q
        rfl
    · simp at h
  · simp at h

/-- At kappa one, a positive column-stochastic `A` gives the ordinary exact
Bayes update with `A`. -/
theorem normalisedUpdate_one_eq_untempered (A : S → O → ℝ) (prior : S → ℝ)
    (o : O) (Apos : ∀ s o, 0 < A s o) (Acol : ∀ s, ∑ o, A s o = 1)
    {q : S → ℝ} (h : normalisedUpdate 1 A prior o = .ok q) :
    q = exactBayesUpdate A prior o := by
  rw [normalisedUpdate_eq_exactBayes 1 A prior o h]
  congr 1
  funext s o'
  exact LikelihoodPrecision.precisionLikelihood_one A Apos Acol s o'

/-! ### Concrete record of the row-only v1 defect -/

private noncomputable def counterexampleA : Fin 2 → Fin 2 → ℝ :=
  fun s o => if s = 0 then 1 / 2 else if o = 0 then 1 / 4 else 3 / 4

private noncomputable def counterexamplePrior : Fin 2 → ℝ := fun _ => 1 / 2

theorem normalised_counterexample_value :
    normalisedUpdate 2 counterexampleA counterexamplePrior 1 =
      .ok (fun s => if s = 0 then 5 / 14 else 9 / 14) := by
  norm_num [normalisedUpdate, counterexampleA, counterexamplePrior,
    LikelihoodPrecision.precisionLikelihood]
  funext s
  fin_cases s <;> norm_num

/-- The old row-only `categoricalUpdate` is not extensionally equal to the
normalised update.  At kappa two, its posterior for state zero is `4/13`,
whereas the repaired update gives `5/14`. -/
theorem categoricalUpdate_not_always_normalised :
    MachineBeliefUpdate.categoricalUpdate 2
        (fun s => counterexampleA s 1) counterexamplePrior 0 ≠
      (normalisedUpdate 2 counterexampleA counterexamplePrior 1).toOption.getD
        counterexamplePrior 0 := by
  have hvalue :
      (normalisedUpdate 2 counterexampleA counterexamplePrior 1).toOption.getD
          counterexamplePrior 0 = 5 / 14 := by
    rw [normalised_counterexample_value]
    rfl
  rw [hvalue]
  norm_num [MachineBeliefUpdate.categoricalUpdate,
    MachineBeliefUpdate.temperedLikelihood, MachineBeliefUpdate.normalise,
    counterexampleA, counterexamplePrior]

/-- The event-weight interface uses exactly the existing machine kappa law,
`kappa(w) = log(1+w)/log 2`. -/
noncomputable def normalisedUpdateFromWeight (weight : ℝ) (A : S → O → ℝ)
    (prior : S → ℝ) (o : O) : Except UpdateError (S → ℝ) :=
  normalisedUpdate (MachineBeliefUpdate.kappa weight) A prior o

theorem normalisedUpdateFromWeight_uses_machineKappa (weight : ℝ)
    (A : S → O → ℝ) (prior : S → ℝ) (o : O) :
    normalisedUpdateFromWeight weight A prior o =
      normalisedUpdate (MachineBeliefUpdate.kappa weight) A prior o := rfl

#print axioms normalisedUpdate_isDistribution
#print axioms normalisedUpdate_eq_exactBayes
#print axioms normalisedUpdate_one_eq_untempered
#print axioms categoricalUpdate_not_always_normalised
#print axioms normalisedUpdateFromWeight_uses_machineKappa

end DarkTower.WarMachine.MachineBeliefUpdateNormalised
