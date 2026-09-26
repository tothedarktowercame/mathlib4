import DarkTower.WarMachine.LikelihoodPrecision

/-!
# The β_ζ update: what it lacked (C3, registry `:likelihood-precision`)

WM-LEAN-ABSENT-TRIAGE-D entry C3 asks for "`betaZetaPost` per the row's
`:formal`, in LikelihoodPrecision.lean". **It is already there.**
`LikelihoodPrecision.betaPosterior` (mathlib4 `fd02c510f8`, the very sha the
registry row's `:lean-at` names) is

  `β_post = β_prior + Σ_τ Σ_o Σ_s ((Σ_s' A_ζ s' o · s_τ s') − o_τ o) · ln A s o · s_τ s`

which is the row's `β_ζ-post = β_ζ-prior + Σ_τ (o_ζ,τ − o_τ)·ln A s_τ` with
`o_ζ,τ = A_ζ s_τ`, at eq. B.19's index conventions. `betaPosterior_nil` is the
triage's zero-steps theorem and `betaPosterior_no_surprise` its
perfect-prediction theorem. So C3's declaration is not missing; the triage entry
is stale against the module.

What IS missing is what this module supplies.

## 1. Nothing said the update ever moves

`betaPosterior_nil` and `betaPosterior_no_surprise` both conclude
`= prior.beta`. Two theorems that the sum VANISHES, and none that it ever does
not: together they are equally true of an update defined as the constant prior.
`betaPosterior_moves` is the missing half — one step whose prediction misses,
giving `β_prior + ¼(ln ¼ − ln ¾)`, strictly below the prior. The update is
driven by prediction error, and now something says so.

## 2. The domain `A > 0` is carried by nobody, and three sources disagree

The registry row's `:formal` ends "(domain: A > 0)". `betaPosterior` takes no
such hypothesis, and `Real.log` is junk outside it: `Real.log 0 = 0` and
`Real.log x = Real.log |x|` for `x < 0`. So at `A s o = 0` the term does not
refuse — it contributes ZERO, which is indistinguishable from a term whose
prediction was perfect (`nonpositiveA_contributesZero`). A value stands in for
an undefined one, silently.

And the code admits exactly that case: `temper-row`
(`futon2:src/futon2/aif/likelihood_precision.clj:31-70`) refuses
`:invalid-zeta`, `:negative-zeta`, `:invalid-row` and `:row-not-stochastic` — it
checks that a row is STOCHASTIC, not that it is POSITIVE, and `temper-bernoulli`
documents "p = 0 stays 0, p = 1 stays 1". So the row's domain says `A > 0`, the
code admits `A = 0`, and the Lean neither carries the domain nor refuses outside
it. `betaPosteriorGuarded` is the form that does, with the code's own
`negativeZeta` name for the arm the code has and a `nonpositiveLikelihood` arm
for the one it does not — named differently BECAUSE the code has no refusal for
it, which is the finding rather than a naming choice.

## 3. Nothing connected the posterior to the next step's ζ̄

The row says `ζ̄ = 1/β_ζ`. `expectedPrecision` states that for the prior; nothing
applied it to the POSTERIOR, which is what the next step tempers at.
`nextLikelihood` is `precisionLikelihood (1 / β_post) A`, and
`nextLikelihood_zeroSteps` is the sanity tie: with no steps it is the prior's
own `expectedPrecision`.

## Which `o` this discharges, and over what

The Lean map's R2→R7 carries three terms: `:adjudication-rates`' `o` and
`ref-label` (both made present by C2, entering through `records`) and
`:likelihood-precision`'s own `o`, which was `:absent` because this row's
`:lean` named `precisionLikelihood`, whose binders are `["A", "ζ"]` — no `o` at
all. This module's subject, `betaPosterior`, binds the trial history, and `o`
enters inside it as the first component of each `(o_τ, s_τ)` pair. That is the
`o` C3 discharges, and it enters through `trial`.

**Over what.** The sum runs over ALL of the outcome type `O` (`∑ o, …`), and
`o_τ : O → ℝ` is a vector over all of it. It is NOT restricted to checked
tokens. When `O` is instantiated as `Finset V` for the token carrier, "all of
`O`" means all outcomes over `V` — so a PARTIAL observation must have `V`
already restricted to the checked tokens before the trial is formed, which is
exactly C5's `tokenLikelihood_restrict` (mathlib4 `02f814aa57`). The update does
not need a restriction of its own; it needs its `O` to be the restricted one.

## Why a separate module

`LikelihoodPrecision.lean` is another lane's, and the `Proof2/` siblings (W1,
W2, C1, C2, C5) are each their own module. Everything here is additive: no
declaration there changes, and `betaPosterior` is used exactly as it stands.
-/

namespace DarkTower.WarMachine.Proof2.LikelihoodPrecisionUpdate

open DarkTower.WarMachine.LikelihoodPrecision

/-! ## 1. The update moves -/

section Moves

/-- One step: the state is a point mass on `true`, and the outcome RECORDED is a
point mass on `true` while `fixtureA` predicts `true` with probability ¾. The
prediction misses by ¼. -/
noncomputable def movingTrial : Fin 1 → (Bool → ℝ) × (Bool → ℝ) :=
  fun _ => (fun o => if o then 1 else 0, fun s => if s then 1 else 0)

/-- **`betaPosterior_moves`.** The update is not vacuous: one step with a missed
prediction moves `β` strictly. Without this, `betaPosterior_nil` and
`betaPosterior_no_surprise` are equally true of a constant. -/
theorem betaPosterior_moves (prior : PrecisionPrior) :
    betaPosterior prior fixtureA movingTrial 1
        = prior.beta + (1/4) * (Real.log (1/4) - Real.log (3/4)) ∧
      betaPosterior prior fixtureA movingTrial 1 < prior.beta := by
  have hone : ∀ s o, precisionLikelihood 1 fixtureA s o = fixtureA s o :=
    fun s o => precisionLikelihood_one fixtureA fixtureA_pos fixtureA_colsum s o
  have hval : betaPosterior prior fixtureA movingTrial 1
      = prior.beta + (1/4) * (Real.log (1/4) - Real.log (3/4)) := by
    simp only [betaPosterior, movingTrial, Fin.sum_univ_one, Fintype.sum_bool, hone,
      fixtureA]
    norm_num
    ring
  refine ⟨hval, ?_⟩
  rw [hval]
  have hlog : Real.log (1/4) < Real.log (3/4) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  nlinarith [hlog]

/-- Stated as the inequality the row's reading needs: a prediction that OVERSHOT
the recorded outcome lowers `β`, hence raises `ζ̄ = 1/β`. Confidence goes up when
the tempered prediction was too spread. -/
theorem betaPosterior_moves_ne (prior : PrecisionPrior) :
    betaPosterior prior fixtureA movingTrial 1 ≠ prior.beta :=
  ne_of_lt (betaPosterior_moves prior).2

end Moves

/-! ## 2. The domain, and what happens outside it -/

variable {S O : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] [Nonempty O]

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] [Nonempty O] in
/-- Outside the row's domain the term does not refuse, it VANISHES: `Real.log 0
= 0`, so a zero likelihood entry contributes exactly what a perfect prediction
would. The two are indistinguishable in the sum. -/
theorem nonpositiveA_contributesZero (A : S → O → ℝ) (s : S) (o : O)
    (h : A s o = 0) (x y : ℝ) : x * Real.log (A s o) * y = 0 := by
  rw [h, Real.log_zero, mul_zero, zero_mul]

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] [Nonempty O] in
/-- And a NEGATIVE entry is silently read at its absolute value. -/
theorem negativeA_readsAbsoluteValue (A : S → O → ℝ) (s : S) (o : O) :
    Real.log (A s o) = Real.log |A s o| := (Real.log_abs _).symm

/-- The absences the update can meet. `negativeZeta` is `temper-row`'s own
(`:negative-zeta`, "precision is nonnegative"). `nonpositiveLikelihood` has NO
counterpart in the code: `temper-row` checks that a row is stochastic, not that
it is positive, and `temper-bernoulli` admits `p = 0`. The row's `:formal` says
the domain is `A > 0`, so this arm is the registry's condition, not the code's. -/
inductive UpdateAbsence where
  | negativeZeta (zeta : ℝ)
  | nonpositiveLikelihood

/-- The update with its domain carried rather than assumed. -/
noncomputable def betaPosteriorGuarded (prior : PrecisionPrior) (A : S → O → ℝ)
    {T : ℕ} (trial : Fin T → (O → ℝ) × (S → ℝ)) (ζ : ℝ) : Except UpdateAbsence ℝ :=
  if ζ < 0 then .error (.negativeZeta ζ)
  else if ∀ s o, 0 < A s o then .ok (betaPosterior prior A trial ζ)
  else .error .nonpositiveLikelihood

omit [DecidableEq S] [DecidableEq O] [Nonempty O] in
/-- On its ok arm the guarded update IS `betaPosterior`: the guard adds a domain,
it does not change the equation. -/
theorem betaPosteriorGuarded_ok (prior : PrecisionPrior) (A : S → O → ℝ)
    {T : ℕ} (trial : Fin T → (O → ℝ) × (S → ℝ)) (ζ : ℝ)
    (hz : 0 ≤ ζ) (hA : ∀ s o, 0 < A s o) :
    betaPosteriorGuarded prior A trial ζ = .ok (betaPosterior prior A trial ζ) := by
  simp [betaPosteriorGuarded, not_lt.mpr hz, hA]

/-- Both refusals are reachable. -/
theorem guardRefusalsAreReachable (prior : PrecisionPrior) :
    betaPosteriorGuarded prior fixtureA movingTrial (-1) = .error (.negativeZeta (-1)) ∧
    betaPosteriorGuarded prior (fun _ _ => (0 : ℝ)) movingTrial 1
      = .error .nonpositiveLikelihood := by
  constructor
  · norm_num [betaPosteriorGuarded]
  · simp only [betaPosteriorGuarded, if_neg (by norm_num : ¬ (1 : ℝ) < 0)]
    rw [if_neg]
    intro h
    exact absurd (h true true) (by norm_num)

/-! ## 3. The next step's ζ̄ -/

/-- `ζ̄ = 1/β_ζ` at the POSTERIOR: the precision the next step tempers at. The
row states the reciprocal law; `expectedPrecision` states it for the prior, and
this applies it to the updated rate. -/
noncomputable def nextZeta (prior : PrecisionPrior) (A : S → O → ℝ)
    {T : ℕ} (trial : Fin T → (O → ℝ) × (S → ℝ)) (ζ : ℝ) : ℝ :=
  1 / betaPosterior prior A trial ζ

/-- The likelihood the next step uses: `A_ζ̄` at the updated ζ̄. This is the
definition `tempered-rates` conforms to, one step on. -/
noncomputable def nextLikelihood (prior : PrecisionPrior) (A : S → O → ℝ)
    {T : ℕ} (trial : Fin T → (O → ℝ) × (S → ℝ)) (ζ : ℝ) : S → O → ℝ :=
  precisionLikelihood (nextZeta prior A trial ζ) A

/-- With no steps, the next step tempers at the PRIOR's own expected precision:
the update and the reciprocal law agree where nothing was observed. -/
theorem nextLikelihood_zeroSteps (prior : PrecisionPrior) (A : S → O → ℝ) (ζ : ℝ) :
    nextLikelihood prior A (T := 0) (fun _ => default) ζ
      = precisionLikelihood (expectedPrecision prior) A := by
  simp [nextLikelihood, nextZeta, betaPosterior_nil, expectedPrecision]

/-- And after the moving step it does NOT: the next step tempers at a different
ζ̄ than the prior's, which is the whole point of an update. -/
theorem nextZeta_moves (prior : PrecisionPrior) :
    nextZeta prior fixtureA movingTrial 1 ≠ expectedPrecision prior := by
  unfold nextZeta expectedPrecision
  intro h
  rw [one_div, one_div] at h
  exact betaPosterior_moves_ne prior (inv_injective h)

#print axioms movingTrial
#print axioms betaPosterior_moves
#print axioms betaPosterior_moves_ne
#print axioms nonpositiveA_contributesZero
#print axioms negativeA_readsAbsoluteValue
#print axioms UpdateAbsence
#print axioms betaPosteriorGuarded
#print axioms betaPosteriorGuarded_ok
#print axioms guardRefusalsAreReachable
#print axioms nextZeta
#print axioms nextLikelihood
#print axioms nextLikelihood_zeroSteps
#print axioms nextZeta_moves

end DarkTower.WarMachine.Proof2.LikelihoodPrecisionUpdate
