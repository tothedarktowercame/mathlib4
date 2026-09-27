import DarkTower.WarMachine.Proof2.LikelihoodPrecisionUpdate

/-!
# B.19 with a likelihood recorded for each trial

Runtime bindings: `futon2.aif.zeta-posterior/beta-posterior` computes this sum;
`trajectory-posterior` supplies the ordered history and the original declared
prior; `lane-options` supplies the resulting mean to the next token-rates lane.
Each A_τ is that lane's recorded raw token-rates likelihood. The tempered product
is supplied by `likelihood-precision/tempered-rates`. The state is the predicted
state, not the prior or the posterior. The observation domain is the checked-token
restriction used to construct the trial, with the sum over ALL outcomes there.

As in the fixed-A binding, ζ is one scalar shared by the family; this is the
scalar-ζ simplification of B.19, not its row-vector generalisation. All historical
terms are recomputed at ONE current ζ from the original prior, not accumulated
using the preceding posterior as a new prior. `betaPosteriorVar_const` establishes
coincidence with the existing fixed-A equation. The fixed-A module is unchanged.

The guard reuses `UpdateAbsence`: negative ζ and any nonpositive historical cell
are refused. It does not add the runtime's separate positive-posterior-rate guard;
`nextLikelihoodVar` states the reciprocal law, whose probabilistic use requires a
positive posterior rate. With no trials the historical-cell condition is vacuous.
-/

namespace DarkTower.WarMachine.Proof2.LikelihoodPrecisionVariableA

open DarkTower.WarMachine.LikelihoodPrecision
open DarkTower.WarMachine.Proof2.LikelihoodPrecisionUpdate

variable {S O : Type*} [Fintype S] [Fintype O]

/-- B.19 with each trial's own likelihood in both the tempered prediction and
`log A_τ`. ζ remains the shared scalar simplification of the fixed-A binding. -/
noncomputable def betaPosteriorVar (prior : PrecisionPrior) {T : ℕ}
    (trial : Fin T → (S → O → ℝ) × (O → ℝ) × (S → ℝ)) (ζ : ℝ) : ℝ :=
  prior.beta + ∑ τ : Fin T, ∑ o, ∑ s,
    ((∑ s', precisionLikelihood ζ (trial τ).1 s' o * (trial τ).2.2 s')
      - (trial τ).2.1 o) * Real.log ((trial τ).1 s o) * (trial τ).2.2 s

/-- Constant historical likelihoods recover the existing binding exactly. -/
theorem betaPosteriorVar_const (prior : PrecisionPrior) (A : S → O → ℝ)
    {T : ℕ} (trial' : Fin T → (O → ℝ) × (S → ℝ)) (ζ : ℝ) :
    betaPosteriorVar prior (fun τ => (A, (trial' τ).1, (trial' τ).2)) ζ
      = betaPosterior prior A trial' ζ := by
  rfl

/-- An empty history leaves the declared prior unchanged. -/
theorem betaPosteriorVar_nil (prior : PrecisionPrior)
    (trial : Fin 0 → (S → O → ℝ) × (O → ℝ) × (S → ℝ)) (ζ : ℝ) :
    betaPosteriorVar prior trial ζ = prior.beta := by
  simp [betaPosteriorVar]

/-- Every historical cell in the finite sum must be positive, even when its
state mass is zero: no silent `log 0` contribution. Reuses the fixed-A carrier. -/
noncomputable def betaPosteriorVarGuarded (prior : PrecisionPrior) {T : ℕ}
    (trial : Fin T → (S → O → ℝ) × (O → ℝ) × (S → ℝ)) (ζ : ℝ)
    : Except UpdateAbsence ℝ :=
  if ζ < 0 then .error (.negativeZeta ζ)
  else if ∀ τ s o, 0 < (trial τ).1 s o then .ok (betaPosteriorVar prior trial ζ)
  else .error .nonpositiveLikelihood

theorem betaPosteriorVarGuarded_ok (prior : PrecisionPrior) {T : ℕ}
    (trial : Fin T → (S → O → ℝ) × (O → ℝ) × (S → ℝ)) (ζ : ℝ)
    (hz : 0 ≤ ζ) (hA : ∀ τ s o, 0 < (trial τ).1 s o) :
    betaPosteriorVarGuarded prior trial ζ = .ok (betaPosteriorVar prior trial ζ) := by
  simp [betaPosteriorVarGuarded, not_lt.mpr hz, hA]

/-- A bad cell in ANY trial refuses the whole family. -/
theorem betaPosteriorVarGuarded_nonpositive (prior : PrecisionPrior) {T : ℕ}
    (trial : Fin T → (S → O → ℝ) × (O → ℝ) × (S → ℝ)) (ζ : ℝ)
    (hz : 0 ≤ ζ) (τ : Fin T) (s : S) (o : O) (hcell : (trial τ).1 s o ≤ 0) :
    betaPosteriorVarGuarded prior trial ζ = .error .nonpositiveLikelihood := by
  have hbad : ¬ ∀ τ s o, 0 < (trial τ).1 s o := by
    intro h
    exact (not_lt_of_ge hcell) (h τ s o)
  simp [betaPosteriorVarGuarded, not_lt.mpr hz, hbad]

/-- Negative control: a positive first likelihood cannot hide the second trial's
zero cell, even with zero state mass. Both existing refusal arms are reachable. -/
theorem variableGuardRefusals (prior : PrecisionPrior) :
    let trials : Fin 2 → (Bool → Bool → ℝ) × (Bool → ℝ) × (Bool → ℝ) :=
      fun τ => ((fun _ _ => if τ = 0 then 1 else 0), fun _ => 0, fun _ => 0)
    betaPosteriorVarGuarded prior trials (-1) = .error (.negativeZeta (-1)) ∧
      betaPosteriorVarGuarded prior trials 1 = .error .nonpositiveLikelihood := by
  dsimp only
  constructor
  · norm_num [betaPosteriorVarGuarded]
  · apply betaPosteriorVarGuarded_nonpositive prior _ 1 (by norm_num) 1 true true
    norm_num

/-- The NEXT click tempers A_next, not a historical A_τ, at the learned mean.
The runtime binding is `lane-options` followed by `tempered-rates`. -/
noncomputable def nextLikelihoodVar (prior : PrecisionPrior) {T : ℕ}
    (trial : Fin T → (S → O → ℝ) × (O → ℝ) × (S → ℝ)) (ζ : ℝ)
    (A_next : S → O → ℝ) : S → O → ℝ :=
  precisionLikelihood (1 / betaPosteriorVar prior trial ζ) A_next

/-- Before any trial the next likelihood uses the prior's expected precision. -/
theorem nextLikelihoodVar_zeroSteps (prior : PrecisionPrior)
    (trial : Fin 0 → (S → O → ℝ) × (O → ℝ) × (S → ℝ)) (ζ : ℝ)
    (A_next : S → O → ℝ) :
    nextLikelihoodVar prior trial ζ A_next
      = precisionLikelihood (expectedPrecision prior) A_next := by
  simp [nextLikelihoodVar, betaPosteriorVar_nil, expectedPrecision]

#print axioms betaPosteriorVar
#print axioms betaPosteriorVar_const
#print axioms betaPosteriorVar_nil
#print axioms betaPosteriorVarGuarded
#print axioms betaPosteriorVarGuarded_ok
#print axioms betaPosteriorVarGuarded_nonpositive
#print axioms variableGuardRefusals
#print axioms nextLikelihoodVar
#print axioms nextLikelihoodVar_zeroSteps

end DarkTower.WarMachine.Proof2.LikelihoodPrecisionVariableA
