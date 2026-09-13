import Mathlib
import DarkTower.WarMachine.MachineTemperature

/-!
# Proposed interoceptive prior-rate seam

This is a proposal, not an adopted machine law.  It examines scaling the mean
of the `Gamma(1, betaPrior)` policy-precision prior by a positive confidence
factor `m`.  Since the shape is one and `betaPrior` is the rate, the adjusted
rate is `betaPrior / m`.  This does not say that posterior gamma is multiplied
by `m`: the posterior remains the root of the full beta equation.
-/
namespace DarkTower.WarMachine.InteroceptivePolicyPrecisionProposal

/-- Rate adjustment which makes the prior mean `m` times its old mean. -/
noncomputable def adjustedPriorRate (betaPrior m : ℝ) : ℝ := betaPrior / m

/-- The original prior is recovered exactly when no interoceptive adjustment
is present (`m = 1`). -/
theorem noInteroceptionReduction (betaPrior : ℝ) :
    adjustedPriorRate betaPrior 1 = betaPrior := by
  simp [adjustedPriorRate]

/-- Positive prior rate and confidence produce a positive adjusted rate. -/
theorem adjustedPriorRatePositive {betaPrior m : ℝ}
    (hbeta : 0 < betaPrior) (hm : 0 < m) :
    0 < adjustedPriorRate betaPrior m := by
  exact div_pos hbeta hm

/-- For a `Gamma(1, rate)` prior, the adjusted mean is exactly `m` times the
old mean.  This is a prior statement only. -/
theorem adjustedPriorMean {betaPrior m : ℝ}
    (hbeta : betaPrior ≠ 0) (hm : m ≠ 0) :
    1 / adjustedPriorRate betaPrior m = m * (1 / betaPrior) := by
  field_simp [adjustedPriorRate, hbeta, hm]

/-- Abstract form of the production fixed point: posterior beta is adjusted
prior rate plus the policy evidence term `(pi - pi0) dot G`, whose dependence
on beta is hidden in `evidenceDelta`. -/
def PosteriorRoot (priorRate : ℝ) (evidenceDelta : ℝ → ℝ) (beta : ℝ) : Prop :=
  beta = priorRate + evidenceDelta beta

/-- The variational temperature remains beta and policy precision remains its
reciprocal. -/
noncomputable def appliedGamma (beta : ℝ) : ℝ := 1 / beta

theorem positiveReciprocity {beta : ℝ} (hbeta : 0 < beta) :
    0 < appliedGamma beta ∧ appliedGamma beta * beta = 1 := by
  constructor
  · exact one_div_pos.mpr hbeta
  · simp [appliedGamma, ne_of_gt hbeta]

/-- Even unique positive roots need not preserve the prior-mean ordering.  For
`delta(beta) = 2*beta - 3`, prior rates 1 and 2 have unique roots 2 and 1;
halving the prior mean therefore *increases* posterior gamma from 1/2 to 1.
No general posterior monotonicity follows from prior-rate scaling alone. -/
theorem priorMeanReductionDoesNotImplyPosteriorGammaReduction :
    let delta : ℝ → ℝ := fun beta => 2 * beta - 3
    PosteriorRoot 1 delta 2 ∧
    PosteriorRoot 2 delta 1 ∧
    appliedGamma 1 > appliedGamma 2 := by
  norm_num [PosteriorRoot, appliedGamma]

/-- Typed outcomes required of any future field-level checker. -/
inductive FieldVerdict
  | appliedReduction
  | restoration
  | refusedUnreadable
  | refusedTestTrip
  | refusedCrossRun
  | refusedNonpositiveInput
  | refusedMultipleRoots
  | heldUnsolved
  | heldAbsent
  | counterexampleNoReduction
  deriving DecidableEq, Repr

#print axioms noInteroceptionReduction
#print axioms adjustedPriorRatePositive
#print axioms adjustedPriorMean
#print axioms positiveReciprocity
#print axioms priorMeanReductionDoesNotImplyPosteriorGammaReduction

end DarkTower.WarMachine.InteroceptivePolicyPrecisionProposal
