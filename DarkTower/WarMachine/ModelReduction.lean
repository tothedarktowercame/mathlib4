import DarkTower.WarMachine.Holes

/-!
# Composite Bayesian model-reduction decision

The registry's model-reduction sentence has three parts.  This module binds
them in one carrier by reference to the frozen declarations in `Holes`; none of
their bodies is restated here.  Argument order is the specification order
`a, A, a'`, while the referenced functions retain their frozen signatures.
-/

namespace DarkTower.WarMachine.ModelReduction

open DarkTower.WarMachine.Holes

noncomputable section

/-- One complete reduction result: reduced posterior, evidence change, and the
threshold verdict.  The equation field prevents an independently supplied
positive concentration vector from drifting from componentwise BMR. -/
structure ModelReductionDecision where
  fullPrior : DirichletConcentrations
  fullPosterior : DirichletConcentrations
  reducedPrior : DirichletConcentrations
  reducedPosterior : DirichletConcentrations
  evidenceChange : ModelReductionFreeEnergyChange
  accepted : Prop
  reducedEquation : reducedPosterior.val =
    bayesianModelReduction fullPosterior.val reducedPrior.val fullPrior.val
  /- The cited equation (Friston 2018 Table 1) compares priors over the same
  coordinates; without this field `List.zip` in `bayesianModelReduction`
  would silently truncate mismatched vectors (audit A1 §3). -/
  sameLength : fullPosterior.val.length = fullPrior.val.length ∧
    reducedPrior.val.length = fullPrior.val.length ∧
    reducedPosterior.val.length = fullPrior.val.length

/-- Compose the three frozen declarations.  Positivity of the componentwise
posterior is supplied explicitly because `bayesianModelReduction` itself
returns a list and does not prove that side condition; the length hypothesis
keeps all four concentration vectors over the same coordinates. -/
def modelReductionDecision
    (a A aPrime APrime : DirichletConcentrations)
    (hAPrime : APrime.val = bayesianModelReduction A.val aPrime.val a.val)
    (hLen : A.val.length = a.val.length ∧
      aPrime.val.length = a.val.length ∧ APrime.val.length = a.val.length) :
    ModelReductionDecision where
  fullPrior := a
  fullPosterior := A
  reducedPrior := aPrime
  reducedPosterior := APrime
  evidenceChange := modelReductionFreeEnergyChange A aPrime a APrime
  accepted := bayesFactorThreshold (modelReductionFreeEnergyChange A aPrime a APrime)
  reducedEquation := hAPrime
  sameLength := hLen

/-- No truncation happens for any decision that can be built: the composite
BMR output has exactly the common length carried by the decision. -/
theorem bayesianModelReduction_length_of_decision
    (d : ModelReductionDecision) :
    (bayesianModelReduction d.fullPosterior.val d.reducedPrior.val
        d.fullPrior.val).length = d.fullPrior.val.length := by
  obtain ⟨h1, h2, h3⟩ := d.sameLength
  simp only [bayesianModelReduction, List.length_map, List.length_zip]
  omega

/-- Audit A1 §3 counterexample: with `a = [1,1]` and `aPrime = [1]` the
same-length condition fails, so no `ModelReductionDecision` can be built
from the audit's vectors. -/
theorem auditCounterexample_lengthFails :
    ¬ ((⟨[1], by simp, by simp⟩ : DirichletConcentrations).val.length =
       (⟨[1, 1], by simp, by simp⟩ : DirichletConcentrations).val.length) := by
  decide

/-- Projection 1: the composite posterior is exactly the frozen componentwise
`bayesianModelReduction` output. -/
theorem reducedPosterior_projection
    (a A aPrime APrime : DirichletConcentrations)
    (h : APrime.val = bayesianModelReduction A.val aPrime.val a.val)
    (hLen : A.val.length = a.val.length ∧
      aPrime.val.length = a.val.length ∧ APrime.val.length = a.val.length) :
    (modelReductionDecision a A aPrime APrime h hLen).reducedPosterior.val =
      bayesianModelReduction A.val aPrime.val a.val := by
  exact h

/-- Projection 2: the composite evidence is exactly the frozen Dirichlet
normalizer change. -/
theorem evidenceChange_projection
    (a A aPrime APrime : DirichletConcentrations)
    (h : APrime.val = bayesianModelReduction A.val aPrime.val a.val)
    (hLen : A.val.length = a.val.length ∧
      aPrime.val.length = a.val.length ∧ APrime.val.length = a.val.length) :
    (modelReductionDecision a A aPrime APrime h hLen).evidenceChange =
      modelReductionFreeEnergyChange A aPrime a APrime := by
  rfl

/-- Projection 3: acceptance is exactly the frozen Bayes-factor threshold at
the composite's evidence change. -/
theorem acceptance_projection
    (a A aPrime APrime : DirichletConcentrations)
    (h : APrime.val = bayesianModelReduction A.val aPrime.val a.val)
    (hLen : A.val.length = a.val.length ∧
      aPrime.val.length = a.val.length ∧ APrime.val.length = a.val.length) :
    (modelReductionDecision a A aPrime APrime h hLen).accepted ↔
      bayesFactorThreshold
        (modelReductionDecision a A aPrime APrime h hLen).evidenceChange := by
  rfl

/-- Positive one-coordinate concentrations used by the V7-R17 identity
fixture (`00-r17.edn`, expected ΔF 0 and rejection). -/
def identityConcentrations : DirichletConcentrations :=
  ⟨[1], by simp, by simp⟩

theorem identityReductionEquation :
    identityConcentrations.val =
      bayesianModelReduction identityConcentrations.val
        identityConcentrations.val identityConcentrations.val := by
  norm_num [identityConcentrations, bayesianModelReduction]

def identityDecision : ModelReductionDecision :=
  modelReductionDecision identityConcentrations identityConcentrations
    identityConcentrations identityConcentrations identityReductionEquation
    ⟨rfl, rfl, rfl⟩

/-- The V7-R17 identity fixture computes through all three referenced laws:
the posterior remains `[1]`, ΔF is zero, and zero does not pass `ΔF ≤ -3`. -/
theorem identityFixture_endToEnd :
    identityDecision.reducedPosterior.val = [1] ∧
    identityDecision.evidenceChange.value = 0 ∧
    ¬ identityDecision.accepted := by
  simp [identityDecision, modelReductionDecision, identityConcentrations,
    modelReductionFreeEnergyChange, logMultivariateBeta,
    bayesFactorThreshold]

/-- A direct rejection instance: any declared evidence change above `-3`
fails the frozen threshold proposition. -/
theorem evidenceAboveThreshold_rejects :
    ¬ bayesFactorThreshold ⟨0⟩ := by
  norm_num [bayesFactorThreshold]

#print axioms bayesianModelReduction_length_of_decision
#print axioms auditCounterexample_lengthFails
#print axioms reducedPosterior_projection
#print axioms evidenceChange_projection
#print axioms acceptance_projection
#print axioms identityFixture_endToEnd
#print axioms evidenceAboveThreshold_rejects

end


end DarkTower.WarMachine.ModelReduction
