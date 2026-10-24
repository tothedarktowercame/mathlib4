import DarkTower.WarMachine.PolicyExpectedFreeEnergy
import DarkTower.WarMachine.CascadeEFE

/-!
# Finite outcome-risk, ambiguity, and joint information identity

Da Costa et al. 2020 equation 13 (`refs/dacosta2020.txt:775-786`) states
expected free energy as hidden-state risk plus ambiguity, and equations 14–16
(`:787-835`) relate it to expected log evidence and information gain.  The
replacement of state risk by outcome risk in equation 15 is explicitly an
approximation requiring a small posterior-divergence term (`:809-822`).  Parr
et al. 2022 equation 7.11 (`refs/parr2022.txt:7301-7325`) writes outcome risk,
ambiguity, and information-gain terms.

The result below is exact finite probability algebra for the *outcome-risk
specialization*: a normalized latent prior, normalized conditional observation
kernel, and normalized strictly-positive outcome preference.  It does not
claim that outcome risk is universally identical to equation 13's state risk.

Information is the existing `CascadeEFE.information`: joint KL against the
product of latent and outcome marginals, with its zero-joint-mass branch.  It is
not defined as entropy minus ambiguity.  The theorem uses the existing
`PolicyExpectedFreeEnergy.predictedOutcome`, `finiteRisk`, and `ambiguity`, and
proves their adapter equalities to the normalized-kernel identity already
established by `CascadeEFE.step_decomposition`.

Zero latent and conditional masses remain permitted. Strict positivity is
required only of the bounded preference in this first result. The fixtures are
synthetic and establish no runtime, selection, prior-authenticity, or R20 claim.
-/

namespace DarkTower.WarMachine.AIFJointObjectiveIdentity

open scoped BigOperators
open DarkTower.WarMachine.Holes

noncomputable section

variable {Z O : Type*} [Fintype Z] [Fintype O]

abbrev outcomeOf (prior : ProbabilityKernel Unit Z)
    (observe : ProbabilityKernel Z O) : O → ℝ :=
  PolicyExpectedFreeEnergy.predictedOutcome
    (fun o z => observe.mass z o) (prior.mass ())

/-- Expected negative log preference, using the existing pragmatic-cost
functional. -/
abbrev expectedNegativeLogPreference (prior : ProbabilityKernel Unit Z)
    (observe : ProbabilityKernel Z O) (preference : ProbabilityKernel Unit O) : ℝ :=
  CascadeEFE.pragmaticCost (CascadeEFE.push prior observe) preference

/-- Mutual information of the induced normalized joint: the existing joint KL
of `prior(z) * observe(o|z)` against `prior(z) * outcome(o)`. -/
abbrev jointInformation (prior : ProbabilityKernel Unit Z)
    (observe : ProbabilityKernel Z O) : ℝ :=
  CascadeEFE.information prior observe

theorem outcomeOf_eq_push (prior : ProbabilityKernel Unit Z)
    (observe : ProbabilityKernel Z O) :
    outcomeOf prior observe = (CascadeEFE.push prior observe).mass () := by
  funext o
  simp only [outcomeOf, PolicyExpectedFreeEnergy.predictedOutcome,
    CascadeEFE.push, CascadeEFE.finiteKernel]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem ambiguity_eq (prior : ProbabilityKernel Unit Z)
    (observe : ProbabilityKernel Z O) :
    PolicyExpectedFreeEnergy.ambiguity (fun o z => observe.mass z o) (prior.mass ()) =
      CascadeEFE.ambiguity prior observe := by
  simp [PolicyExpectedFreeEnergy.ambiguity, PolicyExpectedFreeEnergy.columnEntropy,
    CascadeEFE.ambiguity, CascadeEFE.entropy_eq]

theorem finiteRisk_eq (prior : ProbabilityKernel Unit Z)
    (observe : ProbabilityKernel Z O) (preference : ProbabilityKernel Unit O)
    (positive : ∀ o, 0 < preference.mass () o) :
    PolicyExpectedFreeEnergy.finiteRisk (outcomeOf prior observe) (preference.mass ()) =
      CascadeEFE.risk (CascadeEFE.push prior observe) preference
        (fun _ o _ _ => positive o) := by
  rw [outcomeOf_eq_push]
  unfold PolicyExpectedFreeEnergy.finiteRisk CascadeEFE.risk
  apply Finset.sum_congr rfl
  intro o _
  have nonneg := (CascadeEFE.push prior observe).nonnegative () o
  by_cases hz : (CascadeEFE.push prior observe).mass () o = 0
  · simp [hz, CascadeEFE.klTerm]
  · have hp : 0 < (CascadeEFE.push prior observe).mass () o := lt_of_le_of_ne nonneg (Ne.symm hz)
    simp [hp, hz, CascadeEFE.klTerm, Real.log_div hz (ne_of_gt (positive o)), mul_sub]

/-- Exact outcome-risk specialization: outcome risk plus conditional ambiguity
is expected negative log preference minus joint mutual information. -/
theorem outcomeRisk_add_ambiguity_eq
    (prior : ProbabilityKernel Unit Z)
    (observe : ProbabilityKernel Z O)
    (preference : ProbabilityKernel Unit O)
    (positive : ∀ o, 0 < preference.mass () o) :
    PolicyExpectedFreeEnergy.finiteRisk (outcomeOf prior observe) (preference.mass ()) +
        PolicyExpectedFreeEnergy.ambiguity (fun o z => observe.mass z o) (prior.mass ()) =
      expectedNegativeLogPreference prior observe preference -
        jointInformation prior observe := by
  let admissible : PreferenceRiskSeparation.riskAdmissible
      (CascadeEFE.push prior observe) preference := fun _ o _ _ => positive o
  have decomposition := CascadeEFE.step_decomposition prior observe preference admissible
  rw [CascadeEFE.stepG] at decomposition
  rw [finiteRisk_eq prior observe preference positive, ambiguity_eq]
  exact decomposition

/-! ## Synthetic controls -/

def uniformBool : ProbabilityKernel Unit Bool :=
  CascadeEFE.finiteKernel (fun _ _ => 1 / 2)
    (by intros; norm_num) (by intro; norm_num [Fintype.sum_bool])

def independentObserve : ProbabilityKernel Bool Bool :=
  CascadeEFE.finiteKernel (fun _ _ => 1 / 2)
    (by intros; norm_num) (by intro; norm_num [Fintype.sum_bool])

def informativeObserve : ProbabilityKernel Bool Bool :=
  CascadeEFE.finiteKernel (fun z o => if o = z then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro z; cases z <;> simp)

theorem independent_information_zero :
    jointInformation uniformBool independentObserve = 0 := by
  norm_num [jointInformation, CascadeEFE.information, CascadeEFE.joint,
    CascadeEFE.push, CascadeEFE.finiteKernel, uniformBool, independentObserve,
    Fintype.sum_bool]

theorem informative_information_eq_log_two :
    jointInformation uniformBool informativeObserve = Real.log 2 := by
  classical
  simp [jointInformation, CascadeEFE.information, CascadeEFE.joint,
    CascadeEFE.push, CascadeEFE.finiteKernel, uniformBool, informativeObserve,
    show (Finset.univ : Finset (Bool × Bool)) =
      {(false, false), (false, true), (true, false), (true, true)} by decide]
  ring

theorem informative_information_pos :
    0 < jointInformation uniformBool informativeObserve := by
  rw [informative_information_eq_log_two]
  exact Real.log_pos (by norm_num)

theorem informative_omitting_information_is_false :
    PolicyExpectedFreeEnergy.finiteRisk
          (outcomeOf uniformBool informativeObserve) (uniformBool.mass ()) +
        PolicyExpectedFreeEnergy.ambiguity
          (fun o z => informativeObserve.mass z o) (uniformBool.mass ()) ≠
      expectedNegativeLogPreference uniformBool informativeObserve uniformBool := by
  rw [outcomeRisk_add_ambiguity_eq uniformBool informativeObserve uniformBool
    (by intro; norm_num [uniformBool, CascadeEFE.finiteKernel])]
  intro h
  have : jointInformation uniformBool informativeObserve = 0 := by linarith
  exact (ne_of_gt informative_information_pos) this

#print axioms outcomeRisk_add_ambiguity_eq
#print axioms independent_information_zero
#print axioms informative_information_eq_log_two
#print axioms informative_omitting_information_is_false

end
end DarkTower.WarMachine.AIFJointObjectiveIdentity
