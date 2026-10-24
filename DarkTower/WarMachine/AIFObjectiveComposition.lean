import DarkTower.WarMachine.AIFNeutralDetail
import DarkTower.WarMachine.AIFReportEncoding

/-!
# Composition of the finite supplied-kernel AIF objective

Da Costa et al. 2020 equations 14--16 (`refs/dacosta2020.txt:787-835`) and
Parr et al. 2022 equation 7.11 (`refs/parr2022.txt:7301-7325`) relate outcome
risk, ambiguity, preference cost, and information gain.  As documented by
`AIFJointObjectiveIdentity`, Da Costa equation 15's replacement of state risk
by outcome risk is an explicit approximation; the algebra below is exact for
the finite *outcome-risk* specialization.

Given a raw finite report `X`, supplied maps `g : X → Y` and `w : X → W`, and
an injective paired encoding `x ↦ (g x, w x)`, this module composes three
existing results:

* `AIFJointObjectiveIdentity.outcomeRisk_add_ambiguity_eq`;
* `AIFNeutralDetail.neutral_detail_cost` for the proposed product preference
  `C × uniform(W)`;
* `AIFReportEncoding.information_report_encoding`.

No preference values are selected here. Product preference is a conditional
domain proposal, not a literature mandate. Kernels are supplied, zeros and
unreachable encoded pairs are allowed, and this establishes no runtime,
closure-model, R20, provenance, or full-AIF-compliance claim.
-/

namespace DarkTower.WarMachine.AIFObjectiveComposition

open DarkTower.WarMachine.Holes

noncomputable section

variable {Z X Y W : Type*}
  [Fintype Z] [Fintype X] [Fintype Y] [Fintype W]
  [DecidableEq Y] [DecidableEq W] [Nonempty W]

abbrev pairEncoding (g : X → Y) (w : X → W) : X → Y × W := fun x => (g x, w x)

abbrev encodedObservation (observe : ProbabilityKernel Z X)
    (g : X → Y) (w : X → W) : ProbabilityKernel Z (Y × W) :=
  AIFReportEncoding.reportKernel observe (pairEncoding g w)

abbrev scoredObservation (observe : ProbabilityKernel Z X)
    (g : X → Y) : ProbabilityKernel Z Y :=
  AIFReportEncoding.reportKernel observe g

/-- Marginalizing the paired encoded prediction over detail gives exactly the
prediction obtained by applying the supplied scored-outcome map `g`. -/
theorem marginal_encoded_eq_scored
    (prior : ProbabilityKernel Unit Z) (observe : ProbabilityKernel Z X)
    (g : X → Y) (w : X → W) (y : Y) :
    (AIFNeutralDetail.marginalY
        (CascadeEFE.push prior (encodedObservation observe g w))).mass () y =
      (CascadeEFE.push prior (scoredObservation observe g)).mass () y := by
  classical
  simp only [AIFNeutralDetail.marginalY, CascadeEFE.finiteKernel,
    CascadeEFE.push, encodedObservation, scoredObservation,
    AIFReportEncoding.reportKernel, AIFReportEncoding.encodedMass]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : y = g z
  · simp [h]
  · simp [h]

theorem marginal_encoded_cost
    (prior : ProbabilityKernel Unit Z) (observe : ProbabilityKernel Z X)
    (g : X → Y) (w : X → W) (C : ProbabilityKernel Unit Y) :
    CascadeEFE.pragmaticCost
        (AIFNeutralDetail.marginalY
          (CascadeEFE.push prior (encodedObservation observe g w))) C =
      CascadeEFE.pragmaticCost
        (CascadeEFE.push prior (scoredObservation observe g)) C := by
  unfold CascadeEFE.pragmaticCost
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro y _
  rw [marginal_encoded_eq_scored prior observe g w y]

/-- The composed finite objective theorem. The information term is the
existing information of the raw report, while preference cost is evaluated on
the scored `g`-marginal; fixed detail contributes `log |W|`. -/
theorem supplied_kernel_objective
    (prior : ProbabilityKernel Unit Z)
    (observe : ProbabilityKernel Z X)
    (g : X → Y) (w : X → W)
    (pair_injective : Function.Injective (pairEncoding g w))
    (C : ProbabilityKernel Unit Y) (positive : ∀ y, 0 < C.mass () y) :
    PolicyExpectedFreeEnergy.finiteRisk
          (AIFJointObjectiveIdentity.outcomeOf prior (encodedObservation observe g w))
          ((AIFNeutralDetail.productPreference C).mass ()) +
        PolicyExpectedFreeEnergy.ambiguity
          (fun yw z => (encodedObservation observe g w).mass z yw) (prior.mass ()) =
      CascadeEFE.pragmaticCost
          (CascadeEFE.push prior (scoredObservation observe g)) C -
        CascadeEFE.information prior observe + Real.log (Fintype.card W) := by
  rw [AIFJointObjectiveIdentity.outcomeRisk_add_ambiguity_eq
    prior (encodedObservation observe g w) (AIFNeutralDetail.productPreference C)
    (AIFNeutralDetail.productPreference_positive C positive)]
  change CascadeEFE.pragmaticCost
      (CascadeEFE.push prior (encodedObservation observe g w))
      (AIFNeutralDetail.productPreference C) -
      CascadeEFE.information prior (encodedObservation observe g w) = _
  rw [AIFNeutralDetail.neutral_detail_cost
    (CascadeEFE.push prior (encodedObservation observe g w)) C positive]
  rw [marginal_encoded_cost prior observe g w C]
  rw [AIFReportEncoding.information_report_encoding prior observe
    (pairEncoding g w) pair_injective]
  ring

/-- For the same detail type and preference, the common detail constant does
not affect pairwise order. Each candidate may supply its own raw kernel and
injective paired encoding. -/
theorem same_detail_candidate_order_iff
    (prior₁ prior₂ : ProbabilityKernel Unit Z)
    (observe₁ observe₂ : ProbabilityKernel Z X)
    (g₁ g₂ : X → Y) (w₁ w₂ : X → W)
    (h₁ : Function.Injective (pairEncoding g₁ w₁))
    (h₂ : Function.Injective (pairEncoding g₂ w₂))
    (C : ProbabilityKernel Unit Y) (positive : ∀ y, 0 < C.mass () y) :
    (PolicyExpectedFreeEnergy.finiteRisk
            (AIFJointObjectiveIdentity.outcomeOf prior₁ (encodedObservation observe₁ g₁ w₁))
            ((AIFNeutralDetail.productPreference C).mass ()) +
          PolicyExpectedFreeEnergy.ambiguity
            (fun yw z => (encodedObservation observe₁ g₁ w₁).mass z yw) (prior₁.mass ())) ≤
        (PolicyExpectedFreeEnergy.finiteRisk
            (AIFJointObjectiveIdentity.outcomeOf prior₂ (encodedObservation observe₂ g₂ w₂))
            ((AIFNeutralDetail.productPreference C).mass ()) +
          PolicyExpectedFreeEnergy.ambiguity
            (fun yw z => (encodedObservation observe₂ g₂ w₂).mass z yw) (prior₂.mass ())) ↔
      CascadeEFE.pragmaticCost
            (CascadeEFE.push prior₁ (scoredObservation observe₁ g₁)) C -
          CascadeEFE.information prior₁ observe₁ ≤
        CascadeEFE.pragmaticCost
            (CascadeEFE.push prior₂ (scoredObservation observe₂ g₂)) C -
          CascadeEFE.information prior₂ observe₂ := by
  rw [supplied_kernel_objective prior₁ observe₁ g₁ w₁ h₁ C positive,
    supplied_kernel_objective prior₂ observe₂ g₂ w₂ h₂ C positive]
  constructor <;> intro h <;> linarith

/-! ## Synthetic scored-only-information counterexample -/

def uniformBool : ProbabilityKernel Unit Bool := AIFReportEncoding.uniformBool
def revealBool : ProbabilityKernel Bool Bool := AIFReportEncoding.revealBool
def constantScore : Bool → Unit := fun _ => ()
def detailIdentity : Bool → Bool := id

theorem constant_score_pair_injective :
    Function.Injective (pairEncoding constantScore detailIdentity) := by
  intro a b h
  exact congrArg Prod.snd h

theorem scored_only_information_zero :
    CascadeEFE.information uniformBool
      (scoredObservation revealBool constantScore) = 0 := by
  exact AIFReportEncoding.constant_report_loses_information.1

theorem raw_report_information_positive :
    0 < CascadeEFE.information uniformBool revealBool :=
  AIFReportEncoding.constant_report_loses_information.2

/-- Replacing full-report information by scored-only information changes the
objective in this synthetic case, although the scored outcome is constant.
This states an objective difference, not that any actual choice must differ. -/
theorem collapse_to_scored_information_changes_objective
    (cost : ℝ) :
    cost - CascadeEFE.information uniformBool revealBool ≠
      cost - CascadeEFE.information uniformBool
        (scoredObservation revealBool constantScore) := by
  rw [scored_only_information_zero]
  intro h
  have hz : CascadeEFE.information uniformBool revealBool = 0 := by linarith
  exact (ne_of_gt raw_report_information_positive) hz

#print axioms marginal_encoded_eq_scored
#print axioms supplied_kernel_objective
#print axioms same_detail_candidate_order_iff
#print axioms collapse_to_scored_information_changes_objective

end
end DarkTower.WarMachine.AIFObjectiveComposition
