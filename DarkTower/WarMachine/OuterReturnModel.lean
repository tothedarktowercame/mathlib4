import DarkTower.WarMachine.AIFObjectiveComposition

/-!
# A normalized finite outer-return model

Parr et al. 2022 equations 7.9--7.11
(`refs/parr2022.txt:7214-7236,7295-7345`) factor a generative model into
normalized conditional distributions and distinguish expected preference from
information gain. Da Costa et al. 2020 equation 15
(`refs/dacosta2020.txt:809-822`) marks the replacement of state risk by
outcome risk as an approximation. The results here are exact finite
conditional-kernel algebra; they make no new claim about that approximation.

An outer return has a verdict `v : V` and a result in a supplied finite domain
`Result v`. This dependent sigma type lets a declared qualifying verdict use
an active joint consumer-result domain while a nonqualifying verdict uses a
singleton not-applicable domain. The mathematics does not choose that domain,
the qualifying predicate, verdict meanings, probabilities, kinds, priors, or
truth authority. In particular, a proposed `exhausted` value is merely a
within-budget return label unless an external checked budget artifact warrants
it.

The conditional consumer result is one supplied *joint* kernel. It is not
constructed by multiplying consumer marginals. A finite latent parameter can
be integrated with the existing `CascadeEFE.push`; shared latent dependence
therefore survives marginalization. This module supplies normalized kernels
for later objective use, but chooses no preference and performs no learning or
checked-map update.
-/

namespace DarkTower.WarMachine.OuterReturnModel

open scoped BigOperators
open DarkTower.WarMachine.Holes

noncomputable section

variable {Theta V : Type*} {Result : V → Type*}
  [Fintype Theta] [Fintype V] [∀ v, Fintype (Result v)]

/-- The proposed active/not-applicable discipline, stated independently of
the probability algebra: every nonqualifying branch has exactly one result.
The model does not infer `qualifies` or manufacture the distinguished value. -/
def NonqualifyingSingleton (qualifies : V → Bool) (Result : V → Type*) : Prop :=
  ∀ v, qualifies v = false → ∃! r : Result v, True

def returnMass
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v))
    (theta : Theta) (v : V) (r : Result v) : ℝ :=
  verdict.mass theta v * (result v).mass theta r

/-- A conditional joint return. `result` may encode arbitrary dependence
among all consumer components at a verdict. -/
def conditionalReturn
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v)) :
    ProbabilityKernel Theta (Sigma Result) :=
  CascadeEFE.finiteKernel
    (fun theta out => returnMass verdict result theta out.1 out.2)
    (by
      intro theta out
      rcases out with ⟨v, r⟩
      exact mul_nonneg (verdict.nonnegative theta v) ((result v).nonnegative theta r))
    (by
      intro theta
      simp only [returnMass]
      rw [Fintype.sum_sigma'
        (fun v r => verdict.mass theta v * (result v).mass theta r)]
      simp_rw [← Finset.mul_sum, CascadeEFE.kernel_sum]
      simpa using CascadeEFE.kernel_sum verdict theta)

theorem conditionalReturn_normalised
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v)) (theta : Theta) :
    ∑ out, (conditionalReturn verdict result).mass theta out = 1 :=
  CascadeEFE.kernel_sum _ _

/-- Summing every result branch recovers the verdict mass. Thus positive mass
on a nonqualifying verdict is retained rather than filtered away. -/
theorem verdict_marginal
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v))
    (theta : Theta) (v : V) :
    ∑ r, (conditionalReturn verdict result).mass theta ⟨v, r⟩ =
      verdict.mass theta v := by
  simp [conditionalReturn, returnMass, CascadeEFE.finiteKernel, ← Finset.mul_sum,
    CascadeEFE.kernel_sum]

/-- Integrate a supplied finite latent parameter with the existing kernel
push. Dependence already represented in the joint `result` kernel is kept. -/
def predictiveReturn
    (prior : ProbabilityKernel Unit Theta)
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v)) :
    ProbabilityKernel Unit (Sigma Result) :=
  CascadeEFE.push prior (conditionalReturn verdict result)

theorem predictiveReturn_normalised
    (prior : ProbabilityKernel Unit Theta)
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v)) :
    ∑ out, (predictiveReturn prior verdict result).mass () out = 1 :=
  CascadeEFE.kernel_sum _ _

theorem predictive_verdict_marginal
    (prior : ProbabilityKernel Unit Theta)
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v)) (v : V) :
    ∑ r, (predictiveReturn prior verdict result).mass () ⟨v, r⟩ =
      ∑ theta, prior.mass () theta * verdict.mass theta v := by
  classical
  simp only [predictiveReturn, CascadeEFE.push, CascadeEFE.finiteKernel]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro theta _
  simp [conditionalReturn, returnMass, CascadeEFE.finiteKernel, ← Finset.mul_sum,
    CascadeEFE.kernel_sum]

/-- The unnormalized mass of the defective closed-only gate. It deliberately
is not a `ProbabilityKernel`: nonqualifying verdicts are discarded. -/
def closedOnlyMass (qualifies : V → Bool)
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v))
    (theta : Theta) (out : Sigma Result) : ℝ :=
  if qualifies out.1 then
    verdict.mass theta out.1 * (result out.1).mass theta out.2
  else 0

theorem closedOnly_total
    (qualifies : V → Bool)
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v)) (theta : Theta) :
    ∑ out, closedOnlyMass qualifies verdict result theta out =
      ∑ v, if qualifies v then verdict.mass theta v else 0 := by
  change (∑ (out : Sigma Result), if qualifies out.1 then
      verdict.mass theta out.1 * (result out.1).mass theta out.2 else 0) = _
  rw [Fintype.sum_sigma'
    (fun v r => if qualifies v then
      verdict.mass theta v * (result v).mass theta r else 0)]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : qualifies v
  · simp [closedOnlyMass, h, ← Finset.mul_sum, CascadeEFE.kernel_sum]
  · simp [closedOnlyMass, h]

theorem closedOnly_loses_positive_nonqualifying_mass
    (qualifies : V → Bool)
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v))
    (theta : Theta) (v₀ : V) (hnq : qualifies v₀ = false)
    (hpos : 0 < verdict.mass theta v₀) :
    ∑ out, closedOnlyMass qualifies verdict result theta out < 1 := by
  rw [closedOnly_total]
  have hfull := CascadeEFE.kernel_sum verdict theta
  have hlt : (∑ v, if qualifies v then verdict.mass theta v else 0) <
      ∑ v, verdict.mass theta v := by
    apply Finset.sum_lt_sum
    · intro v _
      split
      · exact le_rfl
      · exact verdict.nonnegative theta v
    · exact ⟨v₀, Finset.mem_univ _, by simp [hnq, hpos]⟩
  simpa [hfull] using hlt

/-! ## Synthetic controls -/

def uniformBool : ProbabilityKernel Unit Bool :=
  CascadeEFE.finiteKernel (fun _ _ => 1 / 2)
    (by intros; norm_num) (by intro; norm_num [Fintype.sum_bool])

def deterministicVerdict : ProbabilityKernel Bool Unit :=
  CascadeEFE.finiteKernel (fun _ _ => 1) (by intros; norm_num) (by intro; simp)

/-- Both consumer components report the same shared latent bit. -/
def sharedConsumers (_ : Unit) : ProbabilityKernel Bool (Bool × Bool) :=
  CascadeEFE.finiteKernel (fun theta out => if out = (theta, theta) then 1 else 0)
    (by intros; split_ifs <;> norm_num)
    (by intro theta; cases theta <;> simp)

theorem shared_latent_joint_diagonal :
    (predictiveReturn uniformBool deterministicVerdict sharedConsumers).mass ()
      ⟨(), (true, true)⟩ = 1 / 2 := by
  norm_num [predictiveReturn, conditionalReturn, CascadeEFE.push,
    returnMass, CascadeEFE.finiteKernel, uniformBool, deterministicVerdict,
    CascadeEFE.point, sharedConsumers, Fintype.sum_bool]

theorem shared_latent_marginals_do_not_multiply :
    (predictiveReturn uniformBool deterministicVerdict sharedConsumers).mass ()
      ⟨(), (true, true)⟩ ≠ (1 / 2 : ℝ) * (1 / 2 : ℝ) := by
  rw [shared_latent_joint_diagonal]
  norm_num

def fairVerdict : ProbabilityKernel Unit Bool := uniformBool
def singletonResult (_ : Bool) : ProbabilityKernel Unit Unit := CascadeEFE.point ()

theorem closed_gate_loses_half :
    ∑ out, closedOnlyMass id fairVerdict singletonResult () out = 1 / 2 := by
  rw [closedOnly_total]
  norm_num [fairVerdict, uniformBool, CascadeEFE.finiteKernel, Fintype.sum_bool]

theorem corrected_model_preserves_all_mass :
    ∑ out, (conditionalReturn fairVerdict singletonResult).mass () out = 1 :=
  conditionalReturn_normalised _ _ _

/-- An observed not-applicable value and an unreported return are distinct in
the minimal reporting wrapper. No missingness/admission rule is inferred. -/
theorem observed_na_ne_unreported :
    (some (Sigma.mk false ()) : Option (Sigma fun _ : Bool => Unit)) ≠ none := by
  simp

#print axioms conditionalReturn_normalised
#print axioms verdict_marginal
#print axioms predictive_verdict_marginal
#print axioms closedOnly_loses_positive_nonqualifying_mass
#print axioms shared_latent_marginals_do_not_multiply

end
end DarkTower.WarMachine.OuterReturnModel
