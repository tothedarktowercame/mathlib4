import DarkTower.WarMachine.AIFJointObjectiveIdentity

/-!
# Information preserved by an injective finite report encoding

Da Costa et al. 2020 equations 14--16 (`refs/dacosta2020.txt:787-835`) and
Parr et al. 2022 equation 7.11 (`refs/parr2022.txt:7301-7325`) use information
gain in the expected-free-energy decomposition.  This module proves the
probability algebra needed when a finite observation is represented by a
deterministic report.

`reportKernel` post-composes an existing conditional observation kernel with a
supplied deterministic encoding.  If that encoding is injective, the existing
`CascadeEFE.information` is unchanged.  No positivity assumption is imposed:
zero-probability observations and report values outside the encoding's range
remain zero.  This is a representation theorem, not a new AIF axiom, runtime
decoder, provenance claim, preference choice, or R20 correspondence.
-/

namespace DarkTower.WarMachine.AIFReportEncoding

open scoped BigOperators
open DarkTower.WarMachine.Holes

noncomputable section

variable {Z O R : Type*} [Fintype Z] [Fintype O] [Fintype R] [DecidableEq R]

/-- The mass of a finite distribution after deterministic encoding. -/
def encodedMass (p : O → ℝ) (encode : O → R) (r : R) : ℝ :=
  ∑ o, p o * if r = encode o then 1 else 0

theorem encodedMass_apply (p : O → ℝ) (encode : O → R)
    (injective : Function.Injective encode) (o : O) :
    encodedMass p encode (encode o) = p o := by
  classical
  simp [encodedMass, injective.eq_iff]

theorem encodedMass_off_range (p : O → ℝ) (encode : O → R) (r : R)
    (outside : r ∉ Set.range encode) : encodedMass p encode r = 0 := by
  classical
  simp only [encodedMass]
  apply Finset.sum_eq_zero
  intro o _
  have h : r ≠ encode o := by
    intro hr
    exact outside ⟨o, hr.symm⟩
  simp [h]

theorem sum_encodedMass_term (p : O → ℝ) (encode : O → R)
    (injective : Function.Injective encode) (term : ℝ → ℝ)
    (term_zero : term 0 = 0) :
    ∑ r, term (encodedMass p encode r) = ∑ o, term (p o) := by
  classical
  calc
    ∑ r, term (encodedMass p encode r) =
        ∑ r ∈ Finset.univ.image encode, term (encodedMass p encode r) := by
      symm
      apply Finset.sum_subset (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _)
      intro r _ hr
      rw [encodedMass_off_range p encode r]
      · exact term_zero
      · simpa [Set.mem_range] using hr
    _ = ∑ o, term (p o) := by
      rw [Finset.sum_image (fun _ _ _ _ h => injective h)]
      apply Finset.sum_congr rfl
      intro o _
      rw [encodedMass_apply p encode injective o]

/-- Post-compose an observation kernel with a deterministic finite encoding. -/
def reportKernel (observe : ProbabilityKernel Z O) (encode : O → R) :
    ProbabilityKernel Z R :=
  CascadeEFE.finiteKernel (fun z r => encodedMass (observe.mass z) encode r)
    (by
      intro z r
      exact Finset.sum_nonneg fun o _ => mul_nonneg (observe.nonnegative z o) (by split_ifs <;> norm_num))
    (by
      intro z
      simp only [encodedMass]
      rw [Finset.sum_comm]
      simp [CascadeEFE.kernel_sum observe z])

theorem push_report_mass (prior : ProbabilityKernel Unit Z)
    (observe : ProbabilityKernel Z O) (encode : O → R) (r : R) :
    (CascadeEFE.push prior (reportKernel observe encode)).mass () r =
      encodedMass ((CascadeEFE.push prior observe).mass ()) encode r := by
  classical
  simp only [CascadeEFE.push, CascadeEFE.finiteKernel, reportKernel, encodedMass]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  by_cases h : r = encode o
  · simp [h]
  · simp [h]

theorem entropy_encoded (p : O → ℝ) (encode : O → R)
    (injective : Function.Injective encode) :
    CascadeEFE.entropy (encodedMass p encode) = CascadeEFE.entropy p := by
  unfold CascadeEFE.entropy
  rw [sum_encodedMass_term p encode injective
    (fun x => if x = 0 then 0 else x * Real.log x) (by simp)]

theorem ambiguity_report (prior : ProbabilityKernel Unit Z)
    (observe : ProbabilityKernel Z O) (encode : O → R)
    (injective : Function.Injective encode) :
    CascadeEFE.ambiguity prior (reportKernel observe encode) =
      CascadeEFE.ambiguity prior observe := by
  unfold CascadeEFE.ambiguity
  apply Finset.sum_congr rfl
  intro z _
  rw [show (reportKernel observe encode).mass z = encodedMass (observe.mass z) encode by rfl,
    entropy_encoded _ _ injective]

/-- A deterministic injective report encoding preserves the existing finite
joint information exactly. Extra report values outside its range are harmless
because `reportKernel` assigns them zero mass. -/
theorem information_report_encoding (prior : ProbabilityKernel Unit Z)
    (observe : ProbabilityKernel Z O) (encode : O → R)
    (injective : Function.Injective encode) :
    CascadeEFE.information prior (reportKernel observe encode) =
      CascadeEFE.information prior observe := by
  rw [CascadeEFE.information_entropy_identity,
    CascadeEFE.information_entropy_identity]
  rw [show (CascadeEFE.push prior (reportKernel observe encode)).mass () =
      encodedMass ((CascadeEFE.push prior observe).mass ()) encode by
        funext r; exact push_report_mass prior observe encode r,
    entropy_encoded _ _ injective, ambiguity_report prior observe encode injective]

/-! ## Synthetic controls -/

def uniformBool : ProbabilityKernel Unit Bool :=
  CascadeEFE.finiteKernel (fun _ _ => 1 / 2)
    (by intros; norm_num) (by intro; norm_num [Fintype.sum_bool])

def revealBool : ProbabilityKernel Bool Bool :=
  CascadeEFE.finiteKernel (fun z o => if o = z then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro z; cases z <;> simp)

theorem relabel_preserves :
    CascadeEFE.information uniformBool (reportKernel revealBool not) =
      CascadeEFE.information uniformBool revealBool := by
  apply information_report_encoding
  intro a b h
  simpa using congrArg not h

theorem constant_report_loses_information :
    CascadeEFE.information uniformBool (reportKernel revealBool (fun _ => Unit.unit)) = 0 ∧
      0 < CascadeEFE.information uniformBool revealBool := by
  constructor
  · classical
    simp [CascadeEFE.information, CascadeEFE.joint, CascadeEFE.push,
      CascadeEFE.finiteKernel, reportKernel, encodedMass, uniformBool, revealBool,
      Fintype.sum_bool]
  · have h : CascadeEFE.information uniformBool revealBool = Real.log 2 := by
      classical
      simp [CascadeEFE.information, CascadeEFE.joint, CascadeEFE.push,
        CascadeEFE.finiteKernel, uniformBool, revealBool,
        show (Finset.univ : Finset (Bool × Bool)) =
          {(false, false), (false, true), (true, false), (true, true)} by decide]
      ring
    rw [h]
    exact Real.log_pos (by norm_num)

/-- An augmented observation may contain the old report and strictly more
latent information. Here the old report reveals the first independent bit;
the augmented report reveals both bits. This is not an encoding of the old
report alone. -/
def uniformPair : ProbabilityKernel Unit (Bool × Bool) :=
  CascadeEFE.finiteKernel (fun _ _ => 1 / 4)
    (by intros; norm_num)
    (by intro; norm_num [Fintype.sum_prod_type, Fintype.sum_bool])

def firstReport : ProbabilityKernel (Bool × Bool) Bool :=
  CascadeEFE.finiteKernel (fun z o => if o = z.1 then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro z; cases z.1 <;> simp)

def fullReport : ProbabilityKernel (Bool × Bool) (Bool × Bool) :=
  CascadeEFE.finiteKernel (fun z o => if o = z then 1 else 0)
    (by intros; split_ifs <;> norm_num)
    (by intro z; simp)

theorem augmented_report_has_strictly_more_information :
    CascadeEFE.information uniformPair firstReport <
      CascadeEFE.information uniformPair fullReport := by
  have hfirst : CascadeEFE.information uniformPair firstReport = Real.log 2 := by
    classical
    simp [CascadeEFE.information, CascadeEFE.joint, CascadeEFE.push,
      CascadeEFE.finiteKernel, uniformPair, firstReport,
      Fintype.sum_prod_type, Fintype.sum_bool]
    ring
  have hfull : CascadeEFE.information uniformPair fullReport = Real.log 4 := by
    classical
    simp [CascadeEFE.information, CascadeEFE.joint, CascadeEFE.push,
      CascadeEFE.finiteKernel, uniformPair, fullReport,
      Fintype.sum_prod_type, Fintype.sum_bool]
    ring
  rw [hfirst, hfull, show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hp : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  linarith

#print axioms information_report_encoding
#print axioms relabel_preserves
#print axioms constant_report_loses_information
#print axioms augmented_report_has_strictly_more_information

end
end DarkTower.WarMachine.AIFReportEncoding
