import DarkTower.WarMachine.PolicyPosterior

namespace DarkTower.WarMachine.PolicyPrecision

noncomputable section

variable {ι : Type*}

/-! ## Temperature and precision

The commitment temperature of variational policy selection, bound to the
variational law only: τ = β with β > 0 and precision γ = 1/τ
(Friston et al. 2017 eq. (2.1) P(π) = σ(−γ G(π)), `refs/friston2017.txt:329–339`,
with γ = 1/β stated after eq. (2.7), `:683–684`; Da Costa et al. 2020 A.2,
`refs/dacosta2020.txt:1262–1271`). The spread and selection-gain engineering
modes are not this quantity. -/

/-- Commitment temperature as the inverse precision of policy selection:
`τ = β` with `β > 0`. -/
structure PolicyTemperature where
  beta : ℝ
  beta_pos : 0 < beta

/-- Policy precision `γ = 1/τ = 1/β` (Friston 2017, after eq. (2.7)). -/
def policyPrecision (t : PolicyTemperature) : ℝ := 1 / t.beta

/-- The policy precision is strictly positive. -/
theorem policyPrecision_pos (t : PolicyTemperature) : 0 < policyPrecision t :=
  one_div_pos.2 t.beta_pos

/-- Precision and temperature are mutual inverses: `γ * β = 1`. -/
theorem policyPrecision_mul_beta (t : PolicyTemperature) :
    policyPrecision t * t.beta = 1 :=
  one_div_mul_cancel (ne_of_gt t.beta_pos)

/-! ## The precision-weighted policy posterior -/

variable [Fintype ι] [Nonempty ι]

/-- Precision-weighted policy posterior over a finite policy space:
`σ(ln E − F − γ G)` (Parr 2022 eq. B.9; Da Costa 2020 A.2). -/
def precisionWeightedPosterior (t : PolicyTemperature) (habit : ι → ℝ)
    (G F : ι → ℝ) (hhabit : ∀ π, 0 < habit π) : ι → ℝ :=
  fun π => Real.exp (Real.log (habit π) - F π - policyPrecision t * G π) /
    ∑ π', Real.exp (Real.log (habit π') - F π' - policyPrecision t * G π')

theorem precisionWeighted_total_pos (t : PolicyTemperature) (habit : ι → ℝ)
    (G F : ι → ℝ) (hhabit : ∀ π, 0 < habit π) :
    0 < ∑ π', Real.exp (Real.log (habit π') - F π' - policyPrecision t * G π') :=
  Finset.sum_pos' (fun b _ => (Real.exp_pos _).le)
    (Exists.intro ‹Nonempty ι›.some ⟨Finset.mem_univ _, Real.exp_pos _⟩)

/-- Every posterior mass is nonnegative. -/
theorem precisionWeightedPosterior_nonneg (t : PolicyTemperature) (habit : ι → ℝ)
    (G F : ι → ℝ) (hhabit : ∀ π, 0 < habit π) (π : ι) :
    0 ≤ precisionWeightedPosterior t habit G F hhabit π :=
  div_nonneg (Real.exp_pos _).le
    (precisionWeighted_total_pos t habit G F hhabit).le

/-- The posterior masses sum to one. -/
theorem precisionWeightedPosterior_sum_eq_one (t : PolicyTemperature) (habit : ι → ℝ)
    (G F : ι → ℝ) (hhabit : ∀ π, 0 < habit π) :
    ∑ π, precisionWeightedPosterior t habit G F hhabit π = 1 := by
  have hpos := precisionWeighted_total_pos t habit G F hhabit
  have hS : (∑ π', Real.exp (Real.log (habit π') - F π' - policyPrecision t * G π')) ≠ 0 :=
    ne_of_gt hpos
  simp only [precisionWeightedPosterior, div_eq_inv_mul]
  rw [← Finset.mul_sum, inv_mul_cancel₀ hS]

/-- With `G π₁ < G π₂`, equal habit and `F`, the posterior ratio is
`exp (γ (G π₂ − G π₁)) > 1`: larger γ (smaller β) concentrates posterior mass
on the lower-`G` policy. -/
theorem higherPrecisionSharpens (t : PolicyTemperature) (habit : ι → ℝ)
    (G F : ι → ℝ) (hhabit : ∀ π, 0 < habit π) (π₁ π₂ : ι)
    (hh : habit π₁ = habit π₂) (hF : F π₁ = F π₂) (hG : G π₁ < G π₂) :
    precisionWeightedPosterior t habit G F hhabit π₁
      / precisionWeightedPosterior t habit G F hhabit π₂
      = Real.exp (policyPrecision t * (G π₂ - G π₁)) := by
  have hpos := precisionWeighted_total_pos t habit G F hhabit
  have hS : (∑ π', Real.exp (Real.log (habit π') - F π' - policyPrecision t * G π')) ≠ 0 :=
    ne_of_gt hpos
  simp only [precisionWeightedPosterior]
  have key : ∀ a b c : ℝ, c ≠ 0 → (a / c) / (b / c) = a / b := by
    intro a b c _
    field_simp
  rw [key _ _ _ hS, ← Real.exp_sub, hh, hF]
  congr 1
  ring

/-! ## Agreement with the closed `:policy-posterior` row -/

/-- A duplicate-free list enumeration of a `Fintype` sums any function like the
whole type does. -/
theorem sum_map_enum (f : ι → ℝ) (l : List ι)
    (hnodup : l.Nodup) (hcover : ∀ i, i ∈ l) : (l.map f).sum = ∑ i, f i := by
  classical
  have key : ∀ (l : List ι), l.Nodup → (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
    intro l
    induction l with
    | nil => simp
    | cons a as ih =>
      intro h
      obtain ⟨ha, has⟩ := List.nodup_cons.mp h
      have hna : a ∉ as.toFinset := fun hm => ha (List.mem_toFinset.mp hm)
      rw [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert hna, ih has]
  have hu : l.toFinset = Finset.univ :=
    Finset.ext fun x => ⟨fun _ => Finset.mem_univ x,
      fun _ => List.mem_toFinset.mpr (hcover x)⟩
  rw [key l hnodup, hu]

omit [Fintype ι] in
/-- A list enumeration of a nonempty type is nonempty. -/
theorem enum_ne_nil (l : List ι) (hcover : ∀ i, i ∈ l) : l ≠ [] := by
  intro h
  rw [h] at hcover
  exact absurd (hcover ‹Nonempty ι›.some) (by simp)

/-- The closed policy posterior (`PolicyPosterior.softmaxWithFPi`) at
`tau = t.beta` equals the precision-weighted posterior over any
duplicate-free exhaustive enumeration: the closed row's `tau` *is* β and its
`G / tau` term *is* `γ * G`. -/
theorem precisionWeightedPosterior_eq_softmaxWithFPi (t : PolicyTemperature)
    (habit : ι → ℝ) (grade : ι → DarkTower.WarMachine.Holes.ExpectedFreeEnergyValue)
    (fPi : ι → ℝ) (G F : ι → ℝ) (l : List ι)
    (hhabit : ∀ π, 0 < habit π)
    (hgrade : ∀ π, (grade π).value = G π) (hfPi : ∀ π, fPi π = F π)
    (hnodup : l.Nodup) (hcover : ∀ π, π ∈ l) :
    PolicyPosterior.softmaxWithFPi habit grade fPi t.beta l hhabit t.beta_pos
        (enum_ne_nil l hcover) hnodup
      = l.map (fun π => precisionWeightedPosterior t habit G F hhabit π) := by
  have hne := enum_ne_nil l hcover
  have hex : ∀ π : ι, Real.log (habit π) - (grade π).value / t.beta - fPi π
      = Real.log (habit π) - F π - policyPrecision t * G π := by
    intro π
    rw [hgrade π, hfPi π, div_eq_inv_mul, policyPrecision, one_div]
    ring
  simp only [PolicyPosterior.softmaxWithFPi, precisionWeightedPosterior]
  rw [List.map_map, PolicyPosterior.foldl_add_eq, zero_add]
  refine List.map_congr_left fun π _ => ?_
  simp only [Function.comp_apply]
  have hsum : (List.map
      (fun π => Real.exp (Real.log (habit π) - (grade π).value / t.beta - fPi π)) l).sum
      = ∑ π', Real.exp (Real.log (habit π') - F π' - policyPrecision t * G π') := by
    rw [sum_map_enum _ l hnodup hcover]
    exact Finset.sum_congr rfl fun i _ => by rw [hex i]
  rw [hex π, hsum]

/-! ## Fixture -/

/-- Fixture: β = 1/4 gives γ = 4. -/
def quarterTemperature : PolicyTemperature where
  beta := 1 / 4
  beta_pos := by norm_num

theorem quarterTemperature_gamma : policyPrecision quarterTemperature = 4 := by
  simp only [policyPrecision, quarterTemperature]
  norm_num

end

end DarkTower.WarMachine.PolicyPrecision
