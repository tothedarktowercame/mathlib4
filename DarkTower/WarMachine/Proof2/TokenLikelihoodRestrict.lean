import DarkTower.WarMachine.TokenObservation

/-!
# A partial observation is scored over the checked tokens (C5)

`futon3c holes/labs/M-wm-wiring/F1b-D.md` §3 (claude-11). `tokenLikelihood r s o`
ranges over ALL of `V`, so a token `v ∉ o` reads as "not reported" — and for an
established token that is a MISS, scored `falseNeg v`, not "not checked". A
partial observation therefore cannot be put into `o` over the full universe: the
unchecked tokens would be scored as reported absent. `restrict_ne_fullUniverse`
below is that difference, exhibited.

The consistent encoding restricts the universe to the CHECKED tokens. The claim
F1b-D makes and this module proves is that the restriction is not an
approximation: because the kernel is a product of independent per-token factors,
each summing to one over `o`-membership, summing over every assignment of the
unchecked tokens gives exactly the kernel over the checked ones. The code already
works this way — `cascade-free-energy` takes `universe (set (keys rates))` and
intersects `obs` with it — so what was missing was the theorem, not the
behaviour.

`tokenLikelihood_colsum` is the whole-`V` column sum and
`MixtureJointSeparationWitness` has a per-token `marginalMiss`; neither says the
unobserved tokens marginalise out to the restricted kernel. That is
`tokenLikelihood_restrict`.

## Why a new module

`TokenObservation.lean` is WM-04's and the `Proof2/` siblings (C1, C2, W1, W2)
are each their own module. `tokenFac` there is `private`, but `tokenLikelihood`
is DEFINED by the inline product, so `fac` below is that same factor named
locally and `tokenLikelihood_eq_prod` ties the two; nothing in WM-04's file
needs to change.

## What this module does not claim

Nothing about which tokens a step checks, nor about `:unobserved` as a record of
what was marginalised (F1b-D §3's "qualified universe" half): that is a question
about the flight's observation entry, not about the kernel. And nothing about
`s`: `s` stays over the full universe here, and the theorem says the likelihood
reads it only on the checked tokens.
-/

namespace DarkTower.WarMachine.Proof2.TokenLikelihoodRestrict

open DarkTower.WarMachine.TokenObservation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One token's factor of the kernel: `TokenObservation.tokenLikelihood`'s
summand, named here because its own is `private`. -/
def fac (r : AdjudicationRates V) (s : Finset V) (v : V) (b : Bool) : ℝ :=
  if v ∈ s then (if b then 1 - r.falseNeg v else r.falseNeg v)
  else (if b then r.falsePos v else 1 - r.falsePos v)

theorem tokenLikelihood_eq_prod (r : AdjudicationRates V) (s o : Finset V) :
    tokenLikelihood r s o = ∏ v, fac r s v (decide (v ∈ o)) := by
  unfold tokenLikelihood fac
  exact Finset.prod_congr rfl fun v _ => by by_cases hv : v ∈ o <;> simp [hv]

omit [Fintype V] in
/-- **Each token's factor sums to one over reported/not-reported.** This is the
independence that makes the restriction exact rather than approximate. -/
theorem fac_sum (r : AdjudicationRates V) (s : Finset V) (v : V) :
    fac r s v true + fac r s v false = 1 := by
  unfold fac
  by_cases hv : v ∈ s <;> simp [hv]

/-- **The kernel over the checked tokens `C` only.** -/
def restrictedLikelihood (r : AdjudicationRates V) (s C o : Finset V) : ℝ :=
  ∏ v ∈ C, fac r s v (decide (v ∈ o))

omit [Fintype V] in
/-- Splitting a product over `D` at a subset `t`: reported on `t`, not reported
off it. -/
theorem prod_split (r : AdjudicationRates V) (s D t : Finset V) (ht : t ⊆ D) :
    ∏ v ∈ D, fac r s v (decide (v ∈ t))
      = (∏ v ∈ t, fac r s v true) * ∏ v ∈ D \ t, fac r s v false := by
  rw [← Finset.prod_sdiff ht, mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun v hv => by simp [hv]
  · exact Finset.prod_congr rfl fun v hv => by
      simp [(Finset.mem_sdiff.mp hv).2]

omit [Fintype V] in
/-- **Summing over every assignment of a token set gives one.** The
`Finset.prod_add` form of the per-token sum: this is what makes the unchecked
tokens marginalise out. -/
theorem sum_powerset_prod (r : AdjudicationRates V) (s D : Finset V) :
    ∑ u ∈ D.powerset, ∏ v ∈ D, fac r s v (decide (v ∈ u)) = 1 := by
  have key := Finset.prod_add (fun v => fac r s v true) (fun v => fac r s v false) D
  rw [Finset.prod_congr rfl fun v _ => fac_sum r s v, Finset.prod_const_one] at key
  rw [Finset.sum_congr rfl fun t ht =>
    prod_split r s D t (Finset.mem_powerset.mp ht)]
  exact key.symm

/-- **`tokenLikelihood_restrict`.** Summing the kernel over every assignment of
the UNCHECKED tokens gives the kernel over the CHECKED ones. `o` is the reported
subset of the checked tokens `C`, and `u` ranges over the unchecked tokens'
possible reports. -/
theorem tokenLikelihood_restrict (r : AdjudicationRates V) (s C o : Finset V)
    (ho : o ⊆ C) :
    ∑ u ∈ Cᶜ.powerset, tokenLikelihood r s (o ∪ u) = restrictedLikelihood r s C o := by
  have hsplit : ∀ u ∈ Cᶜ.powerset, tokenLikelihood r s (o ∪ u)
      = restrictedLikelihood r s C o * ∏ v ∈ Cᶜ, fac r s v (decide (v ∈ u)) := by
    intro u hu
    have hucompl : u ⊆ Cᶜ := Finset.mem_powerset.mp hu
    rw [tokenLikelihood_eq_prod, ← Finset.prod_mul_prod_compl C]
    congr 1
    · refine Finset.prod_congr rfl fun v hv => ?_
      have : (v ∈ o ∪ u) = (v ∈ o) := by
        have hvu : v ∉ u := fun h => (Finset.mem_compl.mp (hucompl h)) hv
        simp [hvu]
      simp [this]
    · refine Finset.prod_congr rfl fun v hv => ?_
      have hvo : v ∉ o := fun h => (Finset.mem_compl.mp hv) (ho h)
      simp [hvo]
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, sum_powerset_prod, mul_one]

/-- The fibre is exactly what was summed over: the `o'` whose checked part is
`o` are the `o ∪ u` for `u` a set of unchecked tokens. -/
theorem fibre_eq (C o : Finset V) (ho : o ⊆ C) :
    Finset.univ.filter (fun o' : Finset V => o' ∩ C = o)
      = Cᶜ.powerset.image (fun u => o ∪ u) := by
  ext o'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_powerset]
  constructor
  · intro h
    refine ⟨o' \ C, fun v hv => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2, ?_⟩
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    by_cases hv : v ∈ C
    · have hiff : v ∈ o ↔ v ∈ o' := by
        rw [← h]
        simp [Finset.mem_inter, hv]
      constructor
      · rintro (hvo | ⟨hvo', -⟩)
        · exact hiff.mp hvo
        · exact hvo'
      · intro hvo'
        exact Or.inl (hiff.mpr hvo')
    · constructor
      · rintro (hvo | ⟨hvo', -⟩)
        · exact absurd (ho hvo) hv
        · exact hvo'
      · intro hvo'
        exact Or.inr ⟨hvo', hv⟩
  · rintro ⟨u, hu, rfl⟩
    ext v
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hv | hv, hC⟩
      · exact hv
      · exact absurd hC (Finset.mem_compl.mp (hu hv))
    · intro hv
      exact ⟨Or.inl hv, ho hv⟩

/-- Restated over the fibre itself, which is the form F1b-D §3 states: the sum
over every `o' ⊆ V` whose checked part is `o`. -/
theorem tokenLikelihood_restrict_fibre (r : AdjudicationRates V) (s C o : Finset V)
    (ho : o ⊆ C) :
    ∑ o' ∈ Finset.univ.filter (fun o' : Finset V => o' ∩ C = o), tokenLikelihood r s o'
      = restrictedLikelihood r s C o := by
  rw [fibre_eq C o ho, Finset.sum_image, tokenLikelihood_restrict r s C o ho]
  intro u hu u' hu' heq
  have hu2 : u ⊆ Cᶜ := Finset.mem_powerset.mp hu
  have hu'2 : u' ⊆ Cᶜ := Finset.mem_powerset.mp hu'
  ext v
  by_cases hv : v ∈ C
  · constructor <;> intro h
    · exact absurd hv (Finset.mem_compl.mp (hu2 h))
    · exact absurd hv (Finset.mem_compl.mp (hu'2 h))
  · have hvo : v ∉ o := fun h => hv (ho h)
    have := congrArg (fun t => v ∈ t) heq
    simpa [Finset.mem_union, hvo] using this

/-! ## The restriction is not a rewording

An established token that was NOT CHECKED is scored as a miss by the whole-`V`
reading. Two tokens, both established; only token `0` is checked and it is
reported. With `falseNeg ≡ 1/2` the restricted kernel is `1/2` and the whole-`V`
kernel is `1/4` — the unchecked token `1` contributing its own `falseNeg`. -/

section Witness

/-- Half-miss, no false positives. -/
noncomputable def halfMiss : AdjudicationRates (Fin 2) where
  falseNeg := fun _ => 1/2
  falsePos := fun _ => 0
  falseNeg_mem := fun _ => by constructor <;> norm_num
  falsePos_mem := fun _ => by constructor <;> norm_num

/-- Both tokens established. -/
def bothEstablished : Finset (Fin 2) := {0, 1}

/-- Only token `0` was checked. -/
def checked : Finset (Fin 2) := {0}

/-- Token `0` was checked and reported. -/
def reported : Finset (Fin 2) := {0}

theorem reported_subset : reported ⊆ checked := by decide

/-- **`restrict_ne_fullUniverse`.** Putting a partial observation into `o` over
the full universe is NOT the restricted kernel: the unchecked established token
is scored as a miss. -/
theorem restrict_ne_fullUniverse :
    restrictedLikelihood halfMiss bothEstablished checked reported = 1/2 ∧
    tokenLikelihood halfMiss bothEstablished reported = 1/4 ∧
    tokenLikelihood halfMiss bothEstablished reported
      ≠ restrictedLikelihood halfMiss bothEstablished checked reported := by
  have hres : restrictedLikelihood halfMiss bothEstablished checked reported = 1/2 := by
    norm_num [restrictedLikelihood, checked, reported, bothEstablished, fac, halfMiss]
  have hfull : tokenLikelihood halfMiss bothEstablished reported = 1/4 := by
    rw [tokenLikelihood_eq_prod]
    norm_num [Fin.prod_univ_two, fac, halfMiss, bothEstablished, reported]
  exact ⟨hres, hfull, by rw [hres, hfull]; norm_num⟩

/-- And the sum over the unchecked token's two reports recovers it: `1/4 + 1/4`
is the `1/2` the restricted kernel gives. -/
theorem witnessMarginalises :
    ∑ u ∈ (checkedᶜ : Finset (Fin 2)).powerset,
        tokenLikelihood halfMiss bothEstablished (reported ∪ u) = 1/2 := by
  rw [tokenLikelihood_restrict halfMiss bothEstablished checked reported reported_subset]
  norm_num [restrictedLikelihood, checked, reported, bothEstablished, fac, halfMiss]

end Witness

#print axioms fac
#print axioms tokenLikelihood_eq_prod
#print axioms fac_sum
#print axioms restrictedLikelihood
#print axioms prod_split
#print axioms sum_powerset_prod
#print axioms tokenLikelihood_restrict
#print axioms fibre_eq
#print axioms tokenLikelihood_restrict_fibre
#print axioms halfMiss
#print axioms restrict_ne_fullUniverse
#print axioms witnessMarginalises

end DarkTower.WarMachine.Proof2.TokenLikelihoodRestrict
