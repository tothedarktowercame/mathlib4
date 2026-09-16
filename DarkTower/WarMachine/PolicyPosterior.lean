import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.PolicyPosterior

noncomputable section

/-- CARRIER · owner: sec-glossary.tex:35 · P-glossary-mathematics · holder: by-rule ·
evidence: Row 16 R6 production-trace witness · falsifier: the declared `F_π` term is
omitted, or the zero-`F_π` branch diverges from `softmax` · The full policy posterior is
Q(π) ∝ exp(ln E(π) − G(π)/τ − F_π(π)). The carrier uses `Real.exp` and `Real.log`
directly; the hypotheses the cited equation (Parr 2022 B.9) needs are part of the
constructor: strictly positive habit mass, strictly positive temperature, and a
nonempty duplicate-free policy list, so every output list is a probability
distribution (see `softmaxWithFPi_nonneg`, `softmaxWithFPi_sum_eq_one`). -/
def softmaxWithFPi {PolicyIndex : Type*} (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → DarkTower.WarMachine.Holes.ExpectedFreeEnergyValue)
    (fPi : PolicyIndex → ℝ) (tau : ℝ) (policies : List PolicyIndex)
    (hhabit : ∀ π, 0 < habit π) (htau : 0 < tau)
    (hne : policies ≠ []) (hnodup : policies.Nodup) : List ℝ :=
  let weights := policies.map fun π =>
    Real.exp (Real.log (habit π) - (grade π).value / tau - fPi π)
  let total := weights.foldl (· + ·) 0
  weights.map fun weight => weight / total

/-- Folding addition over a list of strictly positive reals from a strictly
positive start keeps the accumulator strictly positive. -/
theorem foldl_add_pos_of_pos {b : ℝ} (hb : 0 < b) {l : List ℝ}
    (hl : ∀ x ∈ l, 0 < x) : 0 < l.foldl (· + ·) b := by
  induction l generalizing b with
  | nil => exact hb
  | cons a as ih =>
    exact ih (add_pos hb (hl a (by simp))) (fun x hx => hl x (by simp [hx]))

/-- Folding addition over a list of reals from `b` accumulates `b +` the sum. -/
theorem foldl_add_eq {b : ℝ} {l : List ℝ} : l.foldl (· + ·) b = b + l.sum := by
  induction l generalizing b with
  | nil => exact (add_zero b).symm
  | cons a as ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [ih]
    ring

/-- Dividing every entry of a list by the same real divides the sum. -/
theorem sum_map_div (c : ℝ) {l : List ℝ} : (l.map fun x => x / c).sum = l.sum / c := by
  induction l with
  | nil => simp
  | cons a as ih => simp [ih, add_div]

/-- The normalizer of the full carrier is strictly positive: it is a fold of
strictly positive exponentials over a nonempty policy list. -/
theorem softmaxWithFPi_total_pos {PolicyIndex : Type*} (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → DarkTower.WarMachine.Holes.ExpectedFreeEnergyValue)
    (fPi : PolicyIndex → ℝ) (tau : ℝ) (policies : List PolicyIndex)
    (hne : policies ≠ []) :
    0 < (policies.map fun π =>
      Real.exp (Real.log (habit π) - (grade π).value / tau - fPi π)).foldl (· + ·) 0 := by
  cases policies with
  | nil => exact absurd rfl hne
  | cons a as =>
    simp only [List.map_cons, List.foldl_cons]
    refine foldl_add_pos_of_pos (by positivity) ?_
    intro x hx
    obtain ⟨π, _, hπ⟩ := List.mem_map.mp hx
    subst hπ
    exact Real.exp_pos _

/-- Every output weight of the full policy posterior is nonnegative. -/
theorem softmaxWithFPi_nonneg {PolicyIndex : Type*} (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → DarkTower.WarMachine.Holes.ExpectedFreeEnergyValue)
    (fPi : PolicyIndex → ℝ) (tau : ℝ) (policies : List PolicyIndex)
    (hhabit : ∀ π, 0 < habit π) (htau : 0 < tau)
    (hne : policies ≠ []) (hnodup : policies.Nodup) :
    ∀ x ∈ softmaxWithFPi habit grade fPi tau policies hhabit htau hne hnodup, 0 ≤ x := by
  intro x hx
  simp only [softmaxWithFPi] at hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  obtain ⟨π, _, hπ⟩ := List.mem_map.mp hw
  subst hπ
  exact div_nonneg (Real.exp_pos _).le
    (softmaxWithFPi_total_pos habit grade fPi tau policies hne).le

/-- The output weights of the full policy posterior sum to one: the carrier is
a probability distribution over the policy list. -/
theorem softmaxWithFPi_sum_eq_one {PolicyIndex : Type*} (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → DarkTower.WarMachine.Holes.ExpectedFreeEnergyValue)
    (fPi : PolicyIndex → ℝ) (tau : ℝ) (policies : List PolicyIndex)
    (hhabit : ∀ π, 0 < habit π) (htau : 0 < tau)
    (hne : policies ≠ []) (hnodup : policies.Nodup) :
    (softmaxWithFPi habit grade fPi tau policies hhabit htau hne hnodup).sum = 1 := by
  simp only [softmaxWithFPi]
  rw [sum_map_div, foldl_add_eq, zero_add]
  have h := softmaxWithFPi_total_pos habit grade fPi tau policies hne
  rw [foldl_add_eq, zero_add] at h
  exact div_self (ne_of_gt h)

/-- With an identically zero policy free-energy term, the general carrier is
exactly the existing closed-by-record softmax object (at `Real.exp`,
`Real.log`, which the frozen `Holes.softmax` accepts unchanged). -/
theorem softmaxWithFPi_zero {PolicyIndex : Type*} (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → DarkTower.WarMachine.Holes.ExpectedFreeEnergyValue)
    (tau : ℝ) (policies : List PolicyIndex)
    (hhabit : ∀ π, 0 < habit π) (htau : 0 < tau)
    (hne : policies ≠ []) (hnodup : policies.Nodup) :
    softmaxWithFPi habit grade (fun _ => 0) tau policies hhabit htau hne hnodup =
      DarkTower.WarMachine.Holes.softmax Real.exp Real.log habit grade tau policies := by
  simp [softmaxWithFPi, DarkTower.WarMachine.Holes.softmax]

end

end DarkTower.WarMachine.PolicyPosterior
