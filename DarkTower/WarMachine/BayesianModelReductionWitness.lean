import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.BayesianModelReductionWitness

open Holes

structure CountReductionReference where
  oldPosterior : List ℝ
  reducedPrior : List ℝ
  oldPrior : List ℝ
  reducedPosterior : List ℝ

noncomputable def countReductionReference : CountReductionReference :=
  { oldPosterior := [10, 4]
    reducedPrior := [1, 1 / 100]
    oldPrior := [1, 1]
    reducedPosterior := [10, 301 / 100] }

/-- Hand-derived count preservation: `A-a = [9,3]`; replacing the old prior
`[1,1]` by `[1,1/100]` therefore gives `[10,301/100]`. -/
theorem countPreservingReduction :
    bayesianModelReduction countReductionReference.oldPosterior
      countReductionReference.reducedPrior countReductionReference.oldPrior =
      countReductionReference.reducedPosterior := by
  norm_num [countReductionReference, bayesianModelReduction]

end DarkTower.WarMachine.BayesianModelReductionWitness
