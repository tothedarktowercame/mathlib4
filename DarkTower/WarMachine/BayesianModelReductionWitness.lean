import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.BayesianModelReductionWitness

open Holes

/-- Hand-derived count preservation: `A-a = [9,3]`; replacing the old prior
`[1,1]` by `[1,1/100]` therefore gives `[10,301/100]`. -/
theorem countPreservingReduction :
    bayesianModelReduction [10, 4] [1, (1 / 100 : ℝ)] [1, 1] =
      [10, (301 / 100 : ℝ)] := by
  norm_num [bayesianModelReduction]

end DarkTower.WarMachine.BayesianModelReductionWitness
