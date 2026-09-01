import DarkTower.WarMachine.BayesianModelReductionWitness

open DarkTower.WarMachine.Holes

-- Must fail: the second component adds the new prior without removing the old
-- one, so it does not preserve the accumulated count vector.
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : bayesianModelReduction [10, 4] [1, (1 / 100 : ℝ)] [1, 1] =
    [10, (401 / 100 : ℝ)] := by
  norm_num [bayesianModelReduction]
