import DarkTower.WarMachine.SoftmaxWitness

namespace DarkTower.WarMachine.SoftmaxNegative

open Holes SoftmaxWitness

-- Negative control: the sign-inverted ordering must not elaborate.
theorem invertedOrderSlips :
    softmax Real.exp Real.log habit grade (1 / 3 : ℝ)
      [.lower, .higher] = [1 / 9, 8 / 9] := by
  simp [softmax, habit, grade, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 8)]

end DarkTower.WarMachine.SoftmaxNegative
