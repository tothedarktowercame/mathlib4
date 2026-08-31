import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.BeliefUpdateFalsifier

open Holes

private def kernel : observationKernel Channel Channel where
  support s := [s]
  mass s o := if s = o then 1 else 0
  nonnegative s o := by split <;> norm_num
  normalised s := by simp

private def learningRate : NonnegativeReal := ⟨1, by norm_num⟩
private def precision : PrecisionMap := fun _ => ⟨1, by norm_num⟩
private def prior : BeliefState :=
  {mean := fun _ => 0, variance := fun _ => ⟨1, by norm_num⟩}
private def observation : Channel → ℝ := fun _ => 1
private def posterior : BeliefState :=
  {mean := fun _ => 1, variance := prior.variance}

/-- Positive control: the declared correction moves the mean and eliminates
the fixture's prediction error, so its VFE cannot increase. -/
example : beliefUpdate learningRate kernel prior observation precision posterior := by
  constructor
  · funext k
    simp [posterior, prior, learningRate, precision, observation,
      observationKernelRowMass, predictionError, kernel]
  · simp [variationalFreeEnergy, predictionError, posterior, precision,
      observation, prior, Channel.all, div_eq_mul_inv]
    repeat apply add_nonneg <;> norm_num

/-- Negative control: the shape-correct prior is not an update.  The C16
runner mutates this negation away and requires Lean to reject the result. -/
example : ¬ beliefUpdate learningRate kernel prior observation precision prior := by
  intro h
  have moved := congrFun h.1 Channel.loopHealth
  norm_num [prior, learningRate, precision, observation,
    observationKernelRowMass, predictionError, kernel] at moved

end DarkTower.WarMachine.BeliefUpdateFalsifier
