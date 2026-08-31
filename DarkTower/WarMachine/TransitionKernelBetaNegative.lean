import DarkTower.WarMachine.TransitionKernelWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.TransitionKernelWitness

noncomputable def alpha : DirichletConcentrations := ⟨[1, 1], by simp⟩
noncomputable def betaNormaliser : ℝ := Real.exp (logMultivariateBeta alpha)

-- Must fail: B(alpha), a scalar Dirichlet normalizer, is not transition B.
def badTransition : TransitionKernel State Action := betaNormaliser
