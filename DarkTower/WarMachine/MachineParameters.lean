import DarkTower.WarMachine.MachinePredictiveOutcome

namespace DarkTower.WarMachine.MachineParameters
noncomputable section
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineBeliefState

inductive Theta | identityTransition | controlledTransition
  deriving DecidableEq, Repr

def Theta.all : List Theta := [.identityTransition, .controlledTransition]

noncomputable def machineParameterPrior (Policy : Type) :
    ParameterPriorKernel Policy Theta where
  support _ := Theta.all
  mass _ _ := 1 / 2
  nonnegative := by intros; norm_num
  normalised := by intros; norm_num [Theta.all]

structure RegisteredLikelihood (Obs : Vertex → Type) where
  outcomes : List (Outcome Obs)
  mass : Theta → Outcome Obs → ℝ
  nonnegative : ∀ t o, 0 ≤ mass t o
  normalised : ∀ t, (outcomes.map (mass t)).sum = 1

def evidence (l : RegisteredLikelihood Obs) (o : Outcome Obs) : ℝ :=
  (l.mass .identityTransition o + l.mass .controlledTransition o) / 2

noncomputable def machineParameterPosterior (Policy : Type)
    (l : RegisteredLikelihood Obs)
    (positive : ∀ o, 0 < evidence l o) :
    ParameterPosteriorKernel Policy Obs Theta where
  support _ := Theta.all
  mass po t := (1 / 2) * l.mass t po.2 / evidence l po.2
  nonnegative := by
    intro po t
    exact div_nonneg (mul_nonneg (by norm_num) (l.nonnegative t po.2))
      (le_of_lt (positive po.2))
  normalised := by
    intro po
    have hs : l.mass .identityTransition po.2 + l.mass .controlledTransition po.2 ≠ 0 := by
      intro hs
      have hz : evidence l po.2 = 0 := by simp [evidence, hs]
      exact (ne_of_gt (positive po.2)) hz
    simp only [Theta.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp [evidence]
    field_simp [hs]

theorem bayesConditioning (Policy : Type) (l : RegisteredLikelihood Obs)
    (positive : ∀ o, 0 < evidence l o) (p : Policy) (o : Outcome Obs) (t : Theta) :
    (machineParameterPosterior Policy l positive).mass (p, o) t =
      (machineParameterPrior Policy).mass p t * l.mass t o / evidence l o := rfl

theorem marginalCompatibility (l : RegisteredLikelihood Obs) (o : Outcome Obs) :
    evidence l o =
      (machineParameterPrior Unit).mass () .identityTransition * l.mass .identityTransition o +
      (machineParameterPrior Unit).mass () .controlledTransition * l.mass .controlledTransition o := by
  simp [evidence, machineParameterPrior]
  ring

/-- Theta is neither the seven-state hidden carrier nor a policy prior index;
continuous Dirichlet concentrations are not members of this finite type. -/
theorem parametersDistinctFromHiddenStates : Theta.all.length ≠ Status.all.length := by
  decide

end
end DarkTower.WarMachine.MachineParameters
