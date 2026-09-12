import DarkTower.WarMachine.MachineModelSpec

namespace DarkTower.WarMachine.MachineBeliefDistribution
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineBeliefState

/-- The row-7 context selects one entity; joint contexts require another type. -/
structure EntityContext where
  entity : Entity
  modelId : String
  modelRevision : String

noncomputable def selectedKernel (posterior : Posterior)
    (hn : ∀ s, 0 ≤ posterior s) (h₁ : Normalised posterior) :
    ProbabilityKernel Unit Status where
  support _ := Status.all
  mass _ := posterior
  nonnegative _ s := hn s
  normalised _ := h₁

theorem selectedKernel_normalised (posterior : Posterior)
    (hn : ∀ s, 0 ≤ posterior s) (h₁ : Normalised posterior) :
    ((selectedKernel posterior hn h₁).support () |>.map
      ((selectedKernel posterior hn h₁).mass ())).sum = 1 :=
  (selectedKernel posterior hn h₁).normalised ()

theorem selectedKernel_coordinate (posterior : Posterior)
    (hn : ∀ s, 0 ≤ posterior s) (h₁ : Normalised posterior) (s : Status) :
    (selectedKernel posterior hn h₁).mass () s = posterior s := rfl

theorem selectedPosterior_conserved (stored : machineBeliefState)
    (context : EntityContext) (posterior : Posterior)
    (hp : stored context.entity = some posterior)
    (hn : ∀ s, 0 ≤ posterior s) (h₁ : Normalised posterior) :
    stored context.entity = some posterior ∧
      ∀ s, (selectedKernel posterior hn h₁).mass () s = posterior s := by
  exact ⟨hp, fun _ => rfl⟩

end DarkTower.WarMachine.MachineBeliefDistribution
