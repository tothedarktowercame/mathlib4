import DarkTower.WarMachine.Holes

/-! The positive import contract accepts a nonzero realised update and rejects
missing provenance, ignored outcomes, duplicate receipts and an unconnected
consumer. These are model controls, not evidence of a production run. -/
namespace DarkTower.WarMachine.DirichletImportControls
open Holes
noncomputable section

def observation (c : Channel) : ℝ := if c = .loopHealth then 1 else 0
def belief (_ : Unit) : ℝ := 1

def realised (receipt : Nat) (o : Channel → ℝ) (s : Unit → ℝ) : Prop :=
  receipt = 7 ∧ o = observation ∧ s = belief

def witness : DirichletAccumulationWitness Unit Nat where
  prior := fun _ _ => 1
  outcomes := [(7, observation, belief)]
  updated := fun c _ => 1 + observation c
  consumerInput := fun c _ => 1 + observation c

theorem accepts_realised_accumulation :
    dirichletAccumulationFeedsConcentrations realised witness where
  nonempty := by simp [witness]
  uniqueReceipts := by simp [witness]
  outcomesRealised := by
    intro tick ht
    simp only [witness, List.mem_singleton] at ht
    subst tick
    exact ⟨rfl, rfl, rfl⟩
  observationsNonnegative := by
    intro tick ht c
    simp only [witness, List.mem_singleton] at ht
    subst tick
    simp [observation]
    split_ifs <;> norm_num
  statesNonnegative := by
    intro tick ht s
    simp only [witness, List.mem_singleton] at ht
    subst tick
    norm_num [belief]
  priorPositive := by intro c s; norm_num [witness]
  accumulation := by intro c s; simp [witness, belief]
  contribution := by
    refine ⟨.loopHealth, (), ?_⟩
    norm_num [witness, observation, belief]
  updatedPositive := by
    intro c s
    simp [witness, observation]
    split_ifs <;> norm_num
  consumed := rfl

theorem rejects_no_outcomes :
    ¬ dirichletAccumulationFeedsConcentrations realised {witness with outcomes := []} :=
  fun h => h.nonempty rfl

theorem rejects_unrealised_outcome :
    ¬ dirichletAccumulationFeedsConcentrations realised
      {witness with outcomes := [(99, observation, belief)]} := by
  intro h
  have bad := h.outcomesRealised (99, observation, belief) (by simp)
  norm_num [realised] at bad

theorem rejects_duplicate_receipts :
    ¬ dirichletAccumulationFeedsConcentrations realised
      {witness with outcomes := [(7, observation, belief), (7, observation, belief)]} := by
  intro h
  have bad := h.uniqueReceipts
  simp at bad

theorem rejects_ignored_outcome :
    ¬ dirichletAccumulationFeedsConcentrations realised
      {witness with updated := witness.prior} := by
  intro h
  have bad := h.accumulation .loopHealth ()
  norm_num [witness, observation, belief] at bad

theorem rejects_unconnected_consumer :
    ¬ dirichletAccumulationFeedsConcentrations realised
      {witness with consumerInput := witness.prior} := by
  intro h
  have bad := congrFun (congrFun h.consumed .loopHealth) ()
  norm_num [witness, observation] at bad

#print axioms accepts_realised_accumulation
#print axioms rejects_no_outcomes
#print axioms rejects_unrealised_outcome
#print axioms rejects_duplicate_receipts
#print axioms rejects_ignored_outcome
#print axioms rejects_unconnected_consumer
end
end DarkTower.WarMachine.DirichletImportControls
