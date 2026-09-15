import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.TransitionKernelWitness

open Holes

inductive State where | idle | active deriving DecidableEq
inductive Action where | stay | start deriving DecidableEq

/-- Hand-derived deterministic controlled dynamics: `stay` preserves state;
`start` moves either state to active. Each `(state, action)` row has mass one. -/
noncomputable def controlled : TransitionKernel State Action where
  support
    | (s, .stay) => [s]
    | (_, .start) => [.active]
  mass := fun sa o => match sa with
    | (s, .stay) => if o = s then 1 else 0
    | (_, .start) => if o = .active then 1 else 0
  nonnegative := by intro sa o; rcases sa with ⟨s,a⟩; cases a <;> dsimp <;> split <;> norm_num
  support_nodup := by intro sa; rcases sa with ⟨s,a⟩; cases a <;> simp
  mass_eq_zero_of_not_mem := by intro sa o h; rcases sa with ⟨s,a⟩; cases a <;> simp_all
  normalised := by intro sa; cases sa with | mk s a => cases a <;> simp

theorem startRowMass :
    ((controlled.support (.idle, .start)).map
      (controlled.mass (.idle, .start))).sum = 1 :=
  controlled.normalised (.idle, .start)

theorem allControlledRowsNormalised (s : State) (a : Action) :
    ((controlled.support (s, a)).map (controlled.mass (s, a))).sum = 1 :=
  controlled.normalised (s, a)

end DarkTower.WarMachine.TransitionKernelWitness
