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
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalised := by intro sa; cases sa with | mk s a => cases a <;> simp

theorem startRowMass :
    ((controlled.support (.idle, .start)).map
      (controlled.mass (.idle, .start))).sum = 1 :=
  controlled.normalised (.idle, .start)

theorem allControlledRowsNormalised (s : State) (a : Action) :
    ((controlled.support (s, a)).map (controlled.mass (s, a))).sum = 1 :=
  controlled.normalised (s, a)

end DarkTower.WarMachine.TransitionKernelWitness
