import DarkTower.WarMachine.MachineBeliefState

namespace DarkTower.WarMachine.MachineTransition
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineBeliefState

inductive Action | advanceMission | applyCascade deriving DecidableEq, Repr

def next : Status → Action → Status
  | .spawned, .advanceMission => .refined
  | .refined, .advanceMission => .strengthened
  | .addressed, .applyCascade => .foreclosed
  | .falsified, .applyCascade => .reopened
  | s, _ => s

/-- The v1 declared prior used by the source constructor: every controlled row
has the full seven-state support, including its explicit zero masses. -/
noncomputable def controlled : TransitionKernel Status Action where
  support := fun _ => Status.all
  mass := fun (sa : Status × Action) s' => if s' = next sa.1 sa.2 then 1 else 0
  nonnegative := by intros; split <;> norm_num
  normalised := by
    intro sa
    rcases sa with ⟨s, a⟩
    cases s <;> cases a <;> simp [Status.all, next]

theorem constructionRule (s s' : Status) (a : Action) :
    controlled.mass (s, a) s' = if s' = next s a then 1 else 0 := rfl

theorem completeSupport (s : Status) (a : Action) :
    controlled.support (s, a) = Status.all := rfl

theorem everyRowNormalised (s : Status) (a : Action) :
    ((controlled.support (s, a)).map (controlled.mass (s, a))).sum = 1 :=
  controlled.normalised (s, a)

theorem declaredActionsDistinguished :
    controlled.mass (.spawned, .advanceMission) .refined = 1 ∧
    controlled.mass (.spawned, .applyCascade) .refined = 0 := by
  norm_num [controlled, next]

end DarkTower.WarMachine.MachineTransition
