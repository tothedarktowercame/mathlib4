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
  support_nodup := by intro; simp [Status.all]
  mass_eq_zero_of_not_mem := by intro s o h; cases o <;> simp_all [Status.all]
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
  have h : Status.refined ≠ Status.spawned := by decide
  simp [controlled, next, h]

/-- Rejection case (the carrier's falsifier, `Holes.lean` TransitionKernel):
an action-unconditioned state kernel. Lawful as a kernel, but every row pair
for the declared-distinct actions is equal, and it fails the declared
construction rule at the pair `declaredActionsDistinguished` exhibits. -/
noncomputable def uncontrolled : TransitionKernel Status Action where
  support := fun _ => Status.all
  mass := fun sa s' => if s' = sa.1 then 1 else 0
  nonnegative := by intros; split <;> norm_num
  support_nodup := by intro; simp [Status.all]
  mass_eq_zero_of_not_mem := by intro s o h; cases o <;> simp_all [Status.all]
  normalised := by intro sa; rcases sa with ⟨s, _⟩; cases s <;> simp [Status.all]

theorem uncontrolledActionsIndistinguishable (s : Status) :
    uncontrolled.mass (s, .advanceMission) = uncontrolled.mass (s, .applyCascade) := rfl

theorem uncontrolledFailsDeclaredRule :
    uncontrolled.mass (.spawned, .advanceMission) .refined = 0 := by
  have h : Status.refined ≠ Status.spawned := by decide
  simp [uncontrolled, h]

/-- Rejection case (same falsifier): the scalar multivariate-beta normaliser
broadcast as a mass function. Off `1/7` it cannot normalise a seven-state
row, and as a constant it is action-unconditioned, so it is rejected as a
controlled `B` either way. -/
theorem betaNormaliserRowUnnormalised (b : ℝ) (h : b ≠ 1 / 7) :
    ((Status.all).map (fun _ : Status => b)).sum ≠ 1 := by
  simp [Status.all]
  intro hc
  apply h
  linarith

theorem betaNormaliserActionUnconditioned (b : ℝ) (s : Status) :
    (fun (_ : Status × Action) (_ : Status) => b) (s, .advanceMission)
      = (fun (_ : Status × Action) (_ : Status) => b) (s, .applyCascade) := rfl

end DarkTower.WarMachine.MachineTransition
