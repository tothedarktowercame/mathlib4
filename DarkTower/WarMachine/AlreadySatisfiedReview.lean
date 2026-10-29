/- An existing artifact qualifies a claim for review, not for closing.
   Refines the classifier boundary of AlreadySatisfiedArtifactRefSeam without
   changing its commit-existence precondition or historical observations. -/
namespace DarkTower.WarMachine.AlreadySatisfiedReview
inductive Verdict where
  | accept | refuse | apparatusDefect
  deriving DecidableEq
structure Evidence where
  commitExists : Bool
  sameArtifact : Bool
  completionSupplied : Bool
  reviewExecuted : Bool
  verdict : Verdict
inductive Result where
  | invalid | alreadySatisfied | ordinaryRefused | apparatusFailure
  deriving DecidableEq
 def checked (e : Evidence) : Bool :=
  e.commitExists && e.sameArtifact && e.completionSupplied && e.reviewExecuted
 def close (e : Evidence) : Result :=
  if checked e then
    match e.verdict with
    | .accept => .alreadySatisfied
    | .refuse => .ordinaryRefused
    | .apparatusDefect => .apparatusFailure
  else .invalid
 theorem alreadySatisfied_iff_reviewed (e : Evidence) :
    close e = .alreadySatisfied ↔ checked e = true ∧ e.verdict = .accept := by
  cases e with
  | mk a b c d v => cases a <;> cases b <;> cases c <;> cases d <;> cases v <;> decide
 theorem ordinary_refusal_not_apparatus (e : Evidence)
    (h : checked e = true) (v : e.verdict = .refuse) :
    close e = .ordinaryRefused := by simp [close, h, v]
 theorem existence_alone_does_not_close (e : Evidence)
    (h : e.reviewExecuted = false) : close e = .invalid := by
  simp [close, checked, h]
end DarkTower.WarMachine.AlreadySatisfiedReview
