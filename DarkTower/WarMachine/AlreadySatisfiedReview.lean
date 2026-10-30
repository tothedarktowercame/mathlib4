/- An existing artifact qualifies a claim for review, not for closing.
   Refines the classifier boundary of AlreadySatisfiedArtifactRefSeam without
   changing its commit-existence precondition or historical observations.

   Revision 2 (2026-10-30, click fc2e27e3): a qualified claim must also cite
   the selected target before review.  Click 50 of the criteria-completeness
   campaign (run `2026-10-30-e5f08d91`, target M-typed-memories) claimed
   futon3c `7aac5ca07`, whose message says `Mission: M-giraffe` and whose one
   file is `holes/excursions/E-argument-game-search.md`.  Commit existence
   alone qualified it, a reviewer seat was dispatched and charged, and the
   click closed `:reviewed-claim-refused` four hours later.

   `citesTarget` transcribes `claimed-commit-cites-target` (futon2
   `src/futon2/aif/full_loop_runner.clj`): the commit message names the
   target id, or a changed file is the selected mission's source file, or a
   changed path carries the target id.  `review-already-satisfied-claim!`
   evaluates it after the completion source pin is verified and before the
   first charge.  A qualified claim that does not cite the target closes
   `claimNotOnTarget` (`:guardrail-refusal` /
   `:claimed-artifact-not-on-selected-target`) with no review executed
   (`noncited_closes_without_review`); a citing claim closes exactly as in
   revision 1 (`close_eq_closeByReview_of_cites`).  The check never approves
   (`alreadySatisfied_iff_reviewed`): a citing commit still goes to the
   reviewer, who judges satisfaction.  Like `ordinaryRefused`,
   `claimNotOnTarget` is the author's answer and not the apparatus, so it is
   a non-injury (`explicit-non-injury-kinds` in `meta_terminal_injury.clj`,
   `no-finding-required?` in `stop_line.clj`). -/
namespace DarkTower.WarMachine.AlreadySatisfiedReview
inductive Verdict where
  | accept | refuse | apparatusDefect
  deriving DecidableEq
structure Evidence where
  commitExists : Bool
  sameArtifact : Bool
  completionSupplied : Bool
  /-- Revision 2: the claimed commit is visibly work on the selected target. -/
  citesTarget : Bool
  reviewExecuted : Bool
  verdict : Verdict
inductive Result where
  | invalid | alreadySatisfied | ordinaryRefused | apparatusFailure
  /-- Revision 2: refused mechanically before review; no reviewer dispatched. -/
  | claimNotOnTarget
  deriving DecidableEq
/-- Commit existence, artifact identity and the pinned completion definition:
what qualifies a claim for the citation check, and then for review. -/
def qualified (e : Evidence) : Bool :=
  e.commitExists && e.sameArtifact && e.completionSupplied
/-- Revision 1's `checked`: a qualified claim whose review executed. -/
def checkedByReview (e : Evidence) : Bool :=
  qualified e && e.reviewExecuted
/-- Revision 2: review counts only for a claim that cites the target. -/
def checked (e : Evidence) : Bool :=
  checkedByReview e && e.citesTarget
/-- Revision 1's close: review decides whenever the claim is checked. -/
def closeByReview (e : Evidence) : Result :=
  if checkedByReview e then
    match e.verdict with
    | .accept => .alreadySatisfied
    | .refuse => .ordinaryRefused
    | .apparatusDefect => .apparatusFailure
  else .invalid
/-- Revision 2's close: a qualified claim that does not cite the target is
refused before review; otherwise review decides as in revision 1. -/
def close (e : Evidence) : Result :=
  if qualified e && !e.citesTarget then .claimNotOnTarget else closeByReview e
/-- Which results the terminal classifier reads as non-injuries: the
successful claim, and the two refusals that are the author's answer rather
than the apparatus (`ordinaryRefused` is `:reviewed-claim-refused`,
`claimNotOnTarget` is `:claimed-artifact-not-on-selected-target`). -/
def nonInjury : Result → Bool
  | .alreadySatisfied | .ordinaryRefused | .claimNotOnTarget => true
  | .invalid | .apparatusFailure => false
theorem alreadySatisfied_iff_reviewed (e : Evidence) :
    close e = .alreadySatisfied ↔ checked e = true ∧ e.verdict = .accept := by
  cases e with
  | mk a b c d r v =>
    cases a <;> cases b <;> cases c <;> cases d <;> cases r <;> cases v <;> decide
theorem ordinary_refusal_not_apparatus (e : Evidence)
    (h : checked e = true) (v : e.verdict = .refuse) :
    close e = .ordinaryRefused := by
  revert h v
  cases e with
  | mk a b c d r v =>
    cases a <;> cases b <;> cases c <;> cases d <;> cases r <;> cases v <;> decide
/-- Revision 1's theorem, now for a citing claim: existence without a
review closes nothing. -/
theorem existence_alone_does_not_close (e : Evidence)
    (h : e.reviewExecuted = false) (hc : e.citesTarget = true) : close e = .invalid := by
  simp [close, closeByReview, checkedByReview, h, hc]
/-- A citing claim closes exactly as it did in revision 1. -/
theorem close_eq_closeByReview_of_cites (e : Evidence) (hc : e.citesTarget = true) :
    close e = closeByReview e := by
  simp [close, hc]
/-- A qualified claim that does not cite the target is refused whatever the
review would have said, and whether or not one ran. -/
theorem noncited_closes_without_review (e : Evidence)
    (hq : qualified e = true) (hc : e.citesTarget = false) :
    close e = .claimNotOnTarget := by
  simp [close, hq, hc]
/-- The citation refusal is the author's answer, not the apparatus. -/
theorem claimNotOnTarget_nonInjury : nonInjury .claimNotOnTarget = true := rfl
/-- Click fc2e27e3 before any reviewer is dispatched: the commit exists, is
the claimed artifact, the completion definition is pinned, and the commit
does not cite M-typed-memories. -/
def click50 : Evidence := ⟨true, true, true, false, false, .refuse⟩
/-- Revision 2 refuses click 50's claim with no review executed. -/
theorem click50_refused_before_review : close click50 = .claimNotOnTarget := by decide
/-- What happened under revision 1: the same claim went to review, the
reviewer refused it, and the close was the ordinary reviewed refusal. -/
theorem click50_revision1_reviewed :
    closeByReview { click50 with reviewExecuted := true } = .ordinaryRefused := by decide
/-- Click 14's retained shape: the claimed commit touches the selected
mission's own file, so it cites the target and review decides. -/
theorem click14_still_reviewed :
    close ⟨true, true, true, true, true, .accept⟩ = .alreadySatisfied := by decide
end DarkTower.WarMachine.AlreadySatisfiedReview
