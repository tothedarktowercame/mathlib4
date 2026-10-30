import DarkTower.WarMachine.R20Step

/-! Click-local Q6 reselection. There was no separate reading-reselection model.
The ordinary R20 cascade ranks the reduced field; the exclusion is evidence for
this click, not a mutation of the next click's observation. -/
namespace DarkTower.WarMachine.ReadingRefusalReselection
open R20Step

/-- Only a checked refusal on unchanged inputs removes the target. -/
def reducedField (field : List Candidate) (target : Target)
    (refused : Bool) (previousDigest currentDigest : String) : List Candidate :=
  if refused && previousDigest == currentDigest then
    field.filter (fun c => c.target != target)
  else field

theorem unchanged_excludes (field : List Candidate) (target : Target) (digest : String)
    {c : Candidate} (h : c ∈ reducedField field target true digest digest) :
    c ∈ field ∧ c.target ≠ target := by
  simpa [reducedField] using h

theorem changed_eligible (field : List Candidate) (target : Target)
    (old current : String) (h : old ≠ current) :
    reducedField field target true old current = field := by
  simp [reducedField, h]

/-- Every remaining candidate produced by R20's cascade came from the reduced
field, so no ordering step can reintroduce the Q6-refused target. -/
theorem ranked_mem_reduced (cascade : SelectionCascade) (facts : Target → GiraffeFacts)
    (field : List Candidate) (target : Target) (digest : String) {c : Candidate}
    (h : c ∈ applySelectionCascade cascade facts
      (reducedField field target true digest digest)) :
    c ∈ field ∧ c.target ≠ target :=
  unchanged_excludes field target digest (applySelectionCascade_mem h)

/-- Click 50's refusal digest, retained by the click-51 preview. -/
def click50Digest : String :=
  "c1801780489bea4ed72638a53cca7b1e0d55c0b1d97357c00b9659f41eb6d315"

theorem click50_unchanged (field : List Candidate) (target : Target) {c : Candidate}
    (h : c ∈ reducedField field target true click50Digest click50Digest) :
    c.target ≠ target := (unchanged_excludes field target click50Digest h).2

theorem click50_changed (field : List Candidate) (target : Target) :
    reducedField field target true click50Digest "changed-inputs" = field := by
  apply changed_eligible
  decide
end DarkTower.WarMachine.ReadingRefusalReselection
