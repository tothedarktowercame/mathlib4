import DarkTower.WarMachine.F12SnatchExemplar

/-! # F12 sixth snatch exemplar

The `[:g5 :sharer]` row is the last of the six joint-census rows. Its two
non-empty `addedByOrganise` nodes touch all three computed edges.
-/

open Set
namespace DarkTower.WarMachine.Holes
noncomputable section

def snatchG5SharerSelected : Set Nat := {6, 10}
def snatchG5SharerAdded : Set Nat := {18, 22}

def organiseSnatchG5Sharer : RuledOrganiseType Unit Nat Int := fun _ sel repo adm =>
  { selected := sel
    nodes := sel ∪ snatchG5SharerAdded ∪ adm
    addedByOrganise := snatchG5SharerAdded
    admittedBy := adm
    authoredEdges := repo.standsOn
    organisedEdges := fastForward ((sel ∪ snatchG5SharerAdded ∪ adm) \ snatchG5SharerAdded) repo.standsOn
    precedenceBefore := [5, 2, 0, 3, 4, 6, 10]
    precedenceAfter := [4, 6, 5, 2, 0, 3, 10]
    actingOrderBefore := [10, 6]
    actingOrderAfter := [4, 6]
    scoreBefore := 15
    scoreAfter := 15 }

theorem organiseSnatchG5SharerConformant :
    ConformantOrganiseRuled organiseSnatchG5Sharer where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; rfl
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; rfl
  o4 := by intros; left; simp [organiseSnatchG5Sharer]

def snatchG5SharerRecordedEdges : List (Nat × Nat) :=
  [(6, 18), (10, 18), (18, 22)]

def snatchG5SharerInAdded (n : Nat) : Bool := n == 18 || n == 22

theorem snatchG5SharerNoRecordedEdgeSurvives :
    snatchG5SharerRecordedEdges.filter
      (fun e => !(snatchG5SharerInAdded e.1 || snatchG5SharerInAdded e.2)) = [] := by
  decide

theorem snatchG5SharerRecordedEdgeCount :
    snatchG5SharerRecordedEdges.length = 3 := by decide

theorem organiseSnatchG5SharerNotEdge618 :
    ¬ (organiseSnatchG5Sharer trivialPolicyCascade snatchG5SharerSelected
        snatchRepo ∅).organisedEdges 6 18 := by
  intro h
  exact h.2.1.2 (by simp [snatchG5SharerAdded])

end
end DarkTower.WarMachine.Holes
