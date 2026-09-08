import DarkTower.WarMachine.F12SnatchExemplar

/-! # F12 fourth snatch exemplar

The `[:g1 :sharer]` row is the next unfinished row from the six-row joint
census. Its two non-empty `addedByOrganise` nodes touch every computed edge.
-/

open Set
namespace DarkTower.WarMachine.Holes
noncomputable section

def snatchG1SharerSelected : Set Nat := {6, 10}
def snatchG1SharerAdded : Set Nat := {18, 22}

def organiseSnatchG1Sharer : RuledOrganiseType Unit Nat Int := fun _ sel repo adm =>
  { selected := sel
    nodes := sel ∪ snatchG1SharerAdded ∪ adm
    addedByOrganise := snatchG1SharerAdded
    admittedBy := adm
    authoredEdges := repo.standsOn
    organisedEdges := fastForward ((sel ∪ snatchG1SharerAdded ∪ adm) \ snatchG1SharerAdded) repo.standsOn
    precedenceBefore := [5, 2, 0, 3, 6, 10, 20]
    precedenceAfter := [20, 5, 2, 0, 3, 6, 10]
    actingOrderBefore := [10, 6]
    actingOrderAfter := [20, 6]
    scoreBefore := 15
    scoreAfter := 15 }

theorem organiseSnatchG1SharerConformant :
    ConformantOrganiseRuled organiseSnatchG1Sharer where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; rfl
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; rfl
  o4 := by intros; left; simp [organiseSnatchG1Sharer]

def snatchG1SharerRecordedEdges : List (Nat × Nat) :=
  [(6, 18), (10, 18), (18, 22)]

def snatchG1SharerInAdded (n : Nat) : Bool := n == 18 || n == 22

theorem snatchG1SharerNoRecordedEdgeSurvives :
    snatchG1SharerRecordedEdges.filter
      (fun e => !(snatchG1SharerInAdded e.1 || snatchG1SharerInAdded e.2)) = [] := by
  decide

theorem snatchG1SharerRecordedEdgeCount :
    snatchG1SharerRecordedEdges.length = 3 := by decide

theorem organiseSnatchG1SharerNotEdge618 :
    ¬ (organiseSnatchG1Sharer trivialPolicyCascade snatchG1SharerSelected
        snatchRepo ∅).organisedEdges 6 18 := by
  intro h
  exact h.2.1.2 (by simp [snatchG1SharerAdded])

end
end DarkTower.WarMachine.Holes
