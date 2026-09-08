import DarkTower.WarMachine.F12SnatchExemplar

/-! # F12 fifth snatch exemplar

The `[:g1 :snatcher]` row is the fifth of the six joint-census rows. Its two
non-empty `addedByOrganise` nodes touch both computed edges.
-/

open Set
namespace DarkTower.WarMachine.Holes
noncomputable section

def snatchG1SnatcherSelected : Set Nat := {10, 14}
def snatchG1SnatcherAdded : Set Nat := {18, 22}

def organiseSnatchG1Snatcher : RuledOrganiseType Unit Nat Int := fun _ sel repo adm =>
  { selected := sel
    nodes := sel ∪ snatchG1SnatcherAdded ∪ adm
    addedByOrganise := snatchG1SnatcherAdded
    admittedBy := adm
    authoredEdges := repo.standsOn
    organisedEdges := fastForward ((sel ∪ snatchG1SnatcherAdded ∪ adm) \ snatchG1SnatcherAdded) repo.standsOn
    precedenceBefore := [0, 1, 2, 3, 4, 10, 14]
    precedenceAfter := [14, 0, 1, 2, 3, 4, 10]
    actingOrderBefore := [10, 14]
    actingOrderAfter := [14]
    scoreBefore := -5
    scoreAfter := -5 }

theorem organiseSnatchG1SnatcherConformant :
    ConformantOrganiseRuled organiseSnatchG1Snatcher where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; rfl
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; rfl
  o4 := by intros; left; simp [organiseSnatchG1Snatcher]

def snatchG1SnatcherRecordedEdges : List (Nat × Nat) :=
  [(10, 18), (18, 22)]

def snatchG1SnatcherInAdded (n : Nat) : Bool := n == 18 || n == 22

theorem snatchG1SnatcherNoRecordedEdgeSurvives :
    snatchG1SnatcherRecordedEdges.filter
      (fun e => !(snatchG1SnatcherInAdded e.1 || snatchG1SnatcherInAdded e.2)) = [] := by
  decide

theorem snatchG1SnatcherRecordedEdgeCount :
    snatchG1SnatcherRecordedEdges.length = 2 := by decide

theorem organiseSnatchG1SnatcherNotEdge1018 :
    ¬ (organiseSnatchG1Snatcher trivialPolicyCascade snatchG1SnatcherSelected
        snatchRepo ∅).organisedEdges 10 18 := by
  intro h
  exact h.2.1.2 (by simp [snatchG1SnatcherAdded])

end
end DarkTower.WarMachine.Holes
