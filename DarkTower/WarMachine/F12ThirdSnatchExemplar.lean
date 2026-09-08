import DarkTower.WarMachine.F12SnatchExemplar

/-! # F12 third snatch exemplar

The `[:g1 :cautious]` row is the next unfinished row from the six-row joint
census.  Its two non-empty `addedByOrganise` nodes touch every computed edge.
-/

open Set
namespace DarkTower.WarMachine.Holes
noncomputable section

def snatchG1CautiousSelected : Set Nat := {5, 10}
def snatchG1CautiousAdded : Set Nat := {18, 22}

def organiseSnatchG1Cautious : RuledOrganiseType Unit Nat Int := fun _ sel repo adm =>
  { selected := sel
    nodes := sel ∪ snatchG1CautiousAdded ∪ adm
    addedByOrganise := snatchG1CautiousAdded
    admittedBy := adm
    authoredEdges := repo.standsOn
    organisedEdges := fastForward ((sel ∪ snatchG1CautiousAdded ∪ adm) \ snatchG1CautiousAdded) repo.standsOn
    precedenceBefore := [5, 2, 0, 3, 6, 10, 20]
    precedenceAfter := [20, 5, 2, 0, 3, 6, 10]
    actingOrderBefore := [10, 5]
    actingOrderAfter := [20]
    scoreBefore := 0
    scoreAfter := 0 }

theorem organiseSnatchG1CautiousConformant :
    ConformantOrganiseRuled organiseSnatchG1Cautious where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; rfl
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; rfl
  o4 := by intros; left; simp [organiseSnatchG1Cautious]

def snatchG1CautiousRecordedEdges : List (Nat × Nat) :=
  [(5, 18), (10, 18), (18, 22)]

def snatchG1CautiousInAdded (n : Nat) : Bool := n == 18 || n == 22

theorem snatchG1CautiousNoRecordedEdgeSurvives :
    snatchG1CautiousRecordedEdges.filter
      (fun e => !(snatchG1CautiousInAdded e.1 || snatchG1CautiousInAdded e.2)) = [] := by
  decide

theorem snatchG1CautiousRecordedEdgeCount :
    snatchG1CautiousRecordedEdges.length = 3 := by decide

theorem organiseSnatchG1CautiousNotEdge518 :
    ¬ (organiseSnatchG1Cautious trivialPolicyCascade snatchG1CautiousSelected
        snatchRepo ∅).organisedEdges 5 18 := by
  intro h
  exact h.2.1.2 (by simp [snatchG1CautiousAdded])

end
end DarkTower.WarMachine.Holes
