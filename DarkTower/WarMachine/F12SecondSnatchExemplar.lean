import DarkTower.WarMachine.F12SnatchExemplar

/-! # F12 second snatch exemplar

The `[:g2 :snatcher]` row is the second of the six rows computed by
`cascade-diff-table`.  It tests the ruled no-bootstrap subtraction on a
different non-empty `addedByOrganise` set from the `[:g4 :snatcher]` exemplar.
-/

open Set
namespace DarkTower.WarMachine.Holes
noncomputable section

def snatchG2Selected : Set Nat := {3, 10, 20}
def snatchG2Added : Set Nat := {9, 18, 22}

def organiseSnatchG2 : RuledOrganiseType Unit Nat Int := fun _ sel repo adm =>
  { selected := sel
    nodes := sel ∪ snatchG2Added ∪ adm
    addedByOrganise := snatchG2Added
    admittedBy := adm
    authoredEdges := repo.standsOn
    organisedEdges := fastForward ((sel ∪ snatchG2Added ∪ adm) \ snatchG2Added) repo.standsOn
    precedenceBefore := [3, 9, 10, 20]
    precedenceAfter := [20, 3, 9, 10]
    actingOrderBefore := [10, 3, 20]
    actingOrderAfter := [20]
    scoreBefore := -10
    scoreAfter := -10 }

theorem organiseSnatchG2Conformant : ConformantOrganiseRuled organiseSnatchG2 where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; rfl
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; rfl
  o4 := by intros; left; simp [organiseSnatchG2]

def snatchG2RecordedEdges : List (Nat × Nat) :=
  [(3, 9), (9, 18), (9, 22), (10, 18), (18, 22)]

def snatchG2InAdded (n : Nat) : Bool := n == 9 || n == 18 || n == 22

theorem snatchG2InAdded_iff (n : Nat) :
    snatchG2InAdded n = true ↔ n ∈ snatchG2Added := by
  simp only [snatchG2InAdded, snatchG2Added, Bool.or_eq_true, beq_iff_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Unlike the first exemplar's one survivor, every recorded edge in this row
has an endpoint supplied by `addedByOrganise`; the ruled subtraction keeps
none. -/
theorem snatchG2NoRecordedEdgeSurvives :
    snatchG2RecordedEdges.filter
      (fun e => !(snatchG2InAdded e.1 || snatchG2InAdded e.2)) = [] := by
  decide

theorem snatchG2RecordedEdgeCount : snatchG2RecordedEdges.length = 5 := by decide

/-- A representative recorded edge is refused by the ruled subtraction
because its destination was supplied by `addedByOrganise`. -/
theorem organiseSnatchG2NotEdge39 :
    ¬ (organiseSnatchG2 trivialPolicyCascade snatchG2Selected snatchRepo ∅).organisedEdges 3 9 := by
  intro h
  exact h.2.1.2 (by simp [snatchG2Added])

end
end DarkTower.WarMachine.Holes
