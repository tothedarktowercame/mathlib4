import DarkTower.WarMachine.F12RuledCarrier

/-! # F12 ants exemplar

Index map from `futon3:checks/ants-cascade.edn:69-74` and its admitted member:
`0` cargo-return-discipline; `1` hunger-precision-coupling; `2`
pheromone-trail-tuner; `3` white-space-scout; `4` baseline-cyber-ant.
-/

open Set
namespace DarkTower.WarMachine.Holes
noncomputable section

/-- Selected ants, from `futon3:checks/ants-cascade.edn:69-74`. -/
def antsSelected : Set Nat := {0, 1, 2, 3}
/-- Admitted ant, from `futon3:checks/ants-cascade.edn:110`. -/
def antsAdmitted : Set Nat := {4}
/-- Empty authored relation, from `futon3:checks/ants-cascade.edn:2`. -/
def antsRepo : Repository Nat where
  patterns := {0, 1, 2, 3, 4}
  standsOn := fun _ _ => False
  acyclic := acyclic_of_increasing_rank _ (fun _ => 0) (by intros; contradiction)
/-- Recorded precedence before, `futon3:checks/ants-cascade.edn:89-93`. -/
def antsPrecedenceBefore : List Nat := [0, 1, 2, 3]
/-- Recorded precedence after, `futon3:checks/ants-cascade.edn:84-88`. -/
def antsPrecedenceAfter : List Nat := [0, 1, 3, 2]
/-- Recorded acting order before, `futon3:checks/ants-cascade.edn:79-83`. -/
def antsActingOrderBefore : List Nat := [0, 1, 2, 3]
/-- Recorded acting order after, `futon3:checks/ants-cascade.edn:75-79`. -/
def antsActingOrderAfter : List Nat := [0, 1, 3, 2]
/-- Printed IEEE digits from `futon3:checks/ants-cascade.edn:94-95`; this Rat
transcribes the printout, not the score computation. -/
def antsScore : Rat := 18759999999999874 / 1000000000000000

/-- Ruled carrier with the six recorded ants O4 fields substituted. -/
def organiseAnts : RuledOrganiseType Unit Nat Rat := fun _ sel repo adm =>
  { selected := sel, nodes := sel ∪ adm, addedByOrganise := ∅, admittedBy := adm
    authoredEdges := repo.standsOn, organisedEdges := fastForward (sel ∪ adm) repo.standsOn
    precedenceBefore := antsPrecedenceBefore, precedenceAfter := antsPrecedenceAfter
    actingOrderBefore := antsActingOrderBefore, actingOrderAfter := antsActingOrderAfter
    scoreBefore := antsScore, scoreAfter := antsScore }

/-- All seven ruled clauses; O4 takes its acting-order disjunct. -/
theorem organiseAntsConformant : ConformantOrganiseRuled organiseAnts where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; simp [organiseAnts]
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; simp [organiseAnts]
  o4 := by intros; left; simp [organiseAnts, antsActingOrderBefore, antsActingOrderAfter]

/-- Unlike zaif, the recorded ants O4 antecedent is true. -/
theorem organiseAntsPrecedenceMoves :
    (organiseAnts trivialPolicyCascade antsSelected antsRepo antsAdmitted).precedenceBefore ≠
      (organiseAnts trivialPolicyCascade antsSelected antsRepo antsAdmitted).precedenceAfter := by
  simp [organiseAnts, antsPrecedenceBefore, antsPrecedenceAfter]

/-- The ants record takes the acting-order branch; its score is flat. -/
theorem organiseAntsActingMovesScoreFlat :
    (organiseAnts trivialPolicyCascade antsSelected antsRepo antsAdmitted).actingOrderBefore ≠
        (organiseAnts trivialPolicyCascade antsSelected antsRepo antsAdmitted).actingOrderAfter ∧
      (organiseAnts trivialPolicyCascade antsSelected antsRepo antsAdmitted).scoreBefore =
        (organiseAnts trivialPolicyCascade antsSelected antsRepo antsAdmitted).scoreAfter := by
  simp [organiseAnts, antsActingOrderBefore, antsActingOrderAfter]

/-- The precedence change is a reordering, not a membership change. -/
theorem antsPrecedencePerm : antsPrecedenceBefore.Perm antsPrecedenceAfter := by
  decide

/-- With zero authored edges, ants cannot stress O2/O3 non-vacuously. -/
theorem organiseAntsNoOrganisedEdges (u v : Nat) :
    ¬ (organiseAnts trivialPolicyCascade antsSelected antsRepo antsAdmitted).organisedEdges u v := by
  intro h
  have hr := d1_reachOutside_to_reach h.2.2
  change Reach (fun _ _ : Nat => False) u v at hr
  induction hr with
  | single edge => exact edge
  | tail _ edge _ => exact edge

/-- Zaif exercises an edge with flat precedence; ants exercises moving
precedence with no edge. -/
theorem zaifAntsComplementary :
    (organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).organisedEdges 18 19 ∧
    ¬ ((organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).precedenceBefore ≠
      (organiseRuled (Policy := Unit) (Score := Int)
        trivialPolicyCascade d1Selected d1Repo d1Admitted).precedenceAfter) ∧
    (organiseAnts trivialPolicyCascade antsSelected antsRepo antsAdmitted).precedenceBefore ≠
      (organiseAnts trivialPolicyCascade antsSelected antsRepo antsAdmitted).precedenceAfter ∧
    (∀ u v, ¬ (organiseAnts trivialPolicyCascade antsSelected antsRepo antsAdmitted).organisedEdges u v) :=
  ⟨organiseRuledZaifEdge, organiseRuledZaifO4AntecedentFalse,
    organiseAntsPrecedenceMoves, organiseAntsNoOrganisedEdges⟩

/-- Negative control: moving precedence with flat acting order and score. -/
def organiseAntsFlatActingOrder : RuledOrganiseType Unit Nat Rat := fun t sel repo adm =>
  { organiseAnts t sel repo adm with actingOrderAfter := antsActingOrderBefore }

/-- Every clause except O4 holds for the flat-acting control. -/
theorem organiseAntsFlatActingOrderSansO4 :
    ConformantOrganiseRuledSansO4 organiseAntsFlatActingOrder where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; simp [organiseAntsFlatActingOrder, organiseAnts]
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; simp [organiseAntsFlatActingOrder, organiseAnts]

/-- The flat-acting control fails exactly O4. -/
theorem organiseAntsFlatActingOrderNotConformant :
    ¬ ConformantOrganiseRuled organiseAntsFlatActingOrder := by
  intro h
  have := h.o4 trivialPolicyCascade antsSelected antsRepo antsAdmitted
    (by simp [organiseAntsFlatActingOrder, organiseAnts, antsPrecedenceBefore, antsPrecedenceAfter])
  simp [organiseAntsFlatActingOrder, organiseAnts] at this

/-- Positive control: flat acting order but moving score takes O4's right arm. -/
def organiseAntsScoreMovesInstead : RuledOrganiseType Unit Nat Rat := fun t sel repo adm =>
  { organiseAntsFlatActingOrder t sel repo adm with scoreAfter := antsScore + 1 }

/-- The score-moving alternative is fully ruled-conformant. -/
theorem organiseAntsScoreMovesInsteadConformant :
    ConformantOrganiseRuled organiseAntsScoreMovesInstead where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; simp [organiseAntsScoreMovesInstead, organiseAntsFlatActingOrder, organiseAnts]
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; simp [organiseAntsScoreMovesInstead, organiseAntsFlatActingOrder, organiseAnts]
  o4 := by intros; right
           simp [organiseAntsScoreMovesInstead, organiseAntsFlatActingOrder, organiseAnts, antsScore]

end
end DarkTower.WarMachine.Holes
