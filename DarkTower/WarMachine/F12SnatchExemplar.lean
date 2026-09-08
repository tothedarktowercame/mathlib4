import DarkTower.WarMachine.F12RuledCarrier

/-! # F12 snatch exemplar

The 24 indices, in topological order, are:
0 re-enter-after-observed-repair; 1 a-free-mark-is-always-worth-assigning;
2 consult-the-remedy-before-exiting; 3 forced-play-needs-a-loss-floor;
4 use-talk-to-make-a-testable-offer; 5 an-unmodelled-response-stops-the-line;
6 escalate-only-as-far-as-you-can-lose; 7 mark-without-force;
8 non-binding-talk-still-moves-play; 9 preserve-the-right-to-abstain;
10 probe-before-committing; 11 revert-then-invert;
12 accept-an-offer-that-beats-holding; 13 ask-for-surplus-not-surrender;
14 grim-cuts-the-cascade-and-never-widens-it; 15 lead-with-the-exchange-rule;
16 play-the-authored-order-first; 17 promote-the-remedy-before-the-exit;
18 protect-the-unprotected-move; 19 widen-the-cascade-only-on-evidence;
20 exchange-when-both-sides-gain; 21 have-a-temperament;
22 institutions-vary-by-position-and-force; 23 price-the-final-round-as-final.

The row is computed, not directly recorded: `cascade-diff-table` at
`futon3:checks/find_organise.clj:603-633` pairs the fixture's patterns and
exchange-first rows and organises the former over the full snatch repository.
-/

open Set
namespace DarkTower.WarMachine.Holes
noncomputable section

/-- Computed selection; inputs at `futon3:checks/find_organise.clj:616-622`
and `futon3:checks/snatch-cascade.edn:80-83`. -/
def snatchSelected : Set Nat := {0, 2, 10}

/-- Computed additions; inputs at `futon3:checks/find_organise.clj:619-622`
and `futon3:checks/snatch-cascade.edn:73-76`. -/
def snatchAdded : Set Nat := {7, 11, 18, 22}

/-- The computed row admits nothing; `futon3:checks/find_organise.clj:619-622`. -/
def snatchAdmitted : Set Nat := ∅

/-- All 24 repository patterns and 26 authored edges used by
`futon3:checks/find_organise.clj:619-622`; the repository reader is the
`@why` reader used by that computation. -/
def snatchRepo : Repository Nat where
  patterns := Icc 0 23
  standsOn := fun u v => (u, v) ∈
    ({(0,2),(0,11),(1,7),(2,7),(2,11),(3,9),(4,8),(5,18),(6,18),(7,18),(7,22),
      (8,18),(8,22),(9,18),(9,22),(10,18),(11,18),(11,22),(12,20),(13,20),
      (14,21),(15,21),(16,21),(17,21),(18,22),(19,21)} : Finset (Nat × Nat))
  acyclic := acyclic_of_increasing_rank _ id (by
    intro u v h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;> decide)

/-- Computed before precedence from `futon3:checks/find_organise.clj:616,628`
and the patterns row beginning `futon3:checks/snatch-cascade.edn:84`. -/
def snatchPrecedenceBefore : List Nat := [5, 2, 0, 3, 6, 10, 20]

/-- Computed after precedence from `futon3:checks/find_organise.clj:617,629`
and the exchange-first row at `futon3:checks/snatch-cascade.edn:210-213`. -/
def snatchPrecedenceAfter : List Nat := [20, 5, 2, 0, 3, 6, 10]

/-- Computed before acting order from `futon3:checks/find_organise.clj:616,630`
and `futon3:checks/snatch-cascade.edn:80-83`. -/
def snatchActingOrderBefore : List Nat := [10, 2, 0]

/-- Computed after acting order from `futon3:checks/find_organise.clj:617,631`
and `futon3:checks/snatch-cascade.edn:210`. -/
def snatchActingOrderAfter : List Nat := [20]

/-- Before score 3, from `futon3:checks/find_organise.clj:632` and
`futon3:checks/snatch-cascade.edn:84`. -/
def snatchScoreBefore : Int := 3

/-- After score -5, from `futon3:checks/find_organise.clj:633` and
`futon3:checks/snatch-cascade.edn:211`. -/
def snatchScoreAfter : Int := -5

/-- Ruled no-bootstrap carrier: O3 uses literally `nodes \ addedByOrganise`
for every input, not an equality special to the recorded arguments. -/
def organiseSnatch : RuledOrganiseType Unit Nat Int := fun _ sel repo adm =>
  { selected := sel
    nodes := sel ∪ snatchAdded ∪ adm
    addedByOrganise := snatchAdded
    admittedBy := adm
    authoredEdges := repo.standsOn
    organisedEdges := fastForward ((sel ∪ snatchAdded ∪ adm) \ snatchAdded) repo.standsOn
    precedenceBefore := snatchPrecedenceBefore
    precedenceAfter := snatchPrecedenceAfter
    actingOrderBefore := snatchActingOrderBefore
    actingOrderAfter := snatchActingOrderAfter
    scoreBefore := snatchScoreBefore
    scoreAfter := snatchScoreAfter }

/-- All seven ruled clauses hold. -/
theorem organiseSnatchConformant : ConformantOrganiseRuled organiseSnatch where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; rfl
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; rfl
  o4 := by intros; left; simp [organiseSnatch, snatchActingOrderBefore, snatchActingOrderAfter]

/-- The computed precedence changes. -/
theorem organiseSnatchPrecedenceMoves :
    (organiseSnatch trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted).precedenceBefore ≠
    (organiseSnatch trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted).precedenceAfter := by
  simp [organiseSnatch, snatchPrecedenceBefore, snatchPrecedenceAfter]

/-- Both O4 conclusions hold on this row. The live score arm contrasts with the
flat score in `organiseAntsActingMovesScoreFlat` and unavailable Unit score in
`miningScoreCannotMove`. -/
theorem organiseSnatchActingAndScoreMove :
    (organiseSnatch trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted).actingOrderBefore ≠
      (organiseSnatch trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted).actingOrderAfter ∧
    (organiseSnatch trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted).scoreBefore = 3 ∧
    (organiseSnatch trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted).scoreAfter = -5 ∧
    (organiseSnatch trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted).scoreBefore ≠
      (organiseSnatch trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted).scoreAfter := by
  simp [organiseSnatch, snatchActingOrderBefore, snatchActingOrderAfter,
    snatchScoreBefore, snatchScoreAfter]

/-- The retained direct edge makes O2/O3 non-vacuous. -/
theorem organiseSnatchEdge02 :
    (organiseSnatch trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted).organisedEdges 0 2 := by
  refine ⟨by simp [snatchSelected, snatchAdded, snatchAdmitted],
    by simp [snatchSelected, snatchAdded, snatchAdmitted], ReachOutside.direct ?_⟩
  simp [snatchRepo]

/-- The precedence change is a reordering. -/
theorem snatchPrecedencePerm : snatchPrecedenceBefore.Perm snatchPrecedenceAfter := by decide

/-- Unlike ants, the acting-order change is not a reordering. -/
theorem snatchActingOrderNotPerm :
    ¬ snatchActingOrderBefore.Perm snatchActingOrderAfter := by decide

/-- Full-node reading computed by `o3-fast-forward` at
`futon3:checks/find_organise.clj:525-529`. -/
def organiseSnatchRecordedEdges : RuledOrganiseType Unit Nat Int := fun _ sel repo adm =>
  { selected := sel
    nodes := sel ∪ snatchAdded ∪ adm
    addedByOrganise := snatchAdded
    admittedBy := adm
    authoredEdges := repo.standsOn
    organisedEdges := fastForward (sel ∪ snatchAdded ∪ adm) repo.standsOn
    precedenceBefore := snatchPrecedenceBefore, precedenceAfter := snatchPrecedenceAfter
    actingOrderBefore := snatchActingOrderBefore, actingOrderAfter := snatchActingOrderAfter
    scoreBefore := snatchScoreBefore, scoreAfter := snatchScoreAfter }

/-- Every ruled clause except no-bootstrap O3 holds for the recorded-edge reading. -/
theorem organiseSnatchRecordedEdgesSansO3 :
    ConformantOrganiseRuledSansO3 organiseSnatchRecordedEdges where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; rfl
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o4 := by intros; left
           simp [organiseSnatchRecordedEdges, snatchActingOrderBefore, snatchActingOrderAfter]

/-- The full-node reading carries recorded edge 18→22. -/
theorem organiseSnatchRecordedEdge1822 :
    (organiseSnatchRecordedEdges trivialPolicyCascade snatchSelected snatchRepo
      snatchAdmitted).organisedEdges 18 22 := by
  refine ⟨by simp [snatchSelected, snatchAdded], by simp [snatchSelected, snatchAdded],
    ReachOutside.direct ?_⟩
  simp [snatchRepo]

/-- The ruled subtraction refuses recorded edge 18→22. Together with the next
theorem this witnesses the real-record shape of synthetic
`organiseRuledOwnBootstrap`: the ruled O3 keeps only one of ten computed edges,
so it cannot reproduce that edge set. -/
theorem organiseSnatchNotEdge1822 :
    ¬ (organiseSnatch trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted).organisedEdges
      18 22 := by
  intro h
  exact h.1.2 (by simp [snatchAdded])

/-- The ruled subtraction also refuses computed edge 10→18; nine of ten
computed edges are refused, without taking a position on which reading is right. -/
theorem organiseSnatchNotEdge1018 :
    ¬ (organiseSnatch trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted).organisedEdges
      10 18 := by
  intro h
  exact h.2.1.2 (by simp [snatchAdded])

/-- Recorded-edge reading fails ruled O3 specifically at 18→22. -/
theorem organiseSnatchRecordedEdgesNotConformant :
    ¬ ConformantOrganiseRuled organiseSnatchRecordedEdges := by
  intro h
  have := (h.o3 trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted 18 22).mp
    organiseSnatchRecordedEdge1822
  exact organiseSnatchNotEdge1822 (by
    simpa [organiseSnatch, organiseSnatchRecordedEdges] using this)

/-- Acting order flattened while score still moves: O4's right disjunct suffices. -/
def organiseSnatchActingFlat : RuledOrganiseType Unit Nat Int := fun t sel repo adm =>
  { organiseSnatch t sel repo adm with actingOrderAfter := snatchActingOrderBefore }

/-- The score arm alone makes the acting-flat carrier fully conformant. -/
theorem organiseSnatchActingFlatConformant :
    ConformantOrganiseRuled organiseSnatchActingFlat where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; rfl
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; rfl
  o4 := by intros; right
           simp [organiseSnatchActingFlat, organiseSnatch, snatchScoreBefore, snatchScoreAfter]

/-- Acting order and score both flattened while precedence still moves. -/
def organiseSnatchActingFlatScoreFlat : RuledOrganiseType Unit Nat Int :=
  fun t sel repo adm =>
    { organiseSnatchActingFlat t sel repo adm with scoreAfter := snatchScoreBefore }

/-- Every clause except O4 holds for the doubly-flat control. -/
theorem organiseSnatchActingFlatScoreFlatSansO4 :
    ConformantOrganiseRuledSansO4 organiseSnatchActingFlatScoreFlat where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; rfl
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; rfl

/-- The doubly-flat control fails O4 alone. -/
theorem organiseSnatchActingFlatScoreFlatNotConformant :
    ¬ ConformantOrganiseRuled organiseSnatchActingFlatScoreFlat := by
  intro h
  have := h.o4 trivialPolicyCascade snatchSelected snatchRepo snatchAdmitted
    organiseSnatchPrecedenceMoves
  simp [organiseSnatchActingFlatScoreFlat, organiseSnatchActingFlat, organiseSnatch] at this

#print axioms snatchSelected
#print axioms snatchAdded
#print axioms snatchAdmitted
#print axioms snatchRepo
#print axioms snatchPrecedenceBefore
#print axioms snatchPrecedenceAfter
#print axioms snatchActingOrderBefore
#print axioms snatchActingOrderAfter
#print axioms snatchScoreBefore
#print axioms snatchScoreAfter
#print axioms organiseSnatch
#print axioms organiseSnatchConformant
#print axioms organiseSnatchPrecedenceMoves
#print axioms organiseSnatchActingAndScoreMove
#print axioms organiseSnatchEdge02
#print axioms snatchPrecedencePerm
#print axioms snatchActingOrderNotPerm
#print axioms organiseSnatchRecordedEdges
#print axioms organiseSnatchRecordedEdgesSansO3
#print axioms organiseSnatchRecordedEdge1822
#print axioms organiseSnatchNotEdge1822
#print axioms organiseSnatchNotEdge1018
#print axioms organiseSnatchRecordedEdgesNotConformant
#print axioms organiseSnatchActingFlat
#print axioms organiseSnatchActingFlatConformant
#print axioms organiseSnatchActingFlatScoreFlat
#print axioms organiseSnatchActingFlatScoreFlatSansO4
#print axioms organiseSnatchActingFlatScoreFlatNotConformant

end
end DarkTower.WarMachine.Holes
