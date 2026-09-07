import DarkTower.WarMachine.F12RuledCarrier

/-! # F12 mining exemplar

Index map from `futon2:holes/labs/library-loop/runs/mining-exemplar/cascade.edn:13-25`:
`0` hierarchical-and-temporal-depth; `1` candidate-pattern-action-space; `2`
expected-free-energy-scorecard.

The repository relation transcribes the record-declared edges. Their authorship
is mission-attested at
`futon2:holes/missions/M-wm-aif-policy-grain-compliance.md:34-44` and
`futon2:holes/missions/M-wm-aif-policy-grain-compliance.md:119-132`, not a
futon3 library `@why`/`@how` relation. At the pinned futon3 commit
`cdb5e8a56fd907beb6a99f8b88af9de50ff93126`, no such library edge joins these
three pattern IDs to one another.
-/

open Set
namespace DarkTower.WarMachine.Holes
noncomputable section

/-- The three selected nodes from
`futon2:holes/labs/library-loop/runs/mining-exemplar/cascade.edn:26-29`. -/
def miningSelected : Set Nat := {0, 1, 2}

/-- The empty admission set from
`futon2:holes/labs/library-loop/runs/mining-exemplar/cascade.edn:30-32`; the
note says classifying an unrecorded admission would invent evidence.  So arm
four's attribution input is instantiated EMPTY here and this exemplar witnesses
nothing about it; the nine recorded admissions of `organiseRuledZaifAdmitted`
(`DarkTower/WarMachine/F12RuledCarrier.lean:90`) remain that ruling's only
non-trivial instance. -/
def miningAdmitted : Set Nat := ∅

/-- The two mission-attested edges from
`futon2:holes/labs/library-loop/runs/mining-exemplar/cascade.edn:34-43`. -/
def miningRepo : Repository Nat where
  patterns := {0, 1, 2}
  standsOn := fun u v => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  acyclic := acyclic_of_increasing_rank _ id (by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)

/-- The sole recorded precedence map, transcribed as its `[0,1,2]` order, from
`futon2:holes/labs/library-loop/runs/mining-exemplar/cascade.edn:66-69`. -/
def miningPrecedence : List Nat := [0, 1, 2]

/-- The sole recorded acting order from
`futon2:holes/labs/library-loop/runs/mining-exemplar/cascade.edn:72-75`, inside
the `:o4` block at
`futon2:holes/labs/library-loop/runs/mining-exemplar/cascade.edn:70-76` whose
only other members are `:rule-bearing-members` and `:basis`. -/
def miningActingOrder : List Nat := [0, 1, 2]

/-- Ruled mining carrier. `Score := Unit` because the record contains no score.
The record supplies one precedence and one acting order, not before/after pairs;
both sides are therefore instantiated with the recorded order. Thus O4's
antecedent is false by this transcription choice, not by a recorded measurement. -/
def organiseMining : RuledOrganiseType Unit Nat Unit := fun _ sel repo adm =>
  { selected := sel, nodes := sel ∪ adm, addedByOrganise := ∅, admittedBy := adm
    authoredEdges := repo.standsOn
    organisedEdges := fastForward (sel ∪ adm) repo.standsOn
    precedenceBefore := miningPrecedence, precedenceAfter := miningPrecedence
    actingOrderBefore := miningActingOrder, actingOrderAfter := miningActingOrder
    scoreBefore := (), scoreAfter := () }

/-- The record's silence about a score is carried into the TYPE: at
`Score := Unit`, O4's score-change disjunct is unavailable to every function of
this instantiation, `organiseMining` included, so acting order is the only way
through O4 here.  Stated of an arbitrary `f` rather than of `organiseMining`'s
own `()` literals, which would be a fact about the transcription. -/
theorem miningScoreCannotMove (f : RuledOrganiseType Unit Nat Unit)
    (t : Cascade Unit) (sel : Set Nat) (repo : Repository Nat) (adm : Set Nat) :
    ¬ ((f t sel repo adm).scoreBefore ≠ (f t sel repo adm).scoreAfter) := by
  intro h; exact h (Subsingleton.elim _ _)

/-- All seven ruled clauses hold for the mining transcription. -/
theorem organiseMiningConformant : ConformantOrganiseRuled organiseMining where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; simp [organiseMining]
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; simp [organiseMining]
  o4 := by intros; contradiction

/-- The record's first direct edge exercises O2 and O3 with a true antecedent. -/
theorem organiseMiningEdge01 :
    (organiseMining trivialPolicyCascade miningSelected miningRepo miningAdmitted).organisedEdges
      0 1 := by
  exact ⟨by simp [miningSelected], by simp [miningSelected],
    ReachOutside.direct (by simp [miningRepo])⟩

/-- The record's second direct edge exercises O2 and O3 with a true antecedent. -/
theorem organiseMiningEdge12 :
    (organiseMining trivialPolicyCascade miningSelected miningRepo miningAdmitted).organisedEdges
      1 2 := by
  exact ⟨by simp [miningSelected], by simp [miningSelected],
    ReachOutside.direct (by simp [miningRepo])⟩

/-- Fast-forward excludes `0 → 2`: its only two-edge route uses member `1` as
an intermediate vertex, while `ReachOutside` requires intermediates outside the
member set. -/
theorem organiseMiningNotEdge02 :
    ¬ (organiseMining trivialPolicyCascade miningSelected miningRepo miningAdmitted).organisedEdges
      0 2 := by
  intro h
  rcases h with ⟨_, _, hr⟩
  change ReachOutside (miningSelected ∪ miningAdmitted) miningRepo.standsOn 0 2 at hr
  cases hr with
  | direct edge => simp [miningRepo] at edge
  | through path hout edge =>
      simp [miningRepo] at edge
      rcases edge with ⟨rfl, rfl⟩
      exact hout (by simp [miningSelected, miningAdmitted])

/-- O2 is non-vacuous here, unlike `organiseAntsNoOrganisedEdges` at
`DarkTower/WarMachine/F12AntsExemplar.lean:73`. -/
theorem organiseMiningHasOrganisedEdge :
    ∃ u v, (organiseMining trivialPolicyCascade miningSelected miningRepo miningAdmitted).organisedEdges
      u v := ⟨0, 1, organiseMiningEdge01⟩

/-- Negative control using full reachability instead of ruled fast-forward. -/
def organiseMiningTransitiveClosure : RuledOrganiseType Unit Nat Unit := fun _ sel repo adm =>
  { selected := sel, nodes := sel ∪ adm, addedByOrganise := ∅, admittedBy := adm
    authoredEdges := repo.standsOn
    organisedEdges := fun u v => u ∈ sel ∪ adm ∧ v ∈ sel ∪ adm ∧ Reach repo.standsOn u v
    precedenceBefore := miningPrecedence, precedenceAfter := miningPrecedence
    actingOrderBefore := miningActingOrder, actingOrderAfter := miningActingOrder
    scoreBefore := (), scoreAfter := () }

/-- Every ruled clause except O3 holds for the transitive-closure control. -/
theorem organiseMiningTransitiveClosureSansO3 :
    ConformantOrganiseRuledSansO3 organiseMiningTransitiveClosure where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; simp [organiseMiningTransitiveClosure]
  o2 := by intro _ _ _ _ _ _ h; exact h.2.2
  o4 := by intros; contradiction

/-- The transitive-closure control fails O3 at the recorded two-edge path
`0 → 1 → 2`, precisely where ruled fast-forward excludes it. -/
theorem organiseMiningTransitiveClosureNotConformant :
    ¬ ConformantOrganiseRuled organiseMiningTransitiveClosure := by
  intro h
  have ho3 := h.o3 trivialPolicyCascade miningSelected miningRepo miningAdmitted 0 2
  have hedge : (organiseMiningTransitiveClosure trivialPolicyCascade miningSelected
      miningRepo miningAdmitted).organisedEdges 0 2 := by
    refine ⟨by simp [miningSelected], by simp [miningSelected], ?_⟩
    exact Reach.tail (b := 1) (Reach.single (by simp [miningRepo])) (by simp [miningRepo])
  exact organiseMiningNotEdge02 (by
    simpa [organiseMining, organiseMiningTransitiveClosure] using ho3.mp hedge)

/-- Negative control inventing `2 → 1`. It necessarily also breaks O3 because
O3 is an iff fixing `organisedEdges` to fast-forward, so this cannot isolate O2. -/
def organiseMiningInventedEdge : RuledOrganiseType Unit Nat Unit := fun _ sel repo adm =>
  { selected := sel, nodes := sel ∪ adm, addedByOrganise := ∅, admittedBy := adm
    authoredEdges := repo.standsOn
    organisedEdges := fun u v => fastForward (sel ∪ adm) repo.standsOn u v ∨ (u = 2 ∧ v = 1)
    precedenceBefore := miningPrecedence, precedenceAfter := miningPrecedence
    actingOrderBefore := miningActingOrder, actingOrderAfter := miningActingOrder
    scoreBefore := (), scoreAfter := () }

/-- The invented edge `2 → 1` fails O2 because the authored relation only
moves along the increasing chain `0 → 1 → 2`. -/
theorem organiseMiningInventedEdgeFailsO2 :
    ¬ Reach miningRepo.standsOn 2 1 := by
  intro h
  have : 2 < 1 := reach_increases_rank miningRepo.standsOn id (by
    intro u v hedge
    simp [miningRepo] at hedge
    rcases hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) h
  omega

/-- Consequently the invented-edge control is not ruled-conformant. -/
theorem organiseMiningInventedEdgeNotConformant :
    ¬ ConformantOrganiseRuled organiseMiningInventedEdge := by
  intro h
  apply organiseMiningInventedEdgeFailsO2
  apply h.o2 trivialPolicyCascade miningSelected miningRepo miningAdmitted 2 1
  simp [organiseMiningInventedEdge]

/-- Negative control, and the answer to what the unexercised O4 clause is still
doing here: a function that moves the precedence this record does not, with the
acting order left flat.  The record supplies no before/after pair, so O4's
antecedent is false at `organiseMining` by transcription; the clause nevertheless
refuses this neighbour of it. -/
def organiseMiningPrecedenceMoves : RuledOrganiseType Unit Nat Unit := fun t sel repo adm =>
  { organiseMining t sel repo adm with precedenceAfter := [0, 2, 1] }

/-- Every ruled clause except O4 holds of the moving-precedence control, so its
refutation below is located at O4 alone. -/
theorem organiseMiningPrecedenceMovesSansO4 :
    ConformantOrganiseRuledSansO4 organiseMiningPrecedenceMoves where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; simp [organiseMiningPrecedenceMoves, organiseMining]
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; simp [organiseMiningPrecedenceMoves, organiseMining]

/-- The moving-precedence control fails exactly O4: its acting order is flat and
`miningScoreCannotMove` closes the other disjunct. -/
theorem organiseMiningPrecedenceMovesNotConformant :
    ¬ ConformantOrganiseRuled organiseMiningPrecedenceMoves := by
  intro h
  have hmove := h.o4 trivialPolicyCascade miningSelected miningRepo miningAdmitted
    (by simp [organiseMiningPrecedenceMoves, organiseMining, miningPrecedence])
  rcases hmove with hact | hscore
  · exact hact (by simp [organiseMiningPrecedenceMoves, organiseMining])
  · exact miningScoreCannotMove organiseMiningPrecedenceMoves trivialPolicyCascade
      miningSelected miningRepo miningAdmitted hscore

#print axioms miningSelected
#print axioms miningAdmitted
#print axioms miningRepo
#print axioms miningPrecedence
#print axioms miningActingOrder
#print axioms organiseMining
#print axioms miningScoreCannotMove
#print axioms organiseMiningConformant
#print axioms organiseMiningEdge01
#print axioms organiseMiningEdge12
#print axioms organiseMiningNotEdge02
#print axioms organiseMiningHasOrganisedEdge
#print axioms organiseMiningTransitiveClosure
#print axioms organiseMiningTransitiveClosureSansO3
#print axioms organiseMiningTransitiveClosureNotConformant
#print axioms organiseMiningInventedEdge
#print axioms organiseMiningInventedEdgeFailsO2
#print axioms organiseMiningInventedEdgeNotConformant
#print axioms organiseMiningPrecedenceMoves
#print axioms organiseMiningPrecedenceMovesSansO4
#print axioms organiseMiningPrecedenceMovesNotConformant

end
end DarkTower.WarMachine.Holes
