import DarkTower.WarMachine.F12SupportArm

/-! # F12 O3 no-bootstrap field arm

This module runs the third reading of O3, in which fast-forward endpoints must
come from outside `organise`. It records comparisons without choosing a reading.
-/

open Set

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- F12 slice 11 R1: `ConformantOrganiseNodes` at `F12Conformance.lean:31` with O3 restricted to returned nodes not attributed to organise. -/
structure ConformantOrganiseNoBootstrap {Policy P : Type*}
    (f : OrganiseType Policy P) : Prop where
  o1 : ∀ t sel repo, (f t sel repo).nodes = sel ∪ (f t sel repo).addedByOrganise
  o2 : ∀ t sel repo u v, (f t sel repo).edges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo u v, (f t sel repo).edges u v ↔
    fastForward ((f t sel repo).nodes \ (f t sel repo).addedByOrganise)
      repo.standsOn u v

/-- F12 slice 11 R2: the C59 value fixture at `Holes.lean:872` records no organise-added nodes. -/
theorem c59AddedByOrganiseEmpty : wmCascadeDiffFixture.addedByOrganise = ∅ := rfl

/-- F12 slice 11 R2: removing the empty organise-added field from the C59 nodes changes nothing. -/
theorem c59NodesDiffAdded_eq_nodes :
    wmCascadeDiffFixture.nodes \ wmCascadeDiffFixture.addedByOrganise =
      wmCascadeDiffFixture.nodes := by simp [c59AddedByOrganiseEmpty]

/-- F12 slice 11 R2: the C59 external-origin union is its node set because both origin fields coincide as recorded at `Holes.lean:872-884`. -/
theorem c59SelectedUnionAdmitted_eq_nodes :
    wmCascadeDiffFixture.selected ∪ wmCascadeDiffFixture.admittedBy =
      wmCascadeDiffFixture.nodes := by ext n; simp [wmCascadeDiffFixture]

/-- F12 slice 11 R2: the zaif value fixture at `Holes.lean:974` records no organise-added nodes. -/
theorem zaifAddedByOrganiseEmpty : wmZaifCascadeDiffFixture.addedByOrganise = ∅ := rfl

/-- F12 slice 11 R2: removing the empty organise-added field from zaif nodes changes nothing. -/
theorem zaifNodesDiffAdded_eq_nodes :
    wmZaifCascadeDiffFixture.nodes \ wmZaifCascadeDiffFixture.addedByOrganise =
      wmZaifCascadeDiffFixture.nodes := by simp [zaifAddedByOrganiseEmpty]

/-- F12 slice 11 R2: the eleven selected and nine admitted vertices are exactly the zaif nodes recorded at `Holes.lean:957-984`. -/
theorem zaifSelectedUnionAdmitted_eq_nodes :
    wmZaifCascadeDiffFixture.selected ∪ wmZaifCascadeDiffFixture.admittedBy =
      wmZaifCascadeDiffFixture.nodes := by
  simpa [zaifAddedByOrganiseEmpty] using organiseO1NodesRecordedZaif.symm

/-- F12 slice 11 R2: `organiseO3FastForwardZaif` at `Holes.lean:1014` is also the no-bootstrap O3 because `addedByOrganise` is empty. -/
theorem organiseO3NoBootstrapZaif : ∀ u v,
    wmZaifCascadeDiffFixture.organisedEdges u v ↔
      fastForward
        (wmZaifCascadeDiffFixture.nodes \ wmZaifCascadeDiffFixture.addedByOrganise)
        wmZaifCascadeDiffFixture.authoredEdges u v := by
  intro u v
  rw [zaifNodesDiffAdded_eq_nodes]
  exact organiseO3FastForwardZaif u v

/-- F12 slice 11 R3: node-closure implementation matching `organiseUpClosure` at `F12Conformance.lean:77`, but O3 builds edges over its returned nodes. -/
def organiseNodeClosureEdges {Policy P : Type*} : OrganiseType Policy P :=
  fun _ sel repo =>
    let nodes := sel ∪ {p | ∃ s ∈ sel, Reach repo.standsOn s p}
    { nodes := nodes
      addedByOrganise := {p | p ∉ sel ∧ ∃ s ∈ sel, Reach repo.standsOn s p}
      edges := fastForward nodes repo.standsOn
      acyclic := fastForward_acyclic nodes repo.standsOn repo.acyclic
      precedence := [] }

/-- F12 slice 11 R3(a): the node-closure implementation satisfies the node-set reading from `F12Conformance.lean:31`. -/
theorem organiseNodeClosureEdgesConformantNodes {Policy P : Type*} :
    ConformantOrganiseNodes (organiseNodeClosureEdges (Policy := Policy) (P := P)) where
  o1 := by intro t sel repo; ext p; simp [organiseNodeClosureEdges]; tauto
  o2 := by
    intro t sel repo u v hedge
    exact d1_reachOutside_to_reach hedge.2.2
  o3 := by intros; rfl

/-- F12 slice 11 R3: outside the node-closure implementation's organise-added field, precisely the input selection remains. -/
theorem organiseNodeClosureEdgesOutside_eq_selected {Policy P : Type*}
    (t : Cascade Policy) (sel : Set P) (repo : Repository P) :
    (organiseNodeClosureEdges t sel repo).nodes \
        (organiseNodeClosureEdges t sel repo).addedByOrganise = sel := by
  ext p
  simp [organiseNodeClosureEdges]
  tauto

/-- F12 slice 11 R3(c): recorded vertices 26 and 25 are both organise-added by node closure (`F12D1Arms.lean:26-30`). -/
theorem nodeClosureAddsTwentySixAndTwentyFive :
    (26 : Nat) ∈ (organiseNodeClosureEdges trivialPolicyCascade d1Selected d1Repo).addedByOrganise ∧
    (25 : Nat) ∈ (organiseNodeClosureEdges trivialPolicyCascade d1Selected d1Repo).addedByOrganise := by
  constructor
  · exact ⟨by simp [d1Selected], 6, by simp [d1Selected], Reach.single (by trivial)⟩
  · exact ⟨by simp [d1Selected], 6, by simp [d1Selected],
      Reach.tail
        (Reach.single (show d1Repo.standsOn 6 26 by trivial))
        (show d1Repo.standsOn 26 25 by trivial)⟩

/-- F12 slice 11 R3(c): the node-set reading creates the explicit organised edge `26 → 25` from the authored edge at `F12D1Arms.lean:26-30`. -/
theorem nodeClosureNodeReadingEdgeTwentySixTwentyFive :
    (organiseNodeClosureEdges trivialPolicyCascade d1Selected d1Repo).edges 26 25 := by
  refine ⟨?_, ?_, ReachOutside.direct (by trivial)⟩
  · exact Or.inr (nodeClosureAddsTwentySixAndTwentyFive).1.2
  · exact Or.inr (nodeClosureAddsTwentySixAndTwentyFive).2.2

/-- F12 slice 11 R3(c): the same `26 → 25` edge cannot be a no-bootstrap fast-forward because vertex 26 was organise-added. -/
theorem nodeClosureNoBootstrapRejectsTwentySixTwentyFive :
    ¬ fastForward
      ((organiseNodeClosureEdges trivialPolicyCascade d1Selected d1Repo).nodes \
        (organiseNodeClosureEdges trivialPolicyCascade d1Selected d1Repo).addedByOrganise)
      d1Repo.standsOn 26 25 := by
  rw [organiseNodeClosureEdgesOutside_eq_selected]
  intro hedge
  have h26 := hedge.1
  simp [d1Selected] at h26

/-- F12 slice 11 R3(b): the explicit `26 → 25` edge separates node-set conformance from no-bootstrap conformance on recorded inputs. -/
theorem organiseNodeClosureEdgesNotConformantNoBootstrap :
    ¬ ConformantOrganiseNoBootstrap
      (organiseNodeClosureEdges (Policy := Unit) (P := Nat)) := by
  intro hf
  exact nodeClosureNoBootstrapRejectsTwentySixTwentyFive
    ((hf.o3 trivialPolicyCascade d1Selected d1Repo 26 25).mp
      nodeClosureNodeReadingEdgeTwentySixTwentyFive)

/-- F12 slice 11 R4 recorded measurement: the no-bootstrap endpoint field is `d1Selected`, and its fast-forward relation is empty because authored rank strictly increases from rank-zero selected vertices. -/
theorem recordedNoBootstrapFastForwardEmpty : ∀ u v,
    ¬ fastForward
      ((organiseNodeClosureEdges trivialPolicyCascade d1Selected d1Repo).nodes \
        (organiseNodeClosureEdges trivialPolicyCascade d1Selected d1Repo).addedByOrganise)
      d1Repo.standsOn u v := by
  intro u v hedge
  rw [organiseNodeClosureEdgesOutside_eq_selected] at hedge
  have hrank := reach_increases_rank d1Authored d1Rank d1_authored_increases_rank
    (d1_reachOutside_to_reach hedge.2.2)
  have hu : u < 11 := hedge.1
  have hv : v < 11 := hedge.2.1
  have hu0 : d1Rank u = 0 := by interval_cases u <;> rfl
  have hv0 : d1Rank v = 0 := by interval_cases v <;> rfl
  rw [hu0, hv0] at hrank
  omega

/-- F12 slice 11 R4 constructed implementation: selected-only already satisfies no-bootstrap O3 because its organise-added field is empty (`F12Conformance.lean:59-70`). -/
theorem organiseSelectedOnlyConformantNoBootstrap {Policy P : Type*} :
    ConformantOrganiseNoBootstrap
      (organiseSelectedOnly (Policy := Policy) (P := P)) where
  o1 := by intros; simp [organiseSelectedOnly]
  o2 := by
    intro t sel repo u v hedge
    exact d1_reachOutside_to_reach hedge.2.2
  o3 := by intros; simp [organiseSelectedOnly]

/-- F12 slice 11 R4 constructed non-vacuity: when all twenty vertices are supplied externally, a no-bootstrap-conformant implementation has edge `18 → 19`. -/
theorem noBootstrapConstructedEdge :
    (organiseSelectedOnly (Policy := Unit) trivialPolicyCascade d1Nodes d1Repo).edges 18 19 :=
  selectedOnlyYieldsZaifEdgeWhenAdmittedSupplied

/-- F12 slice 11 R5: no no-bootstrap-conformant function can return the recorded admitted-endpoint edge on the eleven-node selected input. -/
theorem noBootstrapCannotYieldZaifEdge {Policy : Type*}
    (f : OrganiseType Policy Nat) (hf : ConformantOrganiseNoBootstrap f)
    (t : Cascade Policy) : ¬ (f t d1Selected d1Repo).edges 18 19 := by
  intro hedge
  have h18 := ((hf.o3 t d1Selected d1Repo 18 19).mp hedge).1
  rcases (show (18 : Nat) ∈ d1Selected ∪ (f t d1Selected d1Repo).addedByOrganise by
    rw [← hf.o1]; exact h18.1) with hsel | hadd
  · simp [d1Selected] at hsel
  · exact h18.2 hadd

/-- F12 slice 11 R5: supplying all twenty recorded nodes externally makes the same no-bootstrap-conformant selected-only implementation return edge `18 → 19`. -/
theorem noBootstrapYieldsZaifEdgeWhenAllNodesSupplied :
    (organiseSelectedOnly (Policy := Unit) trivialPolicyCascade d1Nodes d1Repo).edges 18 19 :=
  noBootstrapConstructedEdge

end

end DarkTower.WarMachine.Holes
