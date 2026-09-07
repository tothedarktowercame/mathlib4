import DarkTower.WarMachine.F12D1Arms

/-! # F12 organise-function conformance

This module states O1--O3 of an organise function applied to its inputs.  O1
is necessarily the two-way union because `Cascade` (`Holes.lean:29-35`) has no
`admittedBy` field.  O4 is deliberately not stated: that carrier has one
`precedence`, no acting order, and no score, while its input cascade carries a
list of the distinct `Policy` type.
-/

open Set

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- F12 slice 6 signature, identical to `organise` at `Holes.lean:861`. -/
abbrev OrganiseType (Policy P : Type*) :=
  Cascade Policy → Set P → Repository P → Cascade P

/-- F12 slice 6 O1--O3 conformance using the `.selected` reading of O3 from `Holes.lean:909`; O1 is the two-way union because this signature has no `admittedBy` carrier. -/
structure ConformantOrganiseSelected {Policy P : Type*}
    (f : OrganiseType Policy P) : Prop where
  o1 : ∀ t sel repo, (f t sel repo).nodes = sel ∪ (f t sel repo).addedByOrganise
  o2 : ∀ t sel repo u v, (f t sel repo).edges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo u v,
    (f t sel repo).edges u v ↔ fastForward sel repo.standsOn u v

/-- F12 slice 6 O1--O3 conformance using the node-set reading of O3 from `find_organise.clj:529` and `construct_cascade.clj:415`; O1 remains the two-way union because this signature has no `admittedBy` carrier. -/
structure ConformantOrganiseNodes {Policy P : Type*}
    (f : OrganiseType Policy P) : Prop where
  o1 : ∀ t sel repo, (f t sel repo).nodes = sel ∪ (f t sel repo).addedByOrganise
  o2 : ∀ t sel repo u v, (f t sel repo).edges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo u v,
    (f t sel repo).edges u v ↔ fastForward (f t sel repo).nodes repo.standsOn u v

/-- F12 slice 6 reach composition for `Reach` at `CascadeOrder.lean:17-19`. -/
theorem reach_trans {P : Type*} {r : P → P → Prop} {a b c : P} :
    Reach r a b → Reach r b c → Reach r a c := by
  intro hab hbc
  induction hbc with
  | single edge => exact Reach.tail hab edge
  | tail _ edge ih => exact Reach.tail ih edge

/-- F12 slice 6 acyclicity transport: `fastForward` at `Holes.lean:829-831` cannot create a cycle over an acyclic authored relation. -/
theorem fastForward_acyclic {P : Type*} (sel : Set P) (r : P → P → Prop)
    (h : acyclicDescent r) : acyclicDescent (fastForward sel r) := by
  have convert {a b : P} : Reach (fastForward sel r) a b → Reach r a b := by
    intro path
    induction path with
    | single edge => exact d1_reachOutside_to_reach edge.2.2
    | tail _ edge ih =>
        exact reach_trans ih (d1_reachOutside_to_reach edge.2.2)
  intro x cycle
  exact h x (convert cycle)

/-- F12 slice 6 selected-only implementation named by the `Holes.lean:861` type-amendment note. -/
def organiseSelectedOnly {Policy P : Type*} : OrganiseType Policy P :=
  fun _ sel repo =>
    { nodes := sel
      addedByOrganise := ∅
      edges := fastForward sel repo.standsOn
      acyclic := fastForward_acyclic sel repo.standsOn repo.acyclic
      precedence := [] }

/-- F12 slice 6 O1--O3 proof for `organiseSelectedOnly`, under the selected reading. -/
theorem organiseSelectedOnlyConformant {Policy P : Type*} :
    ConformantOrganiseSelected (organiseSelectedOnly (Policy := Policy) (P := P)) where
  o1 := by intro t sel repo; ext x; simp [organiseSelectedOnly]
  o2 := by
    intro t sel repo u v edge
    exact d1_reachOutside_to_reach edge.2.2
  o3 := by intro t sel repo u v; rfl

/-- F12 slice 6 up-closure implementation named by the `Holes.lean:861` type-amendment note. -/
def organiseUpClosure {Policy P : Type*} : OrganiseType Policy P :=
  fun _ sel repo =>
    { nodes := sel ∪ {p | ∃ s ∈ sel, Reach repo.standsOn s p}
      addedByOrganise := {p | p ∉ sel ∧ ∃ s ∈ sel, Reach repo.standsOn s p}
      edges := fastForward sel repo.standsOn
      acyclic := fastForward_acyclic sel repo.standsOn repo.acyclic
      precedence := [] }

/-- F12 slice 6 O1--O3 proof for `organiseUpClosure`, under the selected reading. -/
theorem organiseUpClosureConformant {Policy P : Type*} :
    ConformantOrganiseSelected (organiseUpClosure (Policy := Policy) (P := P)) where
  o1 := by
    intro t sel repo
    ext x
    simp only [organiseUpClosure, mem_union, mem_setOf_eq]
    tauto
  o2 := by
    intro t sel repo u v edge
    exact d1_reachOutside_to_reach edge.2.2
  o3 := by intro t sel repo u v; rfl

/-- F12 slice 6 policy input used to execute both function witnesses on the zaif data. -/
def trivialPolicyCascade : Cascade Unit where
  nodes := ∅
  addedByOrganise := ∅
  edges := fun _ _ => False
  acyclic := by intro x path; cases path with | single h => exact h | tail p h => exact h
  precedence := []

/-- F12 slice 6 swappability witness: both selected-conformant functions return different node sets on the recorded zaif inputs. -/
theorem organiseWitnessesDifferOnZaif :
    (organiseSelectedOnly (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).nodes ≠
      (organiseUpClosure (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).nodes := by
  intro h
  have h26 := Set.ext_iff.mp h 26
  simp [organiseSelectedOnly, organiseUpClosure, d1Selected, d1Repo] at h26
  exact h26 6 (by omega) (Reach.single (by trivial))

/-- F12 slice 6 O1 non-vacuity: the up-closure witness adds recorded vertex 26 through authored edge `6 → 26`. -/
theorem organiseUpClosureAddsSomething :
    (26 : Nat) ∈
      (organiseUpClosure (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).addedByOrganise := by
  refine ⟨by simp [d1Selected], 6, by simp [d1Selected], Reach.single ?_⟩
  trivial

/-- F12 slice 6 admitted-origin measurement: under two-way O1, every recorded admitted node is necessarily attributed to `addedByOrganise`. -/
theorem admittedIndistinguishableFromAdded {Policy : Type*}
    (f : OrganiseType Policy Nat) (hf : ConformantOrganiseSelected f)
    (t : Cascade Policy)
    (hnodes : (f t d1Selected d1Repo).nodes = d1Nodes) :
    d1Admitted ⊆ (f t d1Selected d1Repo).addedByOrganise := by
  intro x hx
  have ho1 := hf.o1 t d1Selected d1Repo
  rw [hnodes] at ho1
  have hxnodes : x ∈ d1Nodes := by
    simp [d1Admitted, d1Nodes] at hx ⊢
    omega
  rw [ho1] at hxnodes
  rcases hxnodes with hxsel | hxadded
  · simp [d1Admitted, d1Selected] at hx hxsel
    omega
  · exact hxadded

/-- F12 slice 6 selected-reading measurement: O3 over the eleven selected nodes cannot yield the recorded admitted-endpoint edge `18 → 19`. -/
theorem selectedReadingCannotYieldZaifEdge {Policy : Type*}
    (f : OrganiseType Policy Nat) (hf : ConformantOrganiseSelected f)
    (t : Cascade Policy) : ¬ ((f t d1Selected d1Repo).edges 18 19) := by
  intro edge
  have selected18 := (hf.o3 t d1Selected d1Repo 18 19).mp edge |>.1
  simp [d1Selected] at selected18

/-- F12 slice 6 missing-origin check: selected-only does yield the recorded `18 → 19` edge when all twenty nodes are supplied as input. -/
theorem selectedOnlyYieldsZaifEdgeWhenAdmittedSupplied :
    (organiseSelectedOnly (Policy := Unit) trivialPolicyCascade d1Nodes d1Repo).edges 18 19 := by
  exact armThreeOrganisedEdgeExists

/-- F12 slice 6 review addition: `organiseSelectedOnly` also satisfies the
node-set reading, because it returns `nodes = sel` and the two readings of O3
are then the same proposition — the same coincidence that made the C59 fixture
unable to tell them apart (`Holes.lean:1018-1034`). -/
theorem organiseSelectedOnlyConformantNodes {Policy P : Type*} :
    ConformantOrganiseNodes (organiseSelectedOnly (Policy := Policy) (P := P)) where
  o1 := by intro t sel repo; ext x; simp [organiseSelectedOnly]
  o2 := by
    intro t sel repo u v edge
    exact d1_reachOutside_to_reach edge.2.2
  o3 := by intro t sel repo u v; rfl

/-- F12 slice 6 review addition: the two readings of O3 are NOT interchangeable
at the implementation, and this is what separates them.  `organiseUpClosure`
satisfies the selected reading (`organiseUpClosureConformant`) and refutes the
node-set reading on the recorded zaif inputs: authored edge `6 → 26` runs
between two vertices of its returned node set, so the node-set reading demands
it as an organised edge, while its edge relation is fast-forward over the
eleven selected and has no such edge.  Slice 2 exhibited this disagreement
between two READINGS of one recorded cascade (`Holes.lean:1034`); here it
separates two implementations at the interface. -/
theorem organiseUpClosureNotConformantNodes :
    ¬ ConformantOrganiseNodes (organiseUpClosure (Policy := Unit) (P := Nat)) := by
  intro hf
  have h6 : (6 : Nat) ∈
      (organiseUpClosure (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).nodes :=
    Or.inl (by simp [d1Selected])
  have h26 : (26 : Nat) ∈
      (organiseUpClosure (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).nodes :=
    Or.inr ⟨6, by simp [d1Selected], Reach.single (by trivial)⟩
  have hff : fastForward
      (organiseUpClosure (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).nodes
      d1Repo.standsOn 6 26 := ⟨h6, h26, ReachOutside.direct (by trivial)⟩
  have hedge := (hf.o3 trivialPolicyCascade d1Selected d1Repo 6 26).mpr hff
  have hsel : (26 : Nat) ∈ d1Selected := hedge.2.1
  simp [d1Selected] at hsel

/-- F12 slice 6 review addition: nothing of rank zero is an authored target, so
no rank-zero vertex is reachable at all.  Uses the rank
(`F12D1Arms.lean:35-48`) that already proves the authored relation acyclic. -/
theorem d1_not_reachable_of_rank_zero {v : Nat} (hv : d1Rank v = 0) (u : Nat) :
    ¬ Reach d1Authored u v := by
  intro path
  cases path with
  | single edge =>
      have := d1_authored_increases_rank _ _ edge
      omega
  | tail _ edge =>
      have := d1_authored_increases_rank _ _ edge
      omega

/-- F12 slice 6 review addition, the unconditional half of
`admittedIndistinguishableFromAdded`: that theorem says a conformant function
returning the recorded twenty nodes MUST attribute the nine admitted ones to
`addedByOrganise`.  This says the up-closure temperament cannot produce them at
all — vertex 11 is not selected and is not an authored target of anything, so no
amount of closing over authorship reaches it.  The nine admitted nodes entered
the recorded cascade through a policy-grain `admit`, which is the origin the
`:LA2` field amendment (`Holes.lean:833-845`) added `admittedBy` to carry and
which this signature has nowhere to put.  That the up-closure of the recorded
selected set is exactly `{20, 21, 25, 26}`, disjoint from all nine admitted
nodes, is recomputed from the record by
`futon2:holes/labs/wm-contract/f12_conformance_check.bb`. -/
theorem organiseUpClosureOmitsAdmittedWitness :
    (11 : Nat) ∉
      (organiseUpClosure (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).nodes := by
  rintro (hsel | ⟨s, -, path⟩)
  · simp [d1Selected] at hsel
  · exact d1_not_reachable_of_rank_zero (by simp [d1Rank]) s path

end


end DarkTower.WarMachine.Holes
