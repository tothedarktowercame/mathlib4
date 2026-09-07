import DarkTower.WarMachine.F12Conformance

/-! # F12 admitting organise arm

This module combines the unchanged argument list of `Holes.lean:861` with the
widened result carrier from `F12D1Arms.lean:76`.  It measures conformance and
origin attribution without selecting a carrier design.
-/

open Set

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- F12 slice 7 signature from `Holes.lean:861`, changing only the codomain to `ArmOneCascade` from `F12D1Arms.lean:76`. -/
abbrev AdmittingOrganiseType (Policy P : Type*) :=
  Cascade Policy → Set P → Repository P → ArmOneCascade P

/-- F12 slice 7 conformance: `osel` prevents the widened selected field drifting from the function argument; O1 is the three-way law at `Holes.lean:895-897`; O2 uses the repository argument; O3 uses returned nodes as in `construct_cascade.clj:415` and `find_organise.clj:529`. -/
structure ConformantOrganiseAdmitting {Policy P : Type*}
    (f : AdmittingOrganiseType Policy P) : Prop where
  osel : ∀ t sel repo, (f t sel repo).selected = sel
  o1 : ∀ t sel repo,
    (f t sel repo).nodes =
      sel ∪ (f t sel repo).addedByOrganise ∪ (f t sel repo).admittedBy
  o2 : ∀ t sel repo u v, (f t sel repo).edges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo u v,
    (f t sel repo).edges u v ↔
      fastForward (f t sel repo).nodes repo.standsOn u v

/-- F12 slice 7 O2 measurement against `F12D1Arms.lean:106`: at the function signature, `d1Repo` supplies authorship definitionally and no `hrepo` argument is needed. -/
theorem admittingArmO2AtZaifRepo {Policy : Type*}
    {f : AdmittingOrganiseType Policy Nat} (hf : ConformantOrganiseAdmitting f) :
    ∀ t sel u v, (f t sel d1Repo).edges u v → Reach d1Authored u v := by
  intro t sel u v edge
  exact hf.o2 t sel d1Repo u v edge

/-- F12 slice 7 O3 measurement against `F12D1Arms.lean:113`: `d1Repo.standsOn` unfolds to `d1Authored`, with no caller-supplied equality. -/
theorem admittingArmO3AtZaifRepo {Policy : Type*}
    {f : AdmittingOrganiseType Policy Nat} (hf : ConformantOrganiseAdmitting f) :
    ∀ t sel u v, (f t sel d1Repo).edges u v ↔
      fastForward (f t sel d1Repo).nodes d1Authored u v := by
  intro t sel u v
  exact hf.o3 t sel d1Repo u v

/-- F12 slice 7 recorded-data helper from `F12D1Arms.lean:19-23`: only the literal selected set receives the nine zaif admissions. -/
def zaifAdmittedFor (sel : Set Nat) : Set Nat :=
  if sel = d1Selected then d1Admitted else ∅

/-- F12 slice 7 admitting implementation at node type `Nat`, because it names the recorded vertices from `F12D1Arms.lean:19-30`. -/
def organiseAdmitting {Policy : Type*} : AdmittingOrganiseType Policy Nat :=
  fun _ sel repo =>
    { nodes := sel ∪ ∅ ∪ zaifAdmittedFor sel
      addedByOrganise := ∅
      edges := fastForward (sel ∪ zaifAdmittedFor sel) repo.standsOn
      acyclic := fastForward_acyclic (sel ∪ zaifAdmittedFor sel) repo.standsOn repo.acyclic
      precedence := []
      selected := sel
      admittedBy := zaifAdmittedFor sel }

/-- F12 slice 7 proof that `organiseAdmitting` satisfies selected fidelity and three-way O1 plus repository-relative O2/O3. -/
theorem organiseAdmittingConformant {Policy : Type*} :
    ConformantOrganiseAdmitting (organiseAdmitting (Policy := Policy)) where
  osel := by intro t sel repo; rfl
  o1 := by intro t sel repo; simp [organiseAdmitting]
  o2 := by
    intro t sel repo u v edge
    exact d1_reachOutside_to_reach edge.2.2
  o3 := by intro t sel repo u v; simp [organiseAdmitting]

/-- F12 slice 7 nontrivial O1 measurement from `Holes.lean:987-996`: the admitting witness returns exactly the nine recorded admitted nodes. -/
theorem organiseAdmittingZaifAdmitsNine :
    (organiseAdmitting (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).admittedBy =
      d1Admitted := by
  simp [organiseAdmitting, zaifAdmittedFor]

/-- F12 slice 7 recorded carrier measurement from `Holes.lean:957-971`: selected plus admitted is exactly the twenty zaif nodes. -/
theorem organiseAdmittingZaifNodes :
    (organiseAdmitting (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).nodes =
      d1Nodes := by
  ext n
  simp [organiseAdmitting, zaifAdmittedFor, d1Selected, d1Admitted, d1Nodes]
  omega

/-- F12 slice 7 mirror implementation: the same recorded nine nodes are attributed to `addedByOrganise`, leaving `admittedBy` empty while preserving nodes and O2/O3-visible edges. -/
def organiseAdmittingMirror {Policy : Type*} : AdmittingOrganiseType Policy Nat :=
  fun _ sel repo =>
    { nodes := sel ∪ zaifAdmittedFor sel ∪ ∅
      addedByOrganise := zaifAdmittedFor sel
      edges := fastForward (sel ∪ zaifAdmittedFor sel) repo.standsOn
      acyclic := fastForward_acyclic (sel ∪ zaifAdmittedFor sel) repo.standsOn repo.acyclic
      precedence := []
      selected := sel
      admittedBy := ∅ }

/-- F12 slice 7 proof that the mirror attribution also satisfies all four conformance fields. -/
theorem organiseAdmittingMirrorConformant {Policy : Type*} :
    ConformantOrganiseAdmitting (organiseAdmittingMirror (Policy := Policy)) where
  osel := by intro t sel repo; rfl
  o1 := by intro t sel repo; simp [organiseAdmittingMirror]
  o2 := by
    intro t sel repo u v edge
    exact d1_reachOutside_to_reach edge.2.2
  o3 := by intro t sel repo u v; simp [organiseAdmittingMirror]

/-- F12 slice 7 comparison: admitting and mirror witnesses agree on recorded nodes. -/
theorem admittingAgreeOnNodes :
    (organiseAdmitting (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).nodes =
      (organiseAdmittingMirror (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).nodes := by
  simp [organiseAdmitting, organiseAdmittingMirror]

/-- F12 slice 7 comparison: admitting and mirror witnesses agree on the complete edge relation visible to O2/O3. -/
theorem admittingAgreeOnEdges :
    (organiseAdmitting (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).edges =
      (organiseAdmittingMirror (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).edges := by
  rfl

/-- F12 slice 7 main measurement: widening makes the third origin statable but not determined; two fully conformant functions agree on nodes and O2/O3-visible edges yet disagree on admission, witnessed by recorded vertex 11. -/
theorem admittingSplitUnderdetermined :
    (organiseAdmitting (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).admittedBy ≠
      (organiseAdmittingMirror (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).admittedBy := by
  intro h
  have h11 := Set.ext_iff.mp h 11
  simp [organiseAdmitting, organiseAdmittingMirror, zaifAdmittedFor,
    d1Admitted] at h11

/-- F12 slice 7 general law consequence: any conformant function returning the recorded nodes is constrained only by the three-way union.  The existential conjuncts then exhibit conformant empty-admission and recorded-admission witnesses; this proves non-uniqueness across implementations, not a stronger claim about an undefined notion of determination for one fixed function. -/
theorem admittingThirdOriginUnconstrainedGeneral {Policy : Type*}
    (f : AdmittingOrganiseType Policy Nat) (hf : ConformantOrganiseAdmitting f)
    (t : Cascade Policy)
    (hnodes : (f t d1Selected d1Repo).nodes = d1Nodes) :
    d1Nodes = d1Selected ∪ (f t d1Selected d1Repo).addedByOrganise ∪
        (f t d1Selected d1Repo).admittedBy ∧
      (∃ g : AdmittingOrganiseType Unit Nat, ConformantOrganiseAdmitting g ∧
        (g trivialPolicyCascade d1Selected d1Repo).nodes = d1Nodes ∧
        (g trivialPolicyCascade d1Selected d1Repo).admittedBy = ∅) ∧
      (∃ g : AdmittingOrganiseType Unit Nat, ConformantOrganiseAdmitting g ∧
        (g trivialPolicyCascade d1Selected d1Repo).nodes = d1Nodes ∧
        (g trivialPolicyCascade d1Selected d1Repo).admittedBy = d1Admitted) := by
  refine ⟨hnodes ▸ hf.o1 t d1Selected d1Repo, ?_, ?_⟩
  · refine ⟨organiseAdmittingMirror, organiseAdmittingMirrorConformant,
      admittingAgreeOnNodes.symm.trans organiseAdmittingZaifNodes, ?_⟩
    rfl
  · exact ⟨organiseAdmitting, organiseAdmittingConformant,
      organiseAdmittingZaifNodes, organiseAdmittingZaifAdmitsNine⟩

/-- F12 slice 7 review: the recorded edge is IN the relation both witnesses return, so
`admittingAgreeOnEdges` is an agreement on a non-empty relation and not on the empty one.
The edge is `18 → 19` from `F12D1Arms.lean:26-28`, the single fast-forward over the twenty
recorded nodes (`runs/F12-organise/01-zaif-transcription.edn` `:fast-forward :over-nodes`). -/
theorem admittingZaifEdgeNonVacuous :
    (organiseAdmitting (Policy := Unit) trivialPolicyCascade d1Selected d1Repo).edges 18 19 ∧
      (organiseAdmittingMirror (Policy := Unit)
        trivialPolicyCascade d1Selected d1Repo).edges 18 19 := by
  have hmem : ∀ n : Nat, n < 20 → n ∈ d1Selected ∪ zaifAdmittedFor d1Selected := by
    intro n hn
    simp [zaifAdmittedFor, d1Selected, d1Admitted]
    omega
  refine ⟨⟨hmem 18 (by omega), hmem 19 (by omega), ReachOutside.direct ?_⟩,
    ⟨hmem 18 (by omega), hmem 19 (by omega), ReachOutside.direct ?_⟩⟩ <;>
    exact trivial

/-- F12 slice 7 review: the selected-reading counterpart of `ConformantOrganiseAdmitting`,
differing in exactly one place — O3 quantifies over the function's `sel` argument, which is
what `Holes.lean:909` does, rather than over its returned nodes, which is what
`futon3:checks/find_organise.clj:529` does.  Which field O3 reads is an open question beside
D1 (C540 §b), so the arm's result is measured under both readings rather than under the one
the slice happened to pick. -/
structure ConformantOrganiseAdmittingSelected {Policy P : Type*}
    (f : AdmittingOrganiseType Policy P) : Prop where
  osel : ∀ t sel repo, (f t sel repo).selected = sel
  o1 : ∀ t sel repo,
    (f t sel repo).nodes =
      sel ∪ (f t sel repo).addedByOrganise ∪ (f t sel repo).admittedBy
  o2 : ∀ t sel repo u v, (f t sel repo).edges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo u v,
    (f t sel repo).edges u v ↔ fastForward sel repo.standsOn u v

/-- F12 slice 7 review: the admitting witness under the selected reading of O3. -/
def organiseAdmittingSelectedReading {Policy : Type*} : AdmittingOrganiseType Policy Nat :=
  fun _ sel repo =>
    { nodes := sel ∪ ∅ ∪ zaifAdmittedFor sel
      addedByOrganise := ∅
      edges := fastForward sel repo.standsOn
      acyclic := fastForward_acyclic sel repo.standsOn repo.acyclic
      precedence := []
      selected := sel
      admittedBy := zaifAdmittedFor sel }

/-- F12 slice 7 review: its mirror, attributing the same nine nodes to `addedByOrganise`. -/
def organiseAdmittingSelectedReadingMirror {Policy : Type*} :
    AdmittingOrganiseType Policy Nat :=
  fun _ sel repo =>
    { nodes := sel ∪ zaifAdmittedFor sel ∪ ∅
      addedByOrganise := zaifAdmittedFor sel
      edges := fastForward sel repo.standsOn
      acyclic := fastForward_acyclic sel repo.standsOn repo.acyclic
      precedence := []
      selected := sel
      admittedBy := ∅ }

/-- F12 slice 7 review: the admitting witness is conformant under the selected reading. -/
theorem organiseAdmittingSelectedReadingConformant {Policy : Type*} :
    ConformantOrganiseAdmittingSelected
      (organiseAdmittingSelectedReading (Policy := Policy)) where
  osel := by intro t sel repo; rfl
  o1 := by intro t sel repo; simp [organiseAdmittingSelectedReading]
  o2 := by
    intro t sel repo u v edge
    exact d1_reachOutside_to_reach edge.2.2
  o3 := by intro t sel repo u v; rfl

/-- F12 slice 7 review: so is its mirror. -/
theorem organiseAdmittingSelectedReadingMirrorConformant {Policy : Type*} :
    ConformantOrganiseAdmittingSelected
      (organiseAdmittingSelectedReadingMirror (Policy := Policy)) where
  osel := by intro t sel repo; rfl
  o1 := by intro t sel repo; simp [organiseAdmittingSelectedReadingMirror]
  o2 := by
    intro t sel repo u v edge
    exact d1_reachOutside_to_reach edge.2.2
  o3 := by intro t sel repo u v; rfl

/-- F12 slice 7 review: the split survives the other reading of O3.  Two functions conformant
under the selected reading agree on the recorded nodes and on the whole edge relation and still
disagree on `admittedBy`, at recorded vertex 11.  So `admittingSplitUnderdetermined` does not
depend on which field O3 quantifies over, and the open field question does not have to be
answered for the arm's result to stand. -/
theorem admittingSplitUnderdeterminedSelectedReading :
    (organiseAdmittingSelectedReading (Policy := Unit)
        trivialPolicyCascade d1Selected d1Repo).nodes =
      (organiseAdmittingSelectedReadingMirror (Policy := Unit)
        trivialPolicyCascade d1Selected d1Repo).nodes ∧
    (organiseAdmittingSelectedReading (Policy := Unit)
        trivialPolicyCascade d1Selected d1Repo).edges =
      (organiseAdmittingSelectedReadingMirror (Policy := Unit)
        trivialPolicyCascade d1Selected d1Repo).edges ∧
    (organiseAdmittingSelectedReading (Policy := Unit)
        trivialPolicyCascade d1Selected d1Repo).admittedBy ≠
      (organiseAdmittingSelectedReadingMirror (Policy := Unit)
        trivialPolicyCascade d1Selected d1Repo).admittedBy := by
  refine ⟨by simp [organiseAdmittingSelectedReading, organiseAdmittingSelectedReadingMirror],
    rfl, ?_⟩
  intro h
  have h11 := Set.ext_iff.mp h 11
  simp [organiseAdmittingSelectedReading, organiseAdmittingSelectedReadingMirror,
    zaifAdmittedFor, d1Admitted] at h11

/-- F12 slice 7 review: every selected vertex has authored rank zero (`F12D1Arms.lean:35-41`). -/
theorem d1Rank_eq_zero_of_selected {v : Nat} (hv : v ∈ d1Selected) : d1Rank v = 0 := by
  simp only [d1Selected, mem_setOf_eq] at hv
  interval_cases v <;> rfl

/-- F12 slice 7 review: what the other reading COSTS, measured rather than argued.  Under the
selected reading the two witnesses agree on an EMPTY edge relation on the recorded inputs — no
fast-forward runs between two selected vertices, because every authored edge raises the rank and
every selected vertex has rank zero.  The one recorded edge `18 → 19`
(`admittingZaifEdgeNonVacuous`) is visible only under the node-set reading, where the admitted
nodes are in the set O3 quantifies over.  So both readings leave the third origin undetermined,
and they differ in whether the agreement is witnessed on any edge at all. -/
theorem admittingSelectedReadingEdgesEmptyOnRecorded :
    ∀ u v, ¬ (organiseAdmittingSelectedReading (Policy := Unit)
      trivialPolicyCascade d1Selected d1Repo).edges u v := by
  intro u v edge
  have hrank : d1Rank u < d1Rank v :=
    reach_increases_rank d1Authored d1Rank d1_authored_increases_rank
      (d1_reachOutside_to_reach edge.2.2)
  rw [d1Rank_eq_zero_of_selected edge.2.1] at hrank
  omega

end


end DarkTower.WarMachine.Holes
