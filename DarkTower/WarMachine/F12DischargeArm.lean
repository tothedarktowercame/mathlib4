import DarkTower.WarMachine.F12Conformance

/-! # F12 organise discharge arm

This module measures inhabitance, conformance, swappability, temperament use,
and opacity at the exact `organise` signature without selecting an implementation.
-/

open Set

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- F12 slice 14 R0.1: empty cascade at the carrier from `Holes.lean:29-34`. -/
def organiseEmptyCascade {P : Type*} : Cascade P where
  nodes := ∅
  addedByOrganise := ∅
  edges := fun _ _ => False
  acyclic := by intro x path; cases path with | single h => exact h | tail _ h => exact h
  precedence := []

/-- F12 slice 14 R0.2: constant inhabitant of `OrganiseType` from `F12Conformance.lean:19-20`. -/
def organiseEmpty {Policy P : Type*} : OrganiseType Policy P :=
  fun _ _ _ => organiseEmptyCascade

/-- F12 slice 14 R0.3: the exact `organise` type at `Holes.lean:861` is inhabited without assumptions. -/
theorem organiseTypeNonempty {Policy P : Type*} : Nonempty (OrganiseType Policy P) :=
  ⟨organiseEmpty⟩

/-- F12 slice 14 R0.4: mere inhabitance buys no selected-reading conformance; O1 fails on `d1Selected` from `F12D1Arms.lean:17`. -/
theorem organiseEmptyNotConformantSelected :
    ¬ ConformantOrganiseSelected (organiseEmpty (Policy := Unit) (P := Nat)) := by
  intro h
  have ho1 := h.o1 trivialPolicyCascade d1Selected d1Repo
  have h0 := Set.ext_iff.mp ho1 0
  simp [organiseEmpty, organiseEmptyCascade, d1Selected] at h0

/-- F12 slice 14 R0.5: the same empty inhabitant also fails node-reading O1 from `F12Conformance.lean:31-36`. -/
theorem organiseEmptyNotConformantNodes :
    ¬ ConformantOrganiseNodes (organiseEmpty (Policy := Unit) (P := Nat)) := by
  intro h
  have ho1 := h.o1 trivialPolicyCascade d1Selected d1Repo
  have h0 := Set.ext_iff.mp ho1 0
  simp [organiseEmpty, organiseEmptyCascade, d1Selected] at h0

/-- F12 slice 14 R1.6: a selected-reading conformant discharge exists, witnessed by `organiseSelectedOnly` at `F12Conformance.lean:59`. -/
theorem organiseDischargeExistsSelected {Policy P : Type*} :
    ∃ f : OrganiseType Policy P, ConformantOrganiseSelected f :=
  ⟨organiseSelectedOnly, organiseSelectedOnlyConformant⟩

/-- F12 slice 14 R1.7: a node-reading conformant discharge exists independently, using `organiseSelectedOnlyConformantNodes` at `F12Conformance.lean:157`. -/
theorem organiseDischargeExistsNodes {Policy P : Type*} :
    ∃ f : OrganiseType Policy P, ConformantOrganiseNodes f :=
  ⟨organiseSelectedOnly, organiseSelectedOnlyConformantNodes⟩

/-- F12 slice 14 R2.8: named up-closure set from `organiseUpClosure` at `F12Conformance.lean:77`. -/
def upClosureNodesSet {P : Type*} (sel : Set P) (repo : Repository P) : Set P :=
  sel ∪ {p | ∃ s ∈ sel, Reach repo.standsOn s p}

/-- F12 slice 14 R2.9: node-reading up-closure discharge whose nodes and fast-forward endpoints share `upClosureNodesSet`. -/
def organiseNodesUpClosure {Policy P : Type*} : OrganiseType Policy P :=
  fun _ sel repo =>
    { nodes := upClosureNodesSet sel repo
      addedByOrganise := upClosureNodesSet sel repo \ sel
      edges := fastForward (upClosureNodesSet sel repo) repo.standsOn
      acyclic := fastForward_acyclic (upClosureNodesSet sel repo) repo.standsOn repo.acyclic
      precedence := [] }

/-- F12 slice 14 R2.10: the named up-closure discharge satisfies the node-set reading at `F12Conformance.lean:31`. -/
theorem organiseNodesUpClosureConformantNodes {Policy P : Type*} :
    ConformantOrganiseNodes
      (organiseNodesUpClosure (Policy := Policy) (P := P)) where
  o1 := by
    intro t sel repo
    ext p
    simp [organiseNodesUpClosure, upClosureNodesSet]
  o2 := by
    intro t sel repo u v hedge
    exact d1_reachOutside_to_reach hedge.2.2
  o3 := by intros; rfl

/-- F12 slice 14 R2.11: selected-reading laws admit two functions with different recorded node sets, using `organiseWitnessesDifferOnZaif` at `F12Conformance.lean:107`. -/
theorem organiseDischargeNotUniqueSelected :
    ∃ f g : OrganiseType Unit Nat,
      ConformantOrganiseSelected f ∧ ConformantOrganiseSelected g ∧
      (f trivialPolicyCascade d1Selected d1Repo).nodes ≠
        (g trivialPolicyCascade d1Selected d1Repo).nodes :=
  ⟨organiseSelectedOnly, organiseUpClosure, organiseSelectedOnlyConformant,
    organiseUpClosureConformant, organiseWitnessesDifferOnZaif⟩

/-- F12 slice 14 R2.12: node-reading laws likewise admit selected-only and node-up-closure functions with different recorded node sets. -/
theorem organiseDischargeNotUniqueNodes :
    ∃ f g : OrganiseType Unit Nat,
      ConformantOrganiseNodes f ∧ ConformantOrganiseNodes g ∧
      (f trivialPolicyCascade d1Selected d1Repo).nodes ≠
        (g trivialPolicyCascade d1Selected d1Repo).nodes := by
  refine ⟨organiseSelectedOnly, organiseNodesUpClosure,
    organiseSelectedOnlyConformantNodes, organiseNodesUpClosureConformantNodes, ?_⟩
  intro h
  have h26 := Set.ext_iff.mp h 26
  simp [organiseSelectedOnly, organiseNodesUpClosure, upClosureNodesSet, d1Selected, d1Repo] at h26
  exact h26 6 (by omega) (Reach.single (by trivial))

/-- F12 slice 14 review addition, R2 floor: the two node-reading discharges are
not two unrelated functions.  Both return every one of the recorded selected
nodes (`F12D1Arms.lean:17`), and that set is not empty, so what
`organiseDischargeNotUniqueNodes` exhibits is a disagreement about O1's SECOND
origin and nothing else.  Slices 8, 10, 11 and 13 each shipped a comparison with
no such floor under it and each had one added in review. -/
theorem organiseDischargeWitnessesAgreeOnSelected :
    d1Selected.Nonempty ∧
      d1Selected ⊆ (organiseSelectedOnly trivialPolicyCascade d1Selected d1Repo).nodes ∧
      d1Selected ⊆ (organiseNodesUpClosure trivialPolicyCascade d1Selected d1Repo).nodes := by
  refine ⟨⟨0, by simp [d1Selected]⟩, ?_, ?_⟩
  · intro x hx; exact hx
  · intro x hx; exact Or.inl hx

/-- F12 slice 14 R3.13: recorded authored edge `6 → 26` from `F12D1Arms.lean:26` makes vertex 26 organise-added. -/
theorem organiseNodesUpClosureAddsZaifVertex :
    (26 : Nat) ∈
      (organiseNodesUpClosure trivialPolicyCascade d1Selected d1Repo).addedByOrganise := by
  refine ⟨Or.inr ⟨6, by simp [d1Selected], Reach.single (by trivial)⟩, ?_⟩
  simp [d1Selected]

/-- F12 slice 14 R3.14: the node-up-closure edge relation is inhabited by recorded edge `6 → 26`. -/
theorem organiseNodesUpClosureEdgeExists :
    (organiseNodesUpClosure trivialPolicyCascade d1Selected d1Repo).edges 6 26 := by
  refine ⟨Or.inl (by simp [d1Selected]), ?_, ReachOutside.direct (by trivial)⟩
  exact organiseNodesUpClosureAddsZaifVertex.1

/-- F12 slice 14 R3.15: selected-only does not contain `6 → 26` because vertex 26 is outside its endpoint set. -/
theorem organiseSelectedOnlyNoSuchEdge :
    ¬ (organiseSelectedOnly trivialPolicyCascade d1Selected d1Repo).edges 6 26 := by
  intro hedge
  have h26 := hedge.2.1
  simp [d1Selected] at h26

/-- F12 slice 14 R3.16: the node-up-closure relation is not total; unauthored pair `0 → 1` is absent as at `F12D1Arms.lean:174`. -/
theorem organiseNodesUpClosureNoUnauthoredEdge :
    ¬ (organiseNodesUpClosure trivialPolicyCascade d1Selected d1Repo).edges 0 1 := by
  intro hedge
  have hrank := reach_increases_rank d1Authored d1Rank d1_authored_increases_rank
    (d1_reachOutside_to_reach hedge.2.2)
  simp [d1Rank] at hrank

/-- F12 slice 14 R4.17: nonempty-precedence temperament contrasting `trivialPolicyCascade` at `F12Conformance.lean:99`. -/
def nonTrivialPolicyCascade : Cascade Unit where
  nodes := ∅
  addedByOrganise := ∅
  edges := fun _ _ => False
  acyclic := by intro x path; cases path with | single h => exact h | tail _ h => exact h
  precedence := [()]

/-- F12 slice 14 R4.18: selected-reading discharge branches on the temperament precedence introduced at `Holes.lean:861`. -/
def organiseByTemperamentSelected {Policy P : Type*} : OrganiseType Policy P :=
  fun t sel repo => match t.precedence with
    | [] => organiseSelectedOnly t sel repo
    | _ :: _ => organiseUpClosure t sel repo

/-- F12 slice 14 R4.19: both temperament branches satisfy selected-reading conformance from `F12Conformance.lean:23`. -/
theorem organiseByTemperamentSelectedConformant {Policy P : Type*} :
    ConformantOrganiseSelected
      (organiseByTemperamentSelected (Policy := Policy) (P := P)) where
  o1 := by
    intro t sel repo
    cases h : t.precedence with
    | nil => simpa [organiseByTemperamentSelected, h] using
        organiseSelectedOnlyConformant.o1 t sel repo
    | cons x xs => simpa [organiseByTemperamentSelected, h] using
        organiseUpClosureConformant.o1 t sel repo
  o2 := by
    intro t sel repo u v
    cases h : t.precedence with
    | nil => simpa [organiseByTemperamentSelected, h] using
        organiseSelectedOnlyConformant.o2 t sel repo u v
    | cons x xs => simpa [organiseByTemperamentSelected, h] using
        organiseUpClosureConformant.o2 t sel repo u v
  o3 := by
    intro t sel repo u v
    cases h : t.precedence with
    | nil => simpa [organiseByTemperamentSelected, h] using
        organiseSelectedOnlyConformant.o3 t sel repo u v
    | cons x xs => simpa [organiseByTemperamentSelected, h] using
        organiseUpClosureConformant.o3 t sel repo u v

/-- F12 slice 14 R4.20: a selected-reading conformant discharge may distinguish the empty and nonempty temperament precedences. -/
theorem organiseByTemperamentSelectedReadsTemperament :
    (organiseByTemperamentSelected trivialPolicyCascade d1Selected d1Repo).nodes ≠
      (organiseByTemperamentSelected nonTrivialPolicyCascade d1Selected d1Repo).nodes := by
  intro h
  have h26 := Set.ext_iff.mp h 26
  simp [organiseByTemperamentSelected, trivialPolicyCascade, nonTrivialPolicyCascade,
    organiseSelectedOnly, organiseUpClosure, d1Selected, d1Repo] at h26
  exact h26 6 (by omega) (Reach.single (by trivial))

/-- F12 slice 14 R4.21: node-reading counterpart branches between selected-only and `organiseNodesUpClosure`. -/
def organiseByTemperamentNodes {Policy P : Type*} : OrganiseType Policy P :=
  fun t sel repo => match t.precedence with
    | [] => organiseSelectedOnly t sel repo
    | _ :: _ => organiseNodesUpClosure t sel repo

/-- F12 slice 14 R4.22: both temperament branches satisfy node-reading conformance at `F12Conformance.lean:31`. -/
theorem organiseByTemperamentNodesConformant {Policy P : Type*} :
    ConformantOrganiseNodes
      (organiseByTemperamentNodes (Policy := Policy) (P := P)) where
  o1 := by
    intro t sel repo
    cases h : t.precedence with
    | nil => simpa [organiseByTemperamentNodes, h] using
        organiseSelectedOnlyConformantNodes.o1 t sel repo
    | cons x xs => simpa [organiseByTemperamentNodes, h] using
        organiseNodesUpClosureConformantNodes.o1 t sel repo
  o2 := by
    intro t sel repo u v
    cases h : t.precedence with
    | nil => simpa [organiseByTemperamentNodes, h] using
        organiseSelectedOnlyConformantNodes.o2 t sel repo u v
    | cons x xs => simpa [organiseByTemperamentNodes, h] using
        organiseNodesUpClosureConformantNodes.o2 t sel repo u v
  o3 := by
    intro t sel repo u v
    cases h : t.precedence with
    | nil => simpa [organiseByTemperamentNodes, h] using
        organiseSelectedOnlyConformantNodes.o3 t sel repo u v
    | cons x xs => simpa [organiseByTemperamentNodes, h] using
        organiseNodesUpClosureConformantNodes.o3 t sel repo u v

/-- F12 slice 14 R4.23: node-reading conformance may also read the temperament, independently of the registered O3-field choice. -/
theorem organiseByTemperamentNodesReadsTemperament :
    (organiseByTemperamentNodes trivialPolicyCascade d1Selected d1Repo).nodes ≠
      (organiseByTemperamentNodes nonTrivialPolicyCascade d1Selected d1Repo).nodes := by
  intro h
  have h26 := Set.ext_iff.mp h 26
  simp [organiseByTemperamentNodes, trivialPolicyCascade, nonTrivialPolicyCascade,
    organiseSelectedOnly, organiseNodesUpClosure, upClosureNodesSet, d1Selected, d1Repo] at h26
  exact h26 6 (by omega) (Reach.single (by trivial))

/-- F12 slice 14 R4.24: the selected-only conformant discharge ignores temperament entirely; full structure equality closes definitionally at `F12Conformance.lean:59-65`. -/
theorem organiseSelectedOnlyIgnoresTemperament :
    ∀ (t t' : Cascade Unit) (sel : Set Nat) (repo : Repository Nat),
      organiseSelectedOnly t sel repo = organiseSelectedOnly t' sel repo := by
  intros
  rfl

/-- F12 slice 14 R5.25, CORRECTED IN REVIEW.  The dispatch packet claimed that
`opaque` REQUIRES a body, so that opacity would hide a chosen implementation
rather than avoid choosing one.  That is false, and `organiseOpaqueNoBody` below
is the refutation.  What the two routes actually differ in is their AXIOM
FOOTPRINT, and the difference is machine-readable: this declaration names
`organiseEmpty` and `#print axioms` reports no axioms of it, while the bodiless
one reports `Classical.choice`.  Either route removes the `sorry` and neither
leaves an O-law provable of the declaration, since nothing about the value
survives the seal -- and the value this one seals is the one
`organiseEmptyNotConformantSelected` refutes. -/
opaque organiseOpaqueZaif : OrganiseType Unit Nat := organiseEmpty

/-- F12 slice 14 R5.25 review addition: the inhabitance `organiseTypeNonempty`
proves is the whole of what `opaque` needs.  Declared `local` so that importing
this module does not put a `Nonempty` instance for `organise`'s own type into
anyone else's scope. -/
local instance organiseTypeNonemptyInstance : Nonempty (OrganiseType Unit Nat) :=
  organiseTypeNonempty

/-- F12 slice 14 R5.25 review addition: `opaque` with NO body at all, elaborating
from the instance above.  This is the declaration that refutes the packet's
premise, and it is what makes the cost of the opacity route measurable rather
than asserted: a bodiless `opaque` is a classical choice among the type's
inhabitants, which `#print axioms` reports as `Classical.choice`, where
`organiseOpaqueZaif` reports none. -/
opaque organiseOpaqueNoBody : OrganiseType Unit Nat

end

end DarkTower.WarMachine.Holes
