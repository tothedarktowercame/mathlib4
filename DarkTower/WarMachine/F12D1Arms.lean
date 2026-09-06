import DarkTower.WarMachine.Holes

/-! # F12 decision D1: three executed carrier arms

This file builds the three carrier alternatives recorded in
`C539-F12-organise-census.md` §4 against the zaif transcription.  It records
what each carrier can state and prove; it makes no choice between them.
-/

open Set

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- Shared F12 slice-5 data from `Holes.lean:957`: the eleven selected nodes. -/
def d1Selected : Set Nat := {n | n < 11}

/-- Shared F12 slice-5 data from `Holes.lean:959`: the nine policy-admitted nodes. -/
def d1Admitted : Set Nat := {n | 11 ≤ n ∧ n < 20}

/-- Shared F12 slice-5 data from `Holes.lean:961`: all twenty cascade nodes. -/
def d1Nodes : Set Nat := {n | n < 20}

/-- Shared F12 slice-5 data from `Holes.lean:965-968`: the thirteen authored `@why` edges. -/
def d1Authored : Nat → Nat → Prop
  | 6, 26 | 7, 20 | 14, 23 | 15, 22 | 16, 24 | 17, 20 | 18, 19 | 19, 20
  | 22, 24 | 23, 26 | 24, 21 | 25, 21 | 26, 25 => True
  | _, _ => False

/-- Shared F12 slice-5 data from `Holes.lean:957-971`: the 27-vertex authored closure. -/
def d1Closure : Set Nat := {n | n < 27}

/-- Shared F12 slice-5 rank used with `CascadeOrder.lean:37-41`; every authored edge increases it. -/
def d1Rank : Nat → Nat
  | 19 | 22 | 23 => 1
  | 20 | 24 | 26 => 2
  | 25 => 3
  | 21 => 4
  | _ => 0

/-- Shared F12 slice-5 edge check for `CascadeOrder.lean:37-41`: authored edges increase `d1Rank`. -/
theorem d1_authored_increases_rank :
    ∀ u v, d1Authored u v → d1Rank u < d1Rank v := by
  intro u v h
  simp only [d1Authored] at h
  split at h <;> simp_all [d1Rank]

/-- Shared F12 slice-5 acyclicity proof for the authored relation, via `CascadeOrder.lean:37-41`. -/
theorem d1AuthoredAcyclic : acyclicDescent d1Authored :=
  acyclic_of_increasing_rank d1Authored d1Rank d1_authored_increases_rank

/-- Shared F12 slice-5 replacement for private `Holes.lean:886-890`: a fast-forward path is authored reachability. -/
theorem d1_reachOutside_to_reach {P : Type*} {selected : Set P}
    {r : P → P → Prop} {u v : P} : ReachOutside selected r u v → Reach r u v := by
  intro path
  induction path with
  | direct edge => exact Reach.single edge
  | through _ _ edge ih => exact Reach.tail ih edge

/-- Shared F12 slice-5 rank fact: every fast-forward over `d1Nodes` increases the authored rank. -/
theorem d1_fastForward_increases_rank :
    ∀ u v, fastForward d1Nodes d1Authored u v → d1Rank u < d1Rank v := by
  intro u v edge
  exact reach_increases_rank d1Authored d1Rank d1_authored_increases_rank
    (d1_reachOutside_to_reach edge.2.2)

/-- Shared F12 slice-5 acyclicity proof for organised edges, using `Holes.lean:829-831` and `CascadeOrder.lean:37-41`. -/
theorem d1OrganisedAcyclic : acyclicDescent (fastForward d1Nodes d1Authored) :=
  acyclic_of_increasing_rank (fastForward d1Nodes d1Authored) d1Rank
    d1_fastForward_increases_rank

/-- Arm one from C539 §4(i): `Cascade` at `Holes.lean:29-35`, widened only with O1's two missing origins. -/
structure ArmOneCascade (P : Type*) where
  nodes : Set P
  addedByOrganise : Set P
  edges : P → P → Prop
  acyclic : acyclicDescent edges
  precedence : List P
  selected : Set P
  admittedBy : Set P

/-- Arm one's proposed organise type, corresponding to `Holes.lean:861`. -/
abbrev armOneOrganiseType (Policy P : Type*) :=
  ArmOneCascade Policy → Set P → Repository P → ArmOneCascade P

/-- Arm one zaif execution from `Holes.lean:957-984`; organised edges fast-forward over all nodes. -/
def armOneZaif : ArmOneCascade Nat where
  nodes := d1Nodes
  addedByOrganise := ∅
  edges := fastForward d1Nodes d1Authored
  acyclic := d1OrganisedAcyclic
  precedence := []
  selected := d1Selected
  admittedBy := d1Admitted

/-- Arm one, O1 from `Holes.lean:987-996`: the widened carrier records all three node origins. -/
theorem armOneO1 :
    armOneZaif.nodes =
      armOneZaif.selected ∪ armOneZaif.addedByOrganise ∪ armOneZaif.admittedBy := by
  ext n
  simp [armOneZaif, d1Nodes, d1Selected, d1Admitted]
  omega

/-- Arm one, O2 from `Holes.lean:998-1005`: with repository `standsOn` named separately, every organised edge has authored reachability.  Thus arm one closes O1 and still needs arm three's pairing to state O2/O3. -/
theorem armOneO2 (repo : Repository Nat) (hrepo : repo.standsOn = d1Authored) :
    ∀ u v, armOneZaif.edges u v → Reach repo.standsOn u v := by
  intro u v edge
  rw [hrepo]
  exact d1_reachOutside_to_reach edge.2.2

/-- Arm one, O3 from `Holes.lean:1007-1016`: with repository `standsOn` named separately, its edge field is exactly node fast-forward. -/
theorem armOneO3 (repo : Repository Nat) (hrepo : repo.standsOn = d1Authored) :
    ∀ u v, armOneZaif.edges u v ↔ fastForward armOneZaif.nodes repo.standsOn u v := by
  intro u v
  simp [armOneZaif, hrepo]

/-- Arm two from C539 §4(ii): retyping `Holes.lean:861` needs a `Score` parameter absent from the s3e signature. -/
abbrev armTwoOrganiseType (Policy P Score : Type*) :=
  Cascade Policy → Set P → Repository P → CascadeDiff P Score

/-- Arm two, O4 measurement from `Holes.lean:916-921` and the public zaif fixture at `Holes.lean:973-984`: the precedence-change antecedent O4 needs is false there, so retyping the codomain buys an O4 that cannot fire on the one library-scale run recorded.  Contrast the C59 fixture at `Holes.lean:872-884`, whose precedence does move -- this is a fact about the run, not about the statement's shape. -/
theorem armTwoO4AntecedentUnsatisfiable :
    ¬ (wmZaifCascadeDiffFixture.precedenceBefore ≠
      wmZaifCascadeDiffFixture.precedenceAfter) :=
  fun h => h rfl

/-- Arm two, O4 measurement, second of the three before/after pairs: the acting order does not move either, so O4's disjunctive conclusion has no witness here. -/
theorem armTwoZaifActingOrderFlat :
    wmZaifCascadeDiffFixture.actingOrderBefore =
      wmZaifCascadeDiffFixture.actingOrderAfter := rfl

/-- Arm two, O4 measurement, third of the three before/after pairs: the score does not move either.  `construct_cascade.clj:402` (fields at `:420-421`) carries no score for this run, which is where the zero comes from. -/
theorem armTwoZaifScoreFlat :
    wmZaifCascadeDiffFixture.scoreBefore = wmZaifCascadeDiffFixture.scoreAfter := rfl

/-- Arm three from C539 §4(iii): the unmodified `Repository` carrier at `Holes.lean:121-124`. -/
def d1Repo : Repository Nat where
  patterns := d1Closure
  standsOn := d1Authored
  acyclic := d1AuthoredAcyclic

/-- Arm three from C539 §4(iii): the unmodified `Cascade` carrier at `Holes.lean:29-35`. -/
def d1CascadeZaif : Cascade Nat where
  nodes := d1Nodes
  addedByOrganise := ∅
  edges := fastForward d1Nodes d1Authored
  acyclic := d1OrganisedAcyclic
  precedence := []

/-- Arm three, O2 from `Holes.lean:998-1005`: every cascade edge is reachability in the paired repository. -/
theorem armThreeO2 :
    ∀ u v, d1CascadeZaif.edges u v → Reach d1Repo.standsOn u v := by
  intro u v edge
  exact d1_reachOutside_to_reach edge.2.2

/-- Arm three, O3 from `Holes.lean:1007-1016`: cascade edges are exactly node fast-forwards through paired repository authorship. -/
theorem armThreeO3 :
    ∀ u v, d1CascadeZaif.edges u v ↔
      fastForward d1CascadeZaif.nodes d1Repo.standsOn u v := by
  intro u v
  rfl

/-- Arm three and arm one, non-vacuity of O2 and O3: the organised edge set is not empty.  Without this both laws would hold of a cascade with no edges at all, and the C59 fixture's single fast-forward would be the only thing either had ever been read on. -/
theorem armThreeOrganisedEdgeExists : d1CascadeZaif.edges 18 19 := by
  refine ⟨?_, ?_, ReachOutside.direct ?_⟩
  · show (18 : Nat) ∈ d1Nodes
    simp [d1Nodes]
  · show (19 : Nat) ∈ d1Nodes
    simp [d1Nodes]
  · trivial

/-- Arm three and arm one, the other half of non-vacuity: an unauthored pair is not an organised edge, so `edges` is not the total relation. -/
theorem armThreeNoUnauthoredEdge : ¬ d1CascadeZaif.edges 0 1 := by
  rintro ⟨-, -, path⟩
  have := d1_fastForward_increases_rank 0 1 ⟨by simp [d1Nodes], by simp [d1Nodes], path⟩
  simp [d1Rank] at this

/-- Arm three, O1 measurement from `Holes.lean:987-996`: substituting repository patterns for the absent selected field is false on the recorded 20-node/27-vertex data. -/
theorem armThreeO1PatternsSubstitutionFails :
    d1CascadeZaif.nodes ≠ d1Repo.patterns ∪ d1CascadeZaif.addedByOrganise := by
  intro h
  have h26 := Set.ext_iff.mp h 26
  simp [d1CascadeZaif, d1Repo, d1Nodes, d1Closure] at h26

end

end DarkTower.WarMachine.Holes
