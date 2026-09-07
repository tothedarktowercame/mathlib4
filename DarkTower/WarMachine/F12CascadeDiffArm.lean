import DarkTower.WarMachine.F12AdmittingArm

/-! # F12 CascadeDiff function arm

This module executes the function-at-`CascadeDiff` carrier arm. It records what
the arm states and what its clauses exclude, without selecting a carrier.
-/

open Set

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- F12 slice 13 task 1: all four laws at `armTwoOrganiseType` from `F12D1Arms.lean:119`; O3 takes the node-set reading used at `futon3:checks/construct_cascade.clj:415`, without deciding the separate field choice. -/
structure ConformantOrganiseCascadeDiff {Policy P Score : Type*}
    (f : armTwoOrganiseType Policy P Score) : Prop where
  osel : ∀ t sel repo, (f t sel repo).selected = sel
  oauth : ∀ t sel repo, (f t sel repo).authoredEdges = repo.standsOn
  o1 : ∀ t sel repo, (f t sel repo).nodes =
    sel ∪ (f t sel repo).addedByOrganise ∪ (f t sel repo).admittedBy
  o2 : ∀ t sel repo u v, (f t sel repo).organisedEdges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo u v, (f t sel repo).organisedEdges u v ↔
    fastForward (f t sel repo).nodes repo.standsOn u v
  o4 : ∀ t sel repo,
    (f t sel repo).precedenceBefore ≠ (f t sel repo).precedenceAfter →
      (f t sel repo).actingOrderBefore ≠ (f t sel repo).actingOrderAfter ∨
      (f t sel repo).scoreBefore ≠ (f t sel repo).scoreAfter

/-- F12 slice 13 task 2: `CascadeDiff` witness using `zaifAdmittedFor` from `F12AdmittingArm.lean:48` and repository authorship directly. -/
def organiseCascadeDiff {Policy Score : Type*} [Inhabited Score] :
    armTwoOrganiseType Policy Nat Score :=
  fun _ sel repo =>
    let nodes := sel ∪ zaifAdmittedFor sel
    { selected := sel
      nodes := nodes
      addedByOrganise := ∅
      admittedBy := zaifAdmittedFor sel
      authoredEdges := repo.standsOn
      organisedEdges := fastForward nodes repo.standsOn
      precedenceBefore := []
      precedenceAfter := []
      actingOrderBefore := []
      actingOrderAfter := []
      scoreBefore := default
      scoreAfter := default }

/-- F12 slice 13 task 2: the natural witness satisfies O1--O4 and both fidelity clauses. -/
theorem organiseCascadeDiffConformant {Policy Score : Type*} [Inhabited Score] :
    ConformantOrganiseCascadeDiff
      (organiseCascadeDiff (Policy := Policy) (Score := Score)) where
  osel := by intros; rfl
  oauth := by intros; rfl
  o1 := by intros; simp [organiseCascadeDiff]
  o2 := by
    intro t sel repo u v hedge
    exact d1_reachOutside_to_reach hedge.2.2
  o3 := by intros; rfl
  o4 := by intros; contradiction

/-- F12 slice 13 task 2 recorded execution: the witness returns `d1Nodes` from `F12D1Arms.lean:23`. -/
theorem organiseCascadeDiffZaifNodes :
    (organiseCascadeDiff (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo).nodes = d1Nodes := by
  ext n
  simp [organiseCascadeDiff, zaifAdmittedFor, d1Selected, d1Admitted, d1Nodes]
  omega

/-- F12 slice 13 task 2 recorded execution: the witness retains the selected argument from `F12D1Arms.lean:17`. -/
theorem organiseCascadeDiffZaifSelected :
    (organiseCascadeDiff (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo).selected = d1Selected := rfl

/-- F12 slice 13 task 2 recorded execution: the witness returns the nine admissions through `zaifAdmittedFor` at `F12AdmittingArm.lean:48`. -/
theorem organiseCascadeDiffZaifAdmitted :
    (organiseCascadeDiff (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo).admittedBy = d1Admitted := by
  simp [organiseCascadeDiff, zaifAdmittedFor]

/-- F12 slice 13 task 3 non-vacuity: the witness contains recorded organised edge `18 → 19` from `F12D1Arms.lean:165`. -/
theorem organiseCascadeDiffZaifEdge :
    (organiseCascadeDiff (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo).organisedEdges 18 19 := by
  have hmem : ∀ n : Nat, n < 20 → n ∈ d1Selected ∪ zaifAdmittedFor d1Selected := by
    intro n hn
    simp [zaifAdmittedFor, d1Selected, d1Admitted]
    omega
  exact ⟨hmem 18 (by omega), hmem 19 (by omega), ReachOutside.direct (by trivial)⟩

/-- F12 slice 13 task 3 negative non-vacuity: unauthored pair `0 → 1` is absent, as in `F12D1Arms.lean:174`. -/
theorem organiseCascadeDiffNoUnauthoredEdge :
    ¬ (organiseCascadeDiff (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo).organisedEdges 0 1 := by
  intro hedge
  have hrank := reach_increases_rank d1Authored d1Rank d1_authored_increases_rank
    (d1_reachOutside_to_reach hedge.2.2)
  simp [d1Rank] at hrank

/-- F12 slice 13 task 4(a): at any input whose two precedence fields agree, the O4 implication from `Holes.lean:916-921` holds regardless of acting order and score. -/
theorem o4VacuousWhenPrecedenceFlat {Policy P Score : Type*}
    (f : armTwoOrganiseType Policy P Score) (t : Cascade Policy)
    (sel : Set P) (repo : Repository P)
    (hflat : (f t sel repo).precedenceBefore = (f t sel repo).precedenceAfter) :
    (f t sel repo).precedenceBefore ≠ (f t sel repo).precedenceAfter →
      (f t sel repo).actingOrderBefore ≠ (f t sel repo).actingOrderAfter ∨
      (f t sel repo).scoreBefore ≠ (f t sel repo).scoreAfter := by
  intro h
  exact False.elim (h hflat)

/-- F12 slice 13 task 4(b): explicit conformance predicate with only O4 removed from `ConformantOrganiseCascadeDiff`. -/
structure ConformantOrganiseCascadeDiffSansO4 {Policy P Score : Type*}
    (f : armTwoOrganiseType Policy P Score) : Prop where
  osel : ∀ t sel repo, (f t sel repo).selected = sel
  oauth : ∀ t sel repo, (f t sel repo).authoredEdges = repo.standsOn
  o1 : ∀ t sel repo, (f t sel repo).nodes =
    sel ∪ (f t sel repo).addedByOrganise ∪ (f t sel repo).admittedBy
  o2 : ∀ t sel repo u v, (f t sel repo).organisedEdges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo u v, (f t sel repo).organisedEdges u v ↔
    fastForward (f t sel repo).nodes repo.standsOn u v

/-- F12 slice 13 task 4(b): the natural witness satisfies the committed sans-O4 predicate. -/
theorem organiseCascadeDiffConformantSansO4 {Policy Score : Type*} [Inhabited Score] :
    ConformantOrganiseCascadeDiffSansO4
      (organiseCascadeDiff (Policy := Policy) (Score := Score)) := by
  have h := organiseCascadeDiffConformant (Policy := Policy) (Score := Score)
  exact ⟨h.osel, h.oauth, h.o1, h.o2, h.o3⟩

/-- F12 slice 13 task 4(b): second recorded-shape witness differs only in acting-order-after and score-after, fields not exercised when precedence is flat at `Holes.lean:974-984`. -/
def organiseCascadeDiffRecordedVariant {Policy : Type*} :
    armTwoOrganiseType Policy Nat Int :=
  fun _ sel repo =>
    let nodes := sel ∪ zaifAdmittedFor sel
    { selected := sel, nodes := nodes, addedByOrganise := ∅,
      admittedBy := zaifAdmittedFor sel, authoredEdges := repo.standsOn,
      organisedEdges := fastForward nodes repo.standsOn,
      precedenceBefore := [], precedenceAfter := [],
      actingOrderBefore := [], actingOrderAfter := [0],
      scoreBefore := 0, scoreAfter := 1 }

/-- F12 slice 13 task 4(b): the field-varying witness remains conformant with O4 because its precedence antecedent is false. -/
theorem organiseCascadeDiffRecordedVariantConformant {Policy : Type*} :
    ConformantOrganiseCascadeDiff
      (organiseCascadeDiffRecordedVariant (Policy := Policy)) where
  osel := by intros; rfl
  oauth := by intros; rfl
  o1 := by intros; simp [organiseCascadeDiffRecordedVariant]
  o2 := by
    intro t sel repo u v hedge
    exact d1_reachOutside_to_reach hedge.2.2
  o3 := by intros; rfl
  o4 := by intros; contradiction

/-- F12 slice 13 task 4(b): the field-varying witness also satisfies the sans-O4 predicate. -/
theorem organiseCascadeDiffRecordedVariantConformantSansO4 {Policy : Type*} :
    ConformantOrganiseCascadeDiffSansO4
      (organiseCascadeDiffRecordedVariant (Policy := Policy)) := by
  have h := organiseCascadeDiffRecordedVariantConformant (Policy := Policy)
  exact ⟨h.osel, h.oauth, h.o1, h.o2, h.o3⟩

/-- F12 slice 13 task 4(b): at recorded inputs the two conformant functions agree on structural fields while the variant changes only acting-order-after and score-after. -/
theorem recordedVariantsExposeO4Vacuity :
    let a := organiseCascadeDiff (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo
    let b := organiseCascadeDiffRecordedVariant (Policy := Unit)
      trivialPolicyCascade d1Selected d1Repo
    a.nodes = b.nodes ∧ a.organisedEdges = b.organisedEdges ∧
      a.precedenceBefore = b.precedenceBefore ∧ a.precedenceAfter = b.precedenceAfter ∧
      a.actingOrderAfter ≠ b.actingOrderAfter ∧ a.scoreAfter ≠ b.scoreAfter := by
  simp [organiseCascadeDiff, organiseCascadeDiffRecordedVariant]

/-- F12 slice 13 task 4(c): counterexample with changed precedence but flat acting order and score, isolating the O4 clause from `Holes.lean:916-921`. -/
def organiseCascadeDiffO4Counterexample {Policy : Type*} :
    armTwoOrganiseType Policy Nat Int :=
  fun _ sel repo =>
    let nodes := sel ∪ zaifAdmittedFor sel
    { selected := sel, nodes := nodes, addedByOrganise := ∅,
      admittedBy := zaifAdmittedFor sel, authoredEdges := repo.standsOn,
      organisedEdges := fastForward nodes repo.standsOn,
      precedenceBefore := [], precedenceAfter := [0],
      actingOrderBefore := [], actingOrderAfter := [],
      scoreBefore := 0, scoreAfter := 0 }

/-- F12 slice 13 task 4(c): every clause other than O4 holds for the O4 counterexample. -/
theorem o4CounterexampleOtherClauses {Policy : Type*} :
    ConformantOrganiseCascadeDiffSansO4
      (organiseCascadeDiffO4Counterexample (Policy := Policy)) where
  osel := by intros; rfl
  oauth := by intros; rfl
  o1 := by intros; simp [organiseCascadeDiffO4Counterexample]
  o2 := by
    intro t sel repo u v hedge
    exact d1_reachOutside_to_reach hedge.2.2
  o3 := by intros; rfl

/-- F12 slice 13 task 4(c): the counterexample is not fully conformant, and the preceding theorem locates the failure exactly at O4. -/
theorem o4CounterexampleNotConformant :
    ¬ ConformantOrganiseCascadeDiff
      (organiseCascadeDiffO4Counterexample (Policy := Unit)) := by
  intro h
  have ho4 := h.o4 trivialPolicyCascade d1Selected d1Repo (by simp [organiseCascadeDiffO4Counterexample])
  simp [organiseCascadeDiffO4Counterexample] at ho4

/-- F12 slice 13 task 5: explicit predicate with only `oauth` removed; O2 and O3 still refer directly to the repository argument. -/
structure ConformantOrganiseCascadeDiffSansOAuth {Policy P Score : Type*}
    (f : armTwoOrganiseType Policy P Score) : Prop where
  osel : ∀ t sel repo, (f t sel repo).selected = sel
  o1 : ∀ t sel repo, (f t sel repo).nodes =
    sel ∪ (f t sel repo).addedByOrganise ∪ (f t sel repo).admittedBy
  o2 : ∀ t sel repo u v, (f t sel repo).organisedEdges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo u v, (f t sel repo).organisedEdges u v ↔
    fastForward (f t sel repo).nodes repo.standsOn u v
  o4 : ∀ t sel repo,
    (f t sel repo).precedenceBefore ≠ (f t sel repo).precedenceAfter →
      (f t sel repo).actingOrderBefore ≠ (f t sel repo).actingOrderAfter ∨
      (f t sel repo).scoreBefore ≠ (f t sel repo).scoreAfter

/-- F12 slice 13 task 5 refutation of the packet expectation: even without `oauth`, O2 itself forbids every organised edge unreachable in the supplied repository. -/
theorem sansOAuthStillForcesRepositoryReachability {Policy P Score : Type*}
    {f : armTwoOrganiseType Policy P Score}
    (hf : ConformantOrganiseCascadeDiffSansOAuth f) :
    ∀ t sel repo u v, (f t sel repo).organisedEdges u v → Reach repo.standsOn u v :=
  hf.o2

/-- F12 slice 13 task 5 witness: without `oauth`, the result's `authoredEdges` field can drift to the empty relation even though O2/O3 remain repository-relative. -/
def organiseCascadeDiffUnpinnedAuthored {Policy : Type*} :
    armTwoOrganiseType Policy Nat Int :=
  fun _ sel repo =>
    let nodes := sel ∪ zaifAdmittedFor sel
    { selected := sel, nodes := nodes, addedByOrganise := ∅,
      admittedBy := zaifAdmittedFor sel, authoredEdges := fun _ _ => False,
      organisedEdges := fastForward nodes repo.standsOn,
      precedenceBefore := [], precedenceAfter := [],
      actingOrderBefore := [], actingOrderAfter := [], scoreBefore := 0, scoreAfter := 0 }

/-- F12 slice 13 task 5: the drifting-authorship witness satisfies every sans-`oauth` clause. -/
theorem organiseCascadeDiffUnpinnedAuthoredSansOAuth {Policy : Type*} :
    ConformantOrganiseCascadeDiffSansOAuth
      (organiseCascadeDiffUnpinnedAuthored (Policy := Policy)) where
  osel := by intros; rfl
  o1 := by intros; simp [organiseCascadeDiffUnpinnedAuthored]
  o2 := by
    intro t sel repo u v hedge
    exact d1_reachOutside_to_reach hedge.2.2
  o3 := by intros; rfl
  o4 := by intros; contradiction

/-- F12 slice 13 task 5 concrete cost: on recorded inputs the drifting field denies authored edge `18 → 19` even though the repository and organised edge relation contain it. -/
theorem unpinnedAuthoredFieldDriftsAtRecordedEdge :
    ¬ (organiseCascadeDiffUnpinnedAuthored (Policy := Unit)
      trivialPolicyCascade d1Selected d1Repo).authoredEdges 18 19 ∧
    d1Repo.standsOn 18 19 ∧
    (organiseCascadeDiffUnpinnedAuthored (Policy := Unit)
      trivialPolicyCascade d1Selected d1Repo).organisedEdges 18 19 := by
  exact ⟨by simp [organiseCascadeDiffUnpinnedAuthored], by trivial,
    organiseCascadeDiffZaifEdge⟩

/-- F12 slice 13 task 5: restoring `oauth` rejects the drifting-authorship witness at recorded edge `18 → 19`. -/
theorem unpinnedAuthoredNotFullyConformant :
    ¬ ConformantOrganiseCascadeDiff
      (organiseCascadeDiffUnpinnedAuthored (Policy := Unit)) := by
  intro h
  have ha := congrFun (congrFun (h.oauth trivialPolicyCascade d1Selected d1Repo) 18) 19
  simp [organiseCascadeDiffUnpinnedAuthored, d1Repo, d1Authored] at ha

/-- F12 slice 13 task 6: one recorded execution discharges O1--O4 plus selected and authored-relation fidelity, with no `hrepo` argument of the kind used at `F12D1Arms.lean:106-113`. -/
theorem cascadeDiffRecordedAllLaws :
    ConformantOrganiseCascadeDiff
      (organiseCascadeDiff (Policy := Unit) (Score := Int)) ∧
    (organiseCascadeDiff (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo).nodes = d1Nodes ∧
    (organiseCascadeDiff (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo).admittedBy = d1Admitted ∧
    (organiseCascadeDiff (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo).organisedEdges 18 19 :=
  ⟨organiseCascadeDiffConformant, organiseCascadeDiffZaifNodes,
    organiseCascadeDiffZaifAdmitted, organiseCascadeDiffZaifEdge⟩


/-- F12 slice 13 REVIEW ADDITION, what the `Score` parameter actually costs.
C550 and the registry entry record arm two's price as "a `Score` type parameter
the declared signature does not have" (`F12D1Arms.lean:119` against
`Holes.lean:861`), which reads as a notational inconvenience.  It is not only
that.  `organise`'s declared type has an implementation at every instantiation --
`organiseSelectedOnly` (`F12Conformance.lean:59`) is one, whatever `Policy` and
`P` are.  This arm's type does not: at `Score := Empty` it is EMPTY, because a
total function at this signature has to produce two `Score` values on inputs that
carry none, and the recorded run carries none
(`futon3:checks/construct_cascade.clj:402`, fields at
`futon3:checks/construct_cascade.clj:420-421`).  That is why the witness above
takes `[Inhabited Score]` and writes `default` twice.  So the parameter is not
free notation: it adds a proof obligation to the interface. -/
theorem cascadeDiffArmIsEmptyAtAnEmptyScore :
    ¬ Nonempty (armTwoOrganiseType Unit Nat Empty) := by
  rintro ⟨f⟩
  exact (f trivialPolicyCascade d1Selected d1Repo).scoreBefore.elim

/-- F12 slice 13 REVIEW ADDITION, the comparand that makes the previous theorem a
cost rather than a curiosity: the declared `organise` signature
(`F12Conformance.lean:19`) is inhabited at the same argument types. -/
theorem organiseTypeIsInhabitedAtTheSameArguments :
    Nonempty (OrganiseType Unit Nat) :=
  ⟨organiseSelectedOnly⟩

/-- F12 slice 13 REVIEW ADDITION: overwrite the result's `authoredEdges` field
with the repository's relation, changing nothing else. -/
def pinAuthored {Policy P Score : Type*} (f : armTwoOrganiseType Policy P Score) :
    armTwoOrganiseType Policy P Score :=
  fun t sel repo => { f t sel repo with authoredEdges := repo.standsOn }

/-- F12 slice 13 REVIEW ADDITION: pinning touches the `authoredEdges` field and
none of the other eleven `CascadeDiff` fields (`Holes.lean:846-858`). -/
theorem pinAuthoredAgreesOutsideAuthoredEdges {Policy P Score : Type*}
    (f : armTwoOrganiseType Policy P Score) (t : Cascade Policy) (sel : Set P)
    (repo : Repository P) :
    (pinAuthored f t sel repo).selected = (f t sel repo).selected ∧
    (pinAuthored f t sel repo).nodes = (f t sel repo).nodes ∧
    (pinAuthored f t sel repo).addedByOrganise = (f t sel repo).addedByOrganise ∧
    (pinAuthored f t sel repo).admittedBy = (f t sel repo).admittedBy ∧
    (pinAuthored f t sel repo).organisedEdges = (f t sel repo).organisedEdges ∧
    (pinAuthored f t sel repo).precedenceBefore = (f t sel repo).precedenceBefore ∧
    (pinAuthored f t sel repo).precedenceAfter = (f t sel repo).precedenceAfter ∧
    (pinAuthored f t sel repo).actingOrderBefore = (f t sel repo).actingOrderBefore ∧
    (pinAuthored f t sel repo).actingOrderAfter = (f t sel repo).actingOrderAfter ∧
    (pinAuthored f t sel repo).scoreBefore = (f t sel repo).scoreBefore ∧
    (pinAuthored f t sel repo).scoreAfter = (f t sel repo).scoreAfter :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- F12 slice 13 REVIEW ADDITION, the positive form of
`sansOAuthStillForcesRepositoryReachability`.  That theorem refutes the
expectation that dropping `oauth` lets O2/O3 be satisfied against a self-chosen
relation.  This says what `oauth` DOES do, and it is less than it looks: any
function conformant without it becomes conformant with it by overwriting the one
field, and by `pinAuthoredAgreesOutsideAuthoredEdges` that overwrite changes
nothing else the laws read.  So at this framing `oauth` constrains no behaviour
of `organise` -- it pins a result field that no other clause mentions, because
O2 and O3 read the repository ARGUMENT.  That is a difference from the
value-grain O2 in `Holes.lean:1000-1004`, which reads `.authoredEdges` because
there is no repository in scope to read instead.  The honest reading of the
twelfth field at this arm is therefore: carried, and unread by the laws. -/
theorem pinAuthoredIsConformant {Policy P Score : Type*}
    {f : armTwoOrganiseType Policy P Score}
    (hf : ConformantOrganiseCascadeDiffSansOAuth f) :
    ConformantOrganiseCascadeDiff (pinAuthored f) where
  osel := hf.osel
  oauth := fun _ _ _ => rfl
  o1 := hf.o1
  o2 := hf.o2
  o3 := hf.o3
  o4 := hf.o4

/-- F12 slice 13 REVIEW ADDITION, the recorded instance: pinning repairs the very
witness `unpinnedAuthoredNotFullyConformant` rejects, so that rejection is about
the field's VALUE and not about anything the function computes. -/
theorem pinAuthoredRepairsTheDriftingWitness {Policy : Type*} :
    ConformantOrganiseCascadeDiff
      (pinAuthored (organiseCascadeDiffUnpinnedAuthored (Policy := Policy))) :=
  pinAuthoredIsConformant organiseCascadeDiffUnpinnedAuthoredSansOAuth

end

end DarkTower.WarMachine.Holes
