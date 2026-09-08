import DarkTower.WarMachine.F12CascadeDiffArm
import DarkTower.WarMachine.F12O3FieldArm

/-! # F12 ruled organise carrier

The ruled carrier combines the `CascadeDiff` codomain with an explicit support
attribution input and the no-bootstrap O3 reading.
-/

open Set

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- The candidate action space supplied to selection and to `organise`.  It is
the existing `Set P` argument given a name, not a second carrier beside it. -/
abbrev CandidateActionSpace (P : Type*) := Set P

/-- F12 slice 4a, the ruled signature: Joe's ARM 6 ruling of 2026-09-07 (`futon2:holes/labs/wm-contract/RULINGS-walkthrough-2026-09-07.md` item 4) takes arm two's `CascadeDiff` codomain from `DarkTower/WarMachine/F12D1Arms.lean:119`, and his ARM 4 ruling (item 9) adds the support-grain `Set P` attribution argument from `DarkTower/WarMachine/F12SupportArm.lean:26`. -/
abbrev RuledOrganiseType (Policy P Score : Type*) :=
  Cascade Policy → CandidateActionSpace P → Repository P → Set P → CascadeDiff P Score

/-- F12 slice 4a, the ruled conformance predicate.  `osel`, `oauth`, `o1`, `o2` and `o4` are arm six's clauses from `DarkTower/WarMachine/F12CascadeDiffArm.lean:16-27`; `oattr` is arm four's from `DarkTower/WarMachine/F12SupportArm.lean:38`; `o3` is the no-bootstrap reading ruled at item 6, in slice 11's shape from `DarkTower/WarMachine/F12O3FieldArm.lean:20-22`. -/
structure ConformantOrganiseRuled {Policy P Score : Type*}
    (f : RuledOrganiseType Policy P Score) : Prop where
  osel : ∀ t sel repo adm, (f t sel repo adm).selected = sel
  oauth : ∀ t sel repo adm, (f t sel repo adm).authoredEdges = repo.standsOn
  oattr : ∀ t sel repo adm, (f t sel repo adm).admittedBy = adm
  o1 : ∀ t sel repo adm, (f t sel repo adm).nodes =
    sel ∪ (f t sel repo adm).addedByOrganise ∪ (f t sel repo adm).admittedBy
  o2 : ∀ t sel repo adm u v,
    (f t sel repo adm).organisedEdges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo adm u v, (f t sel repo adm).organisedEdges u v ↔
    fastForward ((f t sel repo adm).nodes \ (f t sel repo adm).addedByOrganise)
      repo.standsOn u v
  o4 : ∀ t sel repo adm,
    (f t sel repo adm).precedenceBefore ≠ (f t sel repo adm).precedenceAfter →
      (f t sel repo adm).actingOrderBefore ≠ (f t sel repo adm).actingOrderAfter ∨
      (f t sel repo adm).scoreBefore ≠ (f t sel repo adm).scoreAfter

/-- F12 slice 4a: Joe's own reading of the no-bootstrap set at this carrier, verbatim from item 6 -- "At the ruled CascadeDiff carrier the set is `selected u admittedBy`" -- derived from `o1` and `oattr` rather than assumed. -/
theorem noBootstrapCarrier_eq_selected_admitted {Policy P Score : Type*}
    {f : RuledOrganiseType Policy P Score} (hf : ConformantOrganiseRuled f)
    (t : Cascade Policy) (sel : Set P) (repo : Repository P) (adm : Set P)
    (hempty : (f t sel repo adm).addedByOrganise = ∅) :
    (f t sel repo adm).nodes \ (f t sel repo adm).addedByOrganise = sel ∪ adm := by
  rw [hempty, diff_empty, hf.o1, hempty, hf.oattr]
  simp

/-- F12 slice 4a witness at the ruled signature.  It differs from `organiseCascadeDiff` at `DarkTower/WarMachine/F12CascadeDiffArm.lean:31` in exactly the way arm four's ruling requires: `admittedBy` comes from the attribution ARGUMENT, not from `zaifAdmittedFor`. -/
def organiseRuled {Policy P Score : Type*} [Inhabited Score] :
    RuledOrganiseType Policy P Score :=
  fun _ sel repo adm =>
    { selected := sel
      nodes := sel ∪ adm
      addedByOrganise := ∅
      admittedBy := adm
      authoredEdges := repo.standsOn
      organisedEdges := fastForward (sel ∪ adm) repo.standsOn
      precedenceBefore := [], precedenceAfter := []
      actingOrderBefore := [], actingOrderAfter := []
      scoreBefore := default, scoreAfter := default }

/-- F12 slice 4a: the witness satisfies all seven ruled clauses. -/
theorem organiseRuledConformant {Policy P Score : Type*} [Inhabited Score] :
    ConformantOrganiseRuled (organiseRuled (Policy := Policy) (P := P) (Score := Score)) where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; simp [organiseRuled]
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; simp [organiseRuled]
  o4 := by intros; contradiction

/-- This is the exact existential content intended for the later staged
`Holes.lean` amendment; that amendment is deliberately not made here. -/
theorem exists_conformantOrganiseRuled (Policy P Score : Type*) [Inhabited Score] :
    ∃ f : RuledOrganiseType Policy P Score, ConformantOrganiseRuled f :=
  ⟨organiseRuled, organiseRuledConformant⟩

/-- F12 slice 4a recorded execution: the witness returns the recorded twenty nodes `d1Nodes` from `DarkTower/WarMachine/F12D1Arms.lean:23`. -/
theorem organiseRuledZaifNodes :
    (organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).nodes = d1Nodes := by
  ext n; simp [organiseRuled, d1Selected, d1Admitted, d1Nodes]; omega

/-- F12 slice 4a recorded execution: the witness retains the eleven selected nodes `d1Selected` from `DarkTower/WarMachine/F12D1Arms.lean:17`. -/
theorem organiseRuledZaifSelected :
    (organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).selected = d1Selected := rfl

/-- F12 slice 4a recorded execution: the witness returns the nine recorded admissions `d1Admitted` from `DarkTower/WarMachine/F12D1Arms.lean:20`, and under the ruled signature they arrive as the ARGUMENT rather than through a lookup table. -/
theorem organiseRuledZaifAdmitted :
    (organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).admittedBy = d1Admitted := rfl

/-- F12 slice 4a recorded execution: the witness carries the recorded organised edge 18 -> 19 from `DarkTower/WarMachine/F12D1Arms.lean:165`. -/
theorem organiseRuledZaifEdge :
    (organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).organisedEdges 18 19 := by
  exact ⟨by simp [d1Admitted], by simp [d1Admitted], ReachOutside.direct (by trivial)⟩

/-- F12 slice 4a: O4's antecedent is false at the witness's recorded instantiation, so the ruled O4 clause is UNEXERCISED there.  Read on its own this is only a fact about the witness, which writes both precedence fields as `[]`; `organiseRuledZaifPrecedenceIsTheRecordedOne` below is what makes it a fact about the run. -/
theorem organiseRuledZaifO4AntecedentFalse :
    ¬ ((organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).precedenceBefore ≠
      (organiseRuled (Policy := Unit) (Score := Int)
        trivialPolicyCascade d1Selected d1Repo d1Admitted).precedenceAfter) := by
  simp [organiseRuled]

/-- F12 slice 4a: the witness does not CHOOSE its flat precedence -- both its fields equal the recorded zaif fixture's at `DarkTower/WarMachine/Holes.lean:981-982`, which is where the flatness comes from: `futon3:checks/construct_cascade.clj:402` writes both vectors as `[]` literals (fields at `futon3:checks/construct_cascade.clj:420-421`). -/
theorem organiseRuledZaifPrecedenceIsTheRecordedOne :
    (organiseRuled (Policy := Unit) (Score := Int)
        trivialPolicyCascade d1Selected d1Repo d1Admitted).precedenceBefore =
      wmZaifCascadeDiffFixture.precedenceBefore ∧
    (organiseRuled (Policy := Unit) (Score := Int)
        trivialPolicyCascade d1Selected d1Repo d1Admitted).precedenceAfter =
      wmZaifCascadeDiffFixture.precedenceAfter := ⟨rfl, rfl⟩

/-- F12 slice 4a, what this slice does NOT witness: on the one library-scale run recorded, O4's antecedent is false in the RECORD -- `armTwoO4AntecedentUnsatisfiable` at `DarkTower/WarMachine/F12D1Arms.lean:120`.  The exemplar Joe's ARM 6 ruling commissions (item 4: a real recorded run whose precedence moves and carries a score) is therefore still owed, and is slice 4b's, not this slice's. -/
theorem ruledO4UnexercisedOnTheRecordedRun :
    ¬ (wmZaifCascadeDiffFixture.precedenceBefore ≠
      wmZaifCascadeDiffFixture.precedenceAfter) :=
  armTwoO4AntecedentUnsatisfiable

/-- F12 slice 4a: the ruled predicate with only `o4` removed, so the O4 counterexample's failure can be located at `o4` alone.  Model: `DarkTower/WarMachine/F12CascadeDiffArm.lean:111`. -/
structure ConformantOrganiseRuledSansO4 {Policy P Score : Type*}
    (f : RuledOrganiseType Policy P Score) : Prop where
  osel : ∀ t sel repo adm, (f t sel repo adm).selected = sel
  oauth : ∀ t sel repo adm, (f t sel repo adm).authoredEdges = repo.standsOn
  oattr : ∀ t sel repo adm, (f t sel repo adm).admittedBy = adm
  o1 : ∀ t sel repo adm, (f t sel repo adm).nodes = sel ∪
    (f t sel repo adm).addedByOrganise ∪ (f t sel repo adm).admittedBy
  o2 : ∀ t sel repo adm u v, (f t sel repo adm).organisedEdges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo adm u v, (f t sel repo adm).organisedEdges u v ↔
    fastForward ((f t sel repo adm).nodes \ (f t sel repo adm).addedByOrganise) repo.standsOn u v

/-- F12 slice 4a: a function whose precedence moves while acting order and score stay flat, so O4's antecedent fires and its conclusion fails. -/
def organiseRuledO4Counterexample {Policy : Type*} : RuledOrganiseType Policy Nat Int :=
  fun _ sel repo adm =>
    { selected := sel, nodes := sel ∪ adm, addedByOrganise := ∅, admittedBy := adm
      authoredEdges := repo.standsOn, organisedEdges := fastForward (sel ∪ adm) repo.standsOn
      precedenceBefore := [], precedenceAfter := [0]
      actingOrderBefore := [], actingOrderAfter := [], scoreBefore := 0, scoreAfter := 0 }

/-- F12 slice 4a: every ruled clause other than `o4` holds of the counterexample. -/
theorem organiseRuledO4CounterexampleOtherClauses {Policy : Type*} :
    ConformantOrganiseRuledSansO4 (organiseRuledO4Counterexample (Policy := Policy)) where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; simp [organiseRuledO4Counterexample]
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; simp [organiseRuledO4Counterexample]

/-- F12 slice 4a: the counterexample is not ruled-conformant, and the preceding theorem places the failure at `o4` alone -- so the ruled O4 clause is NOT vacuous in general, whatever any one run does to it. -/
theorem organiseRuledO4CounterexampleNotConformant :
    ¬ ConformantOrganiseRuled (organiseRuledO4Counterexample (Policy := Unit)) := by
  intro h
  simpa [organiseRuledO4Counterexample] using
    h.o4 trivialPolicyCascade d1Selected d1Repo d1Admitted

/-- F12 slice 4a negative control 1: a function that files the admissions under `addedByOrganise` and leaves `admittedBy` empty -- the misattribution the `:LA2` field amendment at `DarkTower/WarMachine/Holes.lean:833-845` added the field to prevent. -/
def organiseRuledMisfiled {Policy : Type*} : RuledOrganiseType Policy Nat Int :=
  fun _ sel repo adm =>
    { selected := sel, nodes := sel ∪ adm, addedByOrganise := adm, admittedBy := ∅
      authoredEdges := repo.standsOn, organisedEdges := fastForward sel repo.standsOn
      precedenceBefore := [], precedenceAfter := [], actingOrderBefore := [], actingOrderAfter := []
      scoreBefore := 0, scoreAfter := 0 }

/-- F12 slice 4a negative control 1 is caught, at recorded vertex 11, by `oattr`. -/
theorem organiseRuledMisfiledNotConformant :
    ¬ ConformantOrganiseRuled (organiseRuledMisfiled (Policy := Unit)) := by
  intro h
  have := Set.ext_iff.mp (h.oattr trivialPolicyCascade d1Selected d1Repo d1Admitted) 11
  simp [organiseRuledMisfiled, d1Admitted] at this

/-- F12 slice 4a negative control 2: a function that discards the attribution argument.  This is what arm four's input buys over arm six, so a predicate that did not catch it would not be the ruled one. -/
def organiseRuledIgnoresAttribution {Policy : Type*} : RuledOrganiseType Policy Nat Int :=
  fun t sel repo _ => organiseRuledO4Counterexample (Policy := Policy) t sel repo ∅

/-- F12 slice 4a negative control 2 is caught, at recorded vertex 11, by `oattr`. -/
theorem organiseRuledIgnoresAttributionNotConformant :
    ¬ ConformantOrganiseRuled (organiseRuledIgnoresAttribution (Policy := Unit)) := by
  intro h
  have := Set.ext_iff.mp (h.oattr trivialPolicyCascade d1Selected d1Repo d1Admitted) 11
  simp [organiseRuledIgnoresAttribution, organiseRuledO4Counterexample, d1Admitted] at this

/-- F12 slice 4a negative control 3: a function that adds node 20 itself and then fast-forwards THROUGH its own addition.  This is the control that separates the ruled no-bootstrap `o3` from the node-set reading at `DarkTower/WarMachine/F12CascadeDiffArm.lean:23`, which admits it. -/
def organiseRuledOwnBootstrap {Policy : Type*} : RuledOrganiseType Policy Nat Int :=
  fun _ sel repo adm =>
    let added : Set Nat := {20}
    let nodes := sel ∪ added ∪ adm
    { selected := sel, nodes := nodes, addedByOrganise := added, admittedBy := adm
      authoredEdges := repo.standsOn, organisedEdges := fastForward nodes repo.standsOn
      precedenceBefore := [], precedenceAfter := [], actingOrderBefore := [], actingOrderAfter := []
      scoreBefore := 0, scoreAfter := 0 }

/-- F12 slice 4a: the ruled predicate with only `o3` removed, so negative control 3's failure can be located at `o3` alone.  Without it the control refutes conformance without showing WHICH clause did the refuting, which is the difference between a control and a coincidence. -/
structure ConformantOrganiseRuledSansO3 {Policy P Score : Type*}
    (f : RuledOrganiseType Policy P Score) : Prop where
  osel : ∀ t sel repo adm, (f t sel repo adm).selected = sel
  oauth : ∀ t sel repo adm, (f t sel repo adm).authoredEdges = repo.standsOn
  oattr : ∀ t sel repo adm, (f t sel repo adm).admittedBy = adm
  o1 : ∀ t sel repo adm, (f t sel repo adm).nodes = sel ∪
    (f t sel repo adm).addedByOrganise ∪ (f t sel repo adm).admittedBy
  o2 : ∀ t sel repo adm u v, (f t sel repo adm).organisedEdges u v → Reach repo.standsOn u v
  o4 : ∀ t sel repo adm,
    (f t sel repo adm).precedenceBefore ≠ (f t sel repo adm).precedenceAfter →
      (f t sel repo adm).actingOrderBefore ≠ (f t sel repo adm).actingOrderAfter ∨
      (f t sel repo adm).scoreBefore ≠ (f t sel repo adm).scoreAfter

/-- F12 slice 4a: every ruled clause other than `o3` holds of negative control 3, so its refutation below is the no-bootstrap reading doing the work and nothing else. -/
theorem organiseRuledOwnBootstrapOtherClauses {Policy : Type*} :
    ConformantOrganiseRuledSansO3 (organiseRuledOwnBootstrap (Policy := Policy)) where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; simp [organiseRuledOwnBootstrap]
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o4 := by intros; contradiction

/-- F12 slice 4a negative control 3 is caught by the no-bootstrap `o3`: node 20 is gone from `nodes \ addedByOrganise`, so the recorded edge 19 -> 20 it claims has no fast-forward endpoint. -/
theorem organiseRuledOwnBootstrapNotConformant :
    ¬ ConformantOrganiseRuled (organiseRuledOwnBootstrap (Policy := Unit)) := by
  intro h
  have ho3 := h.o3 trivialPolicyCascade d1Selected d1Repo d1Admitted 19 20
  have hedge : (organiseRuledOwnBootstrap (Policy := Unit)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).organisedEdges 19 20 := by
    exact ⟨by simp [d1Admitted],
      by simp, ReachOutside.direct (by trivial)⟩
  have := ho3.mp hedge
  have hv := this.2.1
  simp [organiseRuledOwnBootstrap] at hv

end

end DarkTower.WarMachine.Holes
