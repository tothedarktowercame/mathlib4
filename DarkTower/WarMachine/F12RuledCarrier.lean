import DarkTower.WarMachine.F12CascadeDiffArm
import DarkTower.WarMachine.F12O3FieldArm

/-! # F12 ruled organise carrier

The ruled carrier combines the `CascadeDiff` codomain with an explicit support
attribution input and the no-bootstrap O3 reading.
-/

open Set

namespace DarkTower.WarMachine.Holes

noncomputable section

abbrev RuledOrganiseType (Policy P Score : Type*) :=
  Cascade Policy → Set P → Repository P → Set P → CascadeDiff P Score

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

theorem noBootstrapCarrier_eq_selected_admitted {Policy P Score : Type*}
    {f : RuledOrganiseType Policy P Score} (hf : ConformantOrganiseRuled f)
    (t : Cascade Policy) (sel : Set P) (repo : Repository P) (adm : Set P)
    (hempty : (f t sel repo adm).addedByOrganise = ∅) :
    (f t sel repo adm).nodes \ (f t sel repo adm).addedByOrganise = sel ∪ adm := by
  rw [hempty, diff_empty, hf.o1, hempty, hf.oattr]
  simp

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

theorem organiseRuledZaifNodes :
    (organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).nodes = d1Nodes := by
  ext n; simp [organiseRuled, d1Selected, d1Admitted, d1Nodes]; omega

theorem organiseRuledZaifSelected :
    (organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).selected = d1Selected := rfl

theorem organiseRuledZaifAdmitted :
    (organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).admittedBy = d1Admitted := rfl

theorem organiseRuledZaifEdge :
    (organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).organisedEdges 18 19 := by
  exact ⟨by simp [d1Admitted], by simp [d1Admitted], ReachOutside.direct (by trivial)⟩

theorem organiseRuledZaifO4AntecedentFalse :
    ¬ ((organiseRuled (Policy := Unit) (Score := Int)
      trivialPolicyCascade d1Selected d1Repo d1Admitted).precedenceBefore ≠
      (organiseRuled (Policy := Unit) (Score := Int)
        trivialPolicyCascade d1Selected d1Repo d1Admitted).precedenceAfter) := by
  simp [organiseRuled]

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

def organiseRuledO4Counterexample {Policy : Type*} : RuledOrganiseType Policy Nat Int :=
  fun _ sel repo adm =>
    { selected := sel, nodes := sel ∪ adm, addedByOrganise := ∅, admittedBy := adm
      authoredEdges := repo.standsOn, organisedEdges := fastForward (sel ∪ adm) repo.standsOn
      precedenceBefore := [], precedenceAfter := [0]
      actingOrderBefore := [], actingOrderAfter := [], scoreBefore := 0, scoreAfter := 0 }

theorem organiseRuledO4CounterexampleOtherClauses {Policy : Type*} :
    ConformantOrganiseRuledSansO4 (organiseRuledO4Counterexample (Policy := Policy)) where
  osel := by intros; rfl
  oauth := by intros; rfl
  oattr := by intros; rfl
  o1 := by intros; simp [organiseRuledO4Counterexample]
  o2 := by intro _ _ _ _ _ _ h; exact d1_reachOutside_to_reach h.2.2
  o3 := by intros; simp [organiseRuledO4Counterexample]

theorem organiseRuledO4CounterexampleNotConformant :
    ¬ ConformantOrganiseRuled (organiseRuledO4Counterexample (Policy := Unit)) := by
  intro h
  simpa [organiseRuledO4Counterexample] using
    h.o4 trivialPolicyCascade d1Selected d1Repo d1Admitted

def organiseRuledMisfiled {Policy : Type*} : RuledOrganiseType Policy Nat Int :=
  fun _ sel repo adm =>
    { selected := sel, nodes := sel ∪ adm, addedByOrganise := adm, admittedBy := ∅
      authoredEdges := repo.standsOn, organisedEdges := fastForward sel repo.standsOn
      precedenceBefore := [], precedenceAfter := [], actingOrderBefore := [], actingOrderAfter := []
      scoreBefore := 0, scoreAfter := 0 }

theorem organiseRuledMisfiledNotConformant :
    ¬ ConformantOrganiseRuled (organiseRuledMisfiled (Policy := Unit)) := by
  intro h
  have := Set.ext_iff.mp (h.oattr trivialPolicyCascade d1Selected d1Repo d1Admitted) 11
  simp [organiseRuledMisfiled, d1Admitted] at this

def organiseRuledIgnoresAttribution {Policy : Type*} : RuledOrganiseType Policy Nat Int :=
  fun t sel repo _ => organiseRuledO4Counterexample (Policy := Policy) t sel repo ∅

theorem organiseRuledIgnoresAttributionNotConformant :
    ¬ ConformantOrganiseRuled (organiseRuledIgnoresAttribution (Policy := Unit)) := by
  intro h
  have := Set.ext_iff.mp (h.oattr trivialPolicyCascade d1Selected d1Repo d1Admitted) 11
  simp [organiseRuledIgnoresAttribution, organiseRuledO4Counterexample, d1Admitted] at this

def organiseRuledOwnBootstrap {Policy : Type*} : RuledOrganiseType Policy Nat Int :=
  fun _ sel repo adm =>
    let added : Set Nat := {20}
    let nodes := sel ∪ added ∪ adm
    { selected := sel, nodes := nodes, addedByOrganise := added, admittedBy := adm
      authoredEdges := repo.standsOn, organisedEdges := fastForward nodes repo.standsOn
      precedenceBefore := [], precedenceAfter := [], actingOrderBefore := [], actingOrderAfter := []
      scoreBefore := 0, scoreAfter := 0 }

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
