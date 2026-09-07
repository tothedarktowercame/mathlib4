import DarkTower.WarMachine.F12AdmittingArm

/-! # F12 attribution-input arm

This module runs the arm that supplies per-pattern admission provenance as an
explicit organise input.  It does not amend the refused implementation at
`Holes.lean:861` or choose an interface.
-/

open Set

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- F12 slice 8 rule id from the recorded zaif provenance map: this type is a singleton because the record names exactly one rule id, not because one rule is sufficient generally.  Consequently this run cannot distinguish an emitting-rule attribution from an admitted/not-admitted flag. -/
inductive ZaifRule where
  | widenTheCascadeOnlyOnEvidence
  deriving DecidableEq

/-- F12 slice 8 transcription of `zaif-cascade.edn` provenance: precisely indices 11 through 19 carry the recorded rule from `F12D1Arms.lean:19`. -/
def zaifProvenance (n : Nat) : Option ZaifRule :=
  if 11 ≤ n ∧ n < 20 then some .widenTheCascadeOnlyOnEvidence else none

/-- F12 slice 8 support check against `d1Admitted` at `F12D1Arms.lean:19`. -/
theorem zaifProvenanceSupport :
    {n | (zaifProvenance n).isSome} = d1Admitted := by
  ext n
  simp [zaifProvenance, d1Admitted]

/-- F12 slice 8 selected-silence check against `d1Selected` at `F12D1Arms.lean:16`. -/
theorem zaifProvenanceSilentOnSelected :
    ∀ n ∈ d1Selected, zaifProvenance n = none := by
  intro n hn
  simp [d1Selected] at hn
  simp [zaifProvenance]
  omega

/-- F12 slice 8 signature: `AdmittingOrganiseType` at `F12AdmittingArm.lean:17` with exactly one provenance-map input added. -/
abbrev AttributingOrganiseType (Policy P Rule : Type*) :=
  Cascade Policy → Set P → Repository P → (P → Option Rule) → ArmOneCascade P

/-- F12 slice 8 conformance extends the four clauses at `F12AdmittingArm.lean:21-30` with exactly `oattr`, retaining returned-nodes O3. -/
structure ConformantOrganiseAttributing {Policy P Rule : Type*}
    (f : AttributingOrganiseType Policy P Rule) : Prop where
  osel : ∀ t sel repo prov, (f t sel repo prov).selected = sel
  o1 : ∀ t sel repo prov,
    (f t sel repo prov).nodes = sel ∪ (f t sel repo prov).addedByOrganise ∪
      (f t sel repo prov).admittedBy
  o2 : ∀ t sel repo prov u v,
    (f t sel repo prov).edges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo prov u v,
    (f t sel repo prov).edges u v ↔
      fastForward (f t sel repo prov).nodes repo.standsOn u v
  oattr : ∀ t sel repo prov,
    (f t sel repo prov).admittedBy = {p | (prov p).isSome}

/-- F12 slice 8 natural attribution-input witness, preserving slice 7's node-based fast-forward at `F12AdmittingArm.lean:52`. -/
def organiseAttributing {Policy P Rule : Type*} :
    AttributingOrganiseType Policy P Rule :=
  fun _ sel repo prov =>
    let admitted := {p | (prov p).isSome}
    { nodes := sel ∪ ∅ ∪ admitted
      addedByOrganise := ∅
      edges := fastForward (sel ∪ ∅ ∪ admitted) repo.standsOn
      acyclic := fastForward_acyclic (sel ∪ ∅ ∪ admitted) repo.standsOn repo.acyclic
      precedence := []
      selected := sel
      admittedBy := admitted }

/-- F12 slice 8 proof of all five clauses for `organiseAttributing`. -/
theorem organiseAttributingConformant {Policy P Rule : Type*} :
    ConformantOrganiseAttributing
      (organiseAttributing (Policy := Policy) (P := P) (Rule := Rule)) where
  osel := by intro t sel repo prov; rfl
  o1 := by intro t sel repo prov; simp [organiseAttributing]
  o2 := by
    intro t sel repo prov u v edge
    exact d1_reachOutside_to_reach edge.2.2
  o3 := by intro t sel repo prov u v; rfl
  oattr := by intro t sel repo prov; rfl

/-- F12 slice 8 recorded support execution from `F12D1Arms.lean:19`: the natural attribution witness returns exactly the nine admitted nodes. -/
theorem organiseAttributingZaifAdmitsNine :
    (organiseAttributing (Policy := Unit) trivialPolicyCascade d1Selected d1Repo
      zaifProvenance).admittedBy = d1Admitted := by
  exact zaifProvenanceSupport

/-- F12 slice 8 recorded node execution from `F12D1Arms.lean:16-23`: selected plus provenance-supported admissions is exactly the twenty-node carrier. -/
theorem organiseAttributingZaifNodes :
    (organiseAttributing (Policy := Unit) trivialPolicyCascade d1Selected d1Repo
      zaifProvenance).nodes = d1Nodes := by
  ext n
  simp [organiseAttributing, zaifProvenance, d1Selected, d1Nodes]
  omega

/-- F12 slice 8 mirror of `F12AdmittingArm.lean:87`: provenance-supported nodes are filed under `addedByOrganise` and `admittedBy` is empty. -/
def organiseAttributingMirror {Policy P Rule : Type*} :
    AttributingOrganiseType Policy P Rule :=
  fun _ sel repo prov =>
    let attributed := {p | (prov p).isSome}
    { nodes := sel ∪ attributed ∪ ∅
      addedByOrganise := attributed
      edges := fastForward (sel ∪ attributed ∪ ∅) repo.standsOn
      acyclic := fastForward_acyclic (sel ∪ attributed ∪ ∅) repo.standsOn repo.acyclic
      precedence := []
      selected := sel
      admittedBy := ∅ }

/-- F12 slice 8 rejection of the slice-7 mirror conformance at `F12AdmittingArm.lean:98`: `oattr` fails at recorded admitted vertex 11. -/
theorem attributingMirrorNotConformant :
    ¬ ConformantOrganiseAttributing
      (organiseAttributingMirror (Policy := Unit) (P := Nat) (Rule := ZaifRule)) := by
  intro h
  have hattr := h.oattr trivialPolicyCascade d1Selected d1Repo zaifProvenance
  have h11 := Set.ext_iff.mp hattr 11
  simp [organiseAttributingMirror, zaifProvenance] at h11

/-- F12 slice 8 determination price: `oattr` cheaply makes `admittedBy` a projection of the new provenance argument.  Determination is bought by enlarging the argument list, not discovered; the singleton `ZaifRule` record cannot test per-rule identity beyond an admitted flag. -/
theorem attributingThirdOriginDetermined {Policy P Rule : Type*}
    {f g : AttributingOrganiseType Policy P Rule}
    (hf : ConformantOrganiseAttributing f)
    (hg : ConformantOrganiseAttributing g)
    (t : Cascade Policy) (sel : Set P) (repo : Repository P)
    (prov : P → Option Rule) :
    (f t sel repo prov).admittedBy = (g t sel repo prov).admittedBy := by
  rw [hf.oattr, hg.oattr]

/-- F12 slice 8 recorded-input price: every conformant function must return exactly `d1Admitted` from the transcribed provenance support at `F12D1Arms.lean:19`. -/
theorem attributingRecordedAdmissions {Policy : Type*}
    {f : AttributingOrganiseType Policy Nat ZaifRule}
    (hf : ConformantOrganiseAttributing f) (t : Cascade Policy) :
    (f t d1Selected d1Repo zaifProvenance).admittedBy = d1Admitted := by
  rw [hf.oattr]
  exact zaifProvenanceSupport

/-- F12 slice 8 recorded policy-grain input: the singleton rule-id node comes from `zaif-cascade.edn :temperaments :shared-nodes`; empty edges use the acyclicity shape at `F12Conformance.lean:99`. -/
def zaifPolicyCascade : Cascade ZaifRule where
  nodes := {.widenTheCascadeOnlyOnEvidence}
  addedByOrganise := ∅
  edges := fun _ _ => False
  acyclic := by intro x path; cases path with | single h => exact h | tail p h => exact h
  precedence := []

/-- F12 slice 8 temperament refutation: the two slice-7 witnesses at `F12AdmittingArm.lean:52,87` remain conformant for `Policy := ZaifRule` yet disagree at admitted vertex 11, so the existing policy cascade does not supply the run's rule-to-pattern map. -/
theorem attributionNotFixedByTemperament :
    ConformantOrganiseAdmitting (organiseAdmitting (Policy := ZaifRule)) ∧
      ConformantOrganiseAdmitting (organiseAdmittingMirror (Policy := ZaifRule)) ∧
      (organiseAdmitting zaifPolicyCascade d1Selected d1Repo).admittedBy ≠
        (organiseAdmittingMirror zaifPolicyCascade d1Selected d1Repo).admittedBy := by
  refine ⟨organiseAdmittingConformant, organiseAdmittingMirrorConformant, ?_⟩
  intro h
  have h11 := Set.ext_iff.mp h 11
  simp [organiseAdmitting, organiseAdmittingMirror, zaifAdmittedFor,
    d1Admitted] at h11

end


end DarkTower.WarMachine.Holes
