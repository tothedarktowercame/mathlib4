import DarkTower.WarMachine.F12AttributionArm

/-! # F12 support-grain attribution input

This module runs C547 §6's support-grain arm.  It measures the arm and its
relation to the rule-grain input without choosing either interface.
-/

open Set Classical

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- F12 slice 10 support erased from the rule-grain input at `F12AttributionArm.lean:48-64`. -/
def provSupport {P Rule : Type*} (prov : P → Option Rule) : Set P :=
  {p | (prov p).isSome}

/-- F12 slice 10 definitional check that `provSupport` is exactly the set pinned by slice 8's `oattr` at `F12AttributionArm.lean:63-64`. -/
theorem mem_provSupport_iff {P Rule : Type*} (prov : P → Option Rule) (p : P) :
    p ∈ provSupport prov ↔ (prov p).isSome := by rfl

/-- F12 slice 10 support-grain signature, replacing slice 8's rule-valued argument at `F12AttributionArm.lean:48-49` by its support. -/
abbrev SupportOrganiseType (Policy P : Type*) :=
  Cascade Policy → Set P → Repository P → Set P → ArmOneCascade P

/-- F12 slice 10 support conformance copies `F12AttributionArm.lean:51-64`, replacing only `oattr` by equality with the support argument. -/
structure ConformantOrganiseSupport {Policy P : Type*}
    (f : SupportOrganiseType Policy P) : Prop where
  osel : ∀ t sel repo adm, (f t sel repo adm).selected = sel
  o1 : ∀ t sel repo adm,
    (f t sel repo adm).nodes = sel ∪ (f t sel repo adm).addedByOrganise ∪
      (f t sel repo adm).admittedBy
  o2 : ∀ t sel repo adm u v,
    (f t sel repo adm).edges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo adm u v,
    (f t sel repo adm).edges u v ↔ fastForward (f t sel repo adm).nodes repo.standsOn u v
  oattr : ∀ t sel repo adm, (f t sel repo adm).admittedBy = adm

/-- F12 slice 10 natural support witness, counterpart of `organiseAttributing` at `F12AttributionArm.lean:66-77`. -/
def organiseSupport {Policy P : Type*} : SupportOrganiseType Policy P :=
  fun _ sel repo adm =>
    { nodes := sel ∪ ∅ ∪ adm
      addedByOrganise := ∅
      edges := fastForward (sel ∪ ∅ ∪ adm) repo.standsOn
      acyclic := fastForward_acyclic (sel ∪ ∅ ∪ adm) repo.standsOn repo.acyclic
      precedence := []
      selected := sel
      admittedBy := adm }

/-- F12 slice 10 proves all five support-conformance clauses for the natural witness. -/
theorem organiseSupportConformant {Policy P : Type*} :
    ConformantOrganiseSupport (organiseSupport (Policy := Policy) (P := P)) where
  osel := by intros; rfl
  o1 := by intros; simp [organiseSupport]
  o2 := by
    intro _ _ _ _ _ _ hedge
    exact d1_reachOutside_to_reach hedge.2.2
  o3 := by intros; rfl
  oattr := by intros; rfl

/-- F12 slice 10 mirror of `F12AttributionArm.lean:84-95`, filing the support under `addedByOrganise`. -/
def organiseSupportMirror {Policy P : Type*} : SupportOrganiseType Policy P :=
  fun _ sel repo adm =>
    { nodes := sel ∪ adm ∪ ∅
      addedByOrganise := adm
      edges := fastForward (sel ∪ adm ∪ ∅) repo.standsOn
      acyclic := fastForward_acyclic (sel ∪ adm ∪ ∅) repo.standsOn repo.acyclic
      precedence := []
      selected := sel
      admittedBy := ∅ }

/-- F12 slice 10 rejects the support mirror at vertex 11, counterpart of `attributingMirrorNotConformant` at `F12AttributionArm.lean:119`. -/
theorem supportMirrorNotConformant :
    ¬ ConformantOrganiseSupport (organiseSupportMirror (Policy := Unit) (P := Nat)) := by
  intro h
  have ha := h.oattr trivialPolicyCascade d1Selected d1Repo d1Admitted
  have h11 := Set.ext_iff.mp ha 11
  simp [organiseSupportMirror, d1Admitted] at h11

/-- F12 slice 10 determination: `oattr` makes every two conformant functions agree on `admittedBy`. -/
theorem supportThirdOriginDetermined {Policy P : Type*}
    {f g : SupportOrganiseType Policy P} (hf : ConformantOrganiseSupport f)
    (hg : ConformantOrganiseSupport g) (t : Cascade Policy) (sel : Set P)
    (repo : Repository P) (adm : Set P) :
    (f t sel repo adm).admittedBy = (g t sel repo adm).admittedBy := by
  rw [hf.oattr, hg.oattr]

/-- F12 slice 10 recorded execution: the natural support witness returns the nine admissions from `F12D1Arms.lean:19`. -/
theorem organiseSupportZaifAdmitsNine :
    (organiseSupport (Policy := Unit) trivialPolicyCascade d1Selected d1Repo d1Admitted).admittedBy = d1Admitted := rfl

/-- F12 slice 10 recorded execution: selected plus the supplied support gives `d1Nodes` from `F12D1Arms.lean:23`. -/
theorem organiseSupportZaifNodes :
    (organiseSupport (Policy := Unit) trivialPolicyCascade d1Selected d1Repo d1Admitted).nodes = d1Nodes := by
  ext n
  simp [organiseSupport, d1Selected, d1Admitted, d1Nodes]
  omega

/-- F12 slice 10 recorded price: every conformant support function returns the supplied `d1Admitted`. -/
theorem supportRecordedAdmissions {Policy : Type*} {f : SupportOrganiseType Policy Nat}
    (hf : ConformantOrganiseSupport f) (t : Cascade Policy) :
    (f t d1Selected d1Repo d1Admitted).admittedBy = d1Admitted := hf.oattr _ _ _ _

/-- F12 slice 10 committed deletion experiment: support conformance with `oattr` removed and all four other laws retained. -/
structure ConformantOrganiseSupportSansAttr {Policy P : Type*}
    (f : SupportOrganiseType Policy P) : Prop where
  osel : ∀ t sel repo adm, (f t sel repo adm).selected = sel
  o1 : ∀ t sel repo adm, (f t sel repo adm).nodes = sel ∪ (f t sel repo adm).addedByOrganise ∪ (f t sel repo adm).admittedBy
  o2 : ∀ t sel repo adm u v, (f t sel repo adm).edges u v → Reach repo.standsOn u v
  o3 : ∀ t sel repo adm u v, (f t sel repo adm).edges u v ↔ fastForward (f t sel repo adm).nodes repo.standsOn u v

/-- F12 slice 10 price measurement: without `oattr`, the natural and mirror functions satisfy the four laws, agree on nodes and edges, and disagree at admitted vertex 11. -/
theorem supportSplitSurvivesWithoutOattr :
    ConformantOrganiseSupportSansAttr (organiseSupport (Policy := Unit) (P := Nat)) ∧
    ConformantOrganiseSupportSansAttr (organiseSupportMirror (Policy := Unit) (P := Nat)) ∧
    (organiseSupport trivialPolicyCascade d1Selected d1Repo d1Admitted).nodes =
      (organiseSupportMirror trivialPolicyCascade d1Selected d1Repo d1Admitted).nodes ∧
    (organiseSupport trivialPolicyCascade d1Selected d1Repo d1Admitted).edges =
      (organiseSupportMirror trivialPolicyCascade d1Selected d1Repo d1Admitted).edges ∧
    (organiseSupport trivialPolicyCascade d1Selected d1Repo d1Admitted).admittedBy ≠
      (organiseSupportMirror trivialPolicyCascade d1Selected d1Repo d1Admitted).admittedBy := by
  refine ⟨?_, ?_, by simp [organiseSupport, organiseSupportMirror], by simp [organiseSupport, organiseSupportMirror], ?_⟩
  · exact ⟨by intros; rfl, by intros; simp [organiseSupport], by
      intro _ _ _ _ _ _ hedge
      exact d1_reachOutside_to_reach hedge.2.2, by intros; rfl⟩
  · exact ⟨by intros; rfl, by intros; simp [organiseSupportMirror], by
      intro _ _ _ _ _ _ hedge
      exact d1_reachOutside_to_reach hedge.2.2, by intros; rfl⟩
  · intro h; have h11 := Set.ext_iff.mp h 11; simp [organiseSupport, organiseSupportMirror, d1Admitted] at h11

/-- F12 slice 10 erases rule identity before calling a support-grain function, measured against `AttributingOrganiseType` at `F12AttributionArm.lean:48-49`. -/
def attributingOfSupport {Policy P Rule : Type*} (f : SupportOrganiseType Policy P) :
    AttributingOrganiseType Policy P Rule := fun t sel repo prov => f t sel repo (provSupport prov)

/-- F12 slice 10 forward comparison: support conformance transfers to rule-grain conformance after support erasure. -/
theorem attributingOfSupport_conformant {Policy P Rule : Type*} {f : SupportOrganiseType Policy P}
    (hf : ConformantOrganiseSupport f) : ConformantOrganiseAttributing (attributingOfSupport (Rule := Rule) f) :=
  ⟨by intros; apply hf.osel, by intros; apply hf.o1, by intros; apply hf.o2; assumption,
    by intros; apply hf.o3, by intros; apply hf.oattr⟩

/-- F12 slice 10 boolean indicator used to embed a support input into rule grain `Unit`. -/
def supportIndicator {P : Type*} (adm : Set P) (p : P) : Option Unit := if p ∈ adm then some () else none

/-- F12 slice 10 indicator support check needed for the reverse comparison. -/
theorem provSupport_supportIndicator {P : Type*} (adm : Set P) : provSupport (supportIndicator adm) = adm := by
  ext p; simp [provSupport, supportIndicator]

/-- F12 slice 10 turns a rule-grain `Unit` function into a support-grain function by the indicator at the requested argument list. -/
def supportOfAttributing {Policy P : Type*} (f : AttributingOrganiseType Policy P Unit) :
    SupportOrganiseType Policy P := fun t sel repo adm => f t sel repo (supportIndicator adm)

/-- F12 slice 10 reverse comparison: rule-grain conformance transfers through the support indicator. -/
theorem supportOfAttributing_conformant {Policy P : Type*} {f : AttributingOrganiseType Policy P Unit}
    (hf : ConformantOrganiseAttributing f) : ConformantOrganiseSupport (supportOfAttributing f) where
  osel := by intros; apply hf.osel
  o1 := by intros; apply hf.o1
  o2 := by intros; apply hf.o2; assumption
  o3 := by intros; apply hf.o3
  oattr := by
    intro t sel repo adm
    change (f t sel repo (supportIndicator adm)).admittedBy = adm
    rw [hf.oattr]
    exact provSupport_supportIndicator adm

/-- F12 slice 10 rule-blindness of the attributed field: equal supports force equal `admittedBy` for any conformant rule-grain function. -/
theorem attributingBlindToRuleIdentity {Policy P Rule : Type*}
    {f : AttributingOrganiseType Policy P Rule} (hf : ConformantOrganiseAttributing f)
    (t : Cascade Policy) (sel : Set P) (repo : Repository P) (prov1 prov2 : P → Option Rule)
    (hs : provSupport prov1 = provSupport prov2) :
    (f t sel repo prov1).admittedBy = (f t sel repo prov2).admittedBy := by
  rw [hf.oattr, hf.oattr]; exact hs

/-- F12 slice 10 counterfactual relabelling: the stop rule, which `zaifProvenanceNeverTheStopRule` says the recorded run never emits, labels exactly the same nine vertices. -/
def zaifProvenanceStopRelabelled (n : Nat) : Option ZaifPolicyRule :=
  if 11 ≤ n ∧ n < 20 then some .haltOnBudget else none

/-- F12 slice 10 proves the counterfactual relabelling has the recorded support. -/
theorem stopRelabelledSameSupport : provSupport zaifProvenanceStopRelabelled = provSupport zaifProvenance := by
  ext n; simp [provSupport, zaifProvenanceStopRelabelled, zaifProvenance]

/-- F12 slice 10 proves the counterfactual and recorded maps differ at admitted vertex 11. -/
theorem stopRelabelledDiffersAtEleven : zaifProvenanceStopRelabelled 11 ≠ zaifProvenance 11 := by decide

/-- F12 slice 10 non-vacuous blindness: any conformant attributing function returns `d1Admitted` for both recorded and counterfactual rule labels. -/
theorem stopRelabelledAdmissionsIndistinguishable {Policy : Type*}
    {f : AttributingOrganiseType Policy Nat ZaifPolicyRule} (hf : ConformantOrganiseAttributing f)
    (t : Cascade Policy) :
    (f t d1Selected d1Repo zaifProvenanceStopRelabelled).admittedBy = d1Admitted ∧
    (f t d1Selected d1Repo zaifProvenance).admittedBy = d1Admitted := by
  constructor <;> rw [hf.oattr]
  · exact stopRelabelledSameSupport.trans zaifProvenanceSupport
  · exact zaifProvenanceSupport

/-- F12 slice 10 rule-sensitive conformant witness: the stop-labelled subset is also filed under `addedByOrganise`, showing rule grain is readable outside `admittedBy`. -/
def organiseAttributingStopMarked {Policy P : Type*} : AttributingOrganiseType Policy P ZaifPolicyRule :=
  fun _ sel repo prov =>
    let adm := provSupport prov
    let stop := {p | prov p = some .haltOnBudget}
    { nodes := sel ∪ stop ∪ adm, addedByOrganise := stop,
      edges := fastForward (sel ∪ stop ∪ adm) repo.standsOn,
      acyclic := fastForward_acyclic _ _ repo.acyclic, precedence := [], selected := sel, admittedBy := adm }

/-- F12 slice 10 proves the stop-marking witness is attributing-conformant.  Each clause is `rfl`, and in particular O1 holds by the shape of the record and does NOT use the containment of the stop-labelled set in the support; that containment is proved separately below, where it is what the node agreement needs. -/
theorem organiseAttributingStopMarkedConformant {Policy P : Type*} :
    ConformantOrganiseAttributing (organiseAttributingStopMarked (Policy := Policy) (P := P)) where
  osel := by intros; rfl
  o1 := by intros; rfl
  o2 := by
    intro _ _ _ _ _ _ hedge
    exact d1_reachOutside_to_reach hedge.2.2
  o3 := by intros; rfl
  oattr := by intros; rfl

/-- F12 slice 10 honest cost measurement: stop-marking agrees with the natural witness on recorded provenance but differs on the counterfactual relabelling. -/
theorem stopMarkedRecordedFlatCounterfactualVisible :
    (organiseAttributingStopMarked (Policy := Unit) trivialPolicyCascade d1Selected d1Repo zaifProvenance).addedByOrganise =
      (organiseAttributing (Policy := Unit) trivialPolicyCascade d1Selected d1Repo zaifProvenance).addedByOrganise ∧
    (organiseAttributingStopMarked (Policy := Unit) trivialPolicyCascade d1Selected d1Repo zaifProvenanceStopRelabelled).addedByOrganise ≠
      (organiseAttributing (Policy := Unit) trivialPolicyCascade d1Selected d1Repo zaifProvenanceStopRelabelled).addedByOrganise := by
  constructor
  · ext n
    simp [organiseAttributingStopMarked, organiseAttributing, zaifProvenance]
  · intro h; have h11 := Set.ext_iff.mp h 11; simp [organiseAttributingStopMarked, organiseAttributing, zaifProvenanceStopRelabelled] at h11

/-- F12 slice 10 review addition: the edge agreement inside `supportSplitSurvivesWithoutOattr` is an agreement on an INHABITED relation and not on the empty one.  The edge is `18 → 19` (`F12D1Arms.lean:26-28`, the single entry of `runs/F12-organise/01-zaif-transcription.edn` `:fast-forward :over-nodes`); slice 7 (`F12AdmittingArm.lean:180`) and slice 8 (`F12AttributionArm.lean:198`) each had to add this for the same reason, and the support arm shipped without it. -/
theorem supportZaifEdgeNonVacuous :
    (organiseSupport (Policy := Unit) trivialPolicyCascade d1Selected d1Repo
        d1Admitted).edges 18 19 ∧
      (organiseSupportMirror (Policy := Unit) trivialPolicyCascade d1Selected d1Repo
        d1Admitted).edges 18 19 := by
  have hmem : ∀ n : Nat, n < 20 → n ∈ d1Selected ∪ d1Admitted := by
    intro n hn
    simp [d1Selected, d1Admitted]
    omega
  refine ⟨⟨?_, ?_, ReachOutside.direct trivial⟩, ⟨?_, ?_, ReachOutside.direct trivial⟩⟩ <;>
    simpa using hmem _ (by omega)

/-- F12 slice 10 review addition: the recorded execution routed through the TRANSCRIPTION rather than through the answer.  `supportRecordedAdmissions` above hands the arm `d1Admitted` itself, so it recovers the nine admissions from an input that already is them; this hands it the support of the recorded provenance map (`F12AttributionArm.lean:22`) and recovers them through `zaifProvenanceSupport` (`F12AttributionArm.lean:26`).  That is the support-grain counterpart of `attributingRecordedAdmissions` (`F12AttributionArm.lean:138`), which routes the same way. -/
theorem supportRecordedAdmissionsFromProvenance {Policy : Type*}
    {f : SupportOrganiseType Policy Nat} (hf : ConformantOrganiseSupport f)
    (t : Cascade Policy) :
    (f t d1Selected d1Repo (provSupport zaifProvenance)).admittedBy = d1Admitted := by
  rw [hf.oattr]
  exact zaifProvenanceSupport

/-- F12 slice 10 review addition: the indicator at an ARBITRARY rule.  `supportIndicator` above is fixed at `Unit`, and `Unit` is the one rule type at which the rule-grain input already carries no rule, so the reverse comparison proved there is the reverse comparison in the case where the two arms trivially coincide. -/
def supportIndicatorAt {P Rule : Type*} (r : Rule) (adm : Set P) (p : P) : Option Rule :=
  if p ∈ adm then some r else none

/-- F12 slice 10 review addition: the general indicator has the support it is built from. -/
theorem provSupport_supportIndicatorAt {P Rule : Type*} (r : Rule) (adm : Set P) :
    provSupport (supportIndicatorAt r adm) = adm := by
  ext p
  simp [provSupport, supportIndicatorAt]

/-- F12 slice 10 review addition: the reverse translation at an arbitrary rule. -/
def supportOfAttributingAt {Policy P Rule : Type*} (r : Rule)
    (f : AttributingOrganiseType Policy P Rule) : SupportOrganiseType Policy P :=
  fun t sel repo adm => f t sel repo (supportIndicatorAt r adm)

/-- F12 slice 10 review addition: rule-grain conformance transfers to support-grain conformance at ANY rule type that names a rule, not only at `Unit`.  With `attributingOfSupport_conformant` this is the arm's result -- the same determination on a strictly smaller input -- stated at the grain the recorded runs actually use. -/
theorem supportOfAttributingAt_conformant {Policy P Rule : Type*} (r : Rule)
    {f : AttributingOrganiseType Policy P Rule} (hf : ConformantOrganiseAttributing f) :
    ConformantOrganiseSupport (supportOfAttributingAt r f) where
  osel := by intros; apply hf.osel
  o1 := by intros; apply hf.o1
  o2 := by intros; apply hf.o2; assumption
  o3 := by intros; apply hf.o3
  oattr := by
    intro t sel repo adm
    change (f t sel repo (supportIndicatorAt r adm)).admittedBy = adm
    rw [hf.oattr]
    exact provSupport_supportIndicatorAt r adm

/-- F12 slice 10 review addition: the reverse translation at the RECORDED rule grain.  Every provenance entry in every cascade record under `futon3:checks` names one rule id, `:widen-the-cascade-only-on-evidence` -- 213 admissions over nine records, `:distinct-rule-ids-in-the-corpus 1` (`runs/F12-organise/06-attribution-arm.edn`, recomputed 2026-09-07) -- so this instance is the translation at the only grain any recorded run exhibits. -/
theorem supportOfAttributingAtRecordedRule_conformant {Policy P : Type*}
    {f : AttributingOrganiseType Policy P ZaifPolicyRule}
    (hf : ConformantOrganiseAttributing f) :
    ConformantOrganiseSupport
      (supportOfAttributingAt ZaifPolicyRule.widenTheCascadeOnlyOnEvidence f) :=
  supportOfAttributingAt_conformant _ hf

/-- F12 slice 10 review addition: the stop-labelled set is inside the provenance support. -/
theorem stopMarkedStopSubsetSupport {P : Type*} (prov : P → Option ZaifPolicyRule) :
    {p | prov p = some ZaifPolicyRule.haltOnBudget} ⊆ provSupport prov := by
  intro p hp
  have h : prov p = some ZaifPolicyRule.haltOnBudget := hp
  simp [provSupport, h]

/-- F12 slice 10 review addition: the stop-marking witness and the natural one return the SAME nodes at every input, so the difference `stopMarkedRecordedFlatCounterfactualVisible` reports is about where an admission is filed and not about which patterns entered.  Without this the counterfactual disagreement would be readable as two functions that admitted different things. -/
theorem stopMarkedAgreeOnNodes {Policy P : Type*} (t : Cascade Policy) (sel : Set P)
    (repo : Repository P) (prov : P → Option ZaifPolicyRule) :
    (organiseAttributingStopMarked t sel repo prov).nodes =
      (organiseAttributing t sel repo prov).nodes := by
  have hsub := stopMarkedStopSubsetSupport prov
  apply Set.Subset.antisymm
  · rintro p (hp | hp)
    · rcases hp with hp | hp
      · exact Or.inl (Or.inl hp)
      · exact Or.inr (hsub hp)
    · exact Or.inr hp
  · rintro p (hp | hp)
    · rcases hp with hp | hp
      · exact Or.inl (Or.inl hp)
      · exact hp.elim
    · exact Or.inr hp

end

end DarkTower.WarMachine.Holes
