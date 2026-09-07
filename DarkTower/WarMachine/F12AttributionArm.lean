import DarkTower.WarMachine.F12AdmittingArm

/-! # F12 attribution-input arm

This module runs the arm that supplies per-pattern admission provenance as an
explicit organise input.  It does not amend the refused implementation at
`Holes.lean:861` or choose an interface.
-/

open Set

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- F12 slice 8 policy-grain rule ids of the temperament that ran, from `futon3:checks/construct_cascade.clj:324-327`: `budgeted-temperament` has the two nodes `[:halt-on-budget :widen-the-cascade-only-on-evidence]`.  The record's `:temperaments :shared-nodes` reports ONE of them because `differ-only-in-the-stop` (`futon3:checks/construct_cascade.clj:338-349`) removes the stop rule before comparing the two temperaments; reading the temperament off that summary would have given the refutation below a weaker input than the recorded one.  Only the second constructor ever appears in a provenance entry, and that is `zaifProvenanceNeverTheStopRule` below rather than a remark: every admission in every provenance map under `futon3:checks` names that one rule, so this run cannot distinguish an emitting-rule attribution from an admitted/not-admitted flag. -/
inductive ZaifPolicyRule where
  | haltOnBudget
  | widenTheCascadeOnlyOnEvidence
  deriving DecidableEq

/-- F12 slice 8 transcription of `zaif-cascade.edn` provenance: precisely indices 11 through 19 carry the recorded rule from `F12D1Arms.lean:19`. -/
def zaifProvenance (n : Nat) : Option ZaifPolicyRule :=
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

/-- F12 slice 8 range check: the recorded provenance names one of the temperament's two nodes and never the stop rule, so the attribution the run carries is a proper part of the policy cascade rather than all of it. -/
theorem zaifProvenanceNeverTheStopRule :
    ∀ n, zaifProvenance n ≠ some ZaifPolicyRule.haltOnBudget := by
  intro n
  simp only [zaifProvenance]
  split <;> simp

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
      (organiseAttributingMirror (Policy := Unit) (P := Nat) (Rule := ZaifPolicyRule)) := by
  intro h
  have hattr := h.oattr trivialPolicyCascade d1Selected d1Repo zaifProvenance
  have h11 := Set.ext_iff.mp hattr 11
  simp [organiseAttributingMirror, zaifProvenance] at h11

/-- F12 slice 8 determination price: `oattr` cheaply makes `admittedBy` a projection of the new provenance argument.  Determination is bought by enlarging the argument list, not discovered; the singleton `ZaifPolicyRule` record cannot test per-rule identity beyond an admitted flag. -/
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
    {f : AttributingOrganiseType Policy Nat ZaifPolicyRule}
    (hf : ConformantOrganiseAttributing f) (t : Cascade Policy) :
    (f t d1Selected d1Repo zaifProvenance).admittedBy = d1Admitted := by
  rw [hf.oattr]
  exact zaifProvenanceSupport

/-- F12 slice 8 review addition: `ConformantOrganiseAttributing` at `F12AttributionArm.lean:44` with `oattr` removed and nothing else changed.  Control C2 planted this deletion and watched `attributingMirrorNotConformant` stop elaborating; a planted deletion is not something a later reader can cite, so the deletion is committed here as a predicate and the surviving split is proved of it. -/
structure ConformantOrganiseAttributingSansAttr {Policy P Rule : Type*}
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

/-- F12 slice 8 review addition: without `oattr` the natural witness still conforms. -/
theorem organiseAttributingConformantSansAttr {Policy P Rule : Type*} :
    ConformantOrganiseAttributingSansAttr
      (organiseAttributing (Policy := Policy) (P := P) (Rule := Rule)) where
  osel := by intro t sel repo prov; rfl
  o1 := by intro t sel repo prov; simp [organiseAttributing]
  o2 := by
    intro t sel repo prov u v edge
    exact d1_reachOutside_to_reach edge.2.2
  o3 := by intro t sel repo prov u v; rfl

/-- F12 slice 8 review addition: without `oattr` the mirror conforms too, which is what `attributingMirrorNotConformant` overturns once the clause is present. -/
theorem organiseAttributingMirrorConformantSansAttr {Policy P Rule : Type*} :
    ConformantOrganiseAttributingSansAttr
      (organiseAttributingMirror (Policy := Policy) (P := P) (Rule := Rule)) where
  osel := by intro t sel repo prov; rfl
  o1 := by intro t sel repo prov; simp [organiseAttributingMirror]
  o2 := by
    intro t sel repo prov u v edge
    exact d1_reachOutside_to_reach edge.2.2
  o3 := by intro t sel repo prov u v; rfl

/-- F12 slice 8 review addition: the two witnesses agree on the node set, so the disagreement below is about attribution and not about which patterns entered. -/
theorem attributingAgreeOnNodes {Policy P Rule : Type*}
    (t : Cascade Policy) (sel : Set P) (repo : Repository P) (prov : P → Option Rule) :
    (organiseAttributing t sel repo prov).nodes =
      (organiseAttributingMirror t sel repo prov).nodes := by
  simp [organiseAttributing, organiseAttributingMirror]

/-- F12 slice 8 review addition: the two witnesses agree on the whole edge relation O2 and O3 see. -/
theorem attributingAgreeOnEdges {Policy P Rule : Type*}
    (t : Cascade Policy) (sel : Set P) (repo : Repository P) (prov : P → Option Rule) :
    (organiseAttributing t sel repo prov).edges =
      (organiseAttributingMirror t sel repo prov).edges := by
  simp [organiseAttributing, organiseAttributingMirror]

/-- F12 slice 8 review addition: the recorded fast-forward edge `18 → 19` (`F12D1Arms.lean:26-28`, the single entry of `runs/F12-organise/01-zaif-transcription.edn` `:fast-forward :over-nodes`) is in the relation BOTH witnesses return on the recorded provenance, so `attributingAgreeOnEdges` is an agreement on an inhabited relation.  Slice 7's first spelling of the same agreement was provable by `rfl` with nothing anywhere saying the relation was non-empty. -/
theorem attributingZaifEdgeNonVacuous :
    (organiseAttributing (Policy := Unit) trivialPolicyCascade d1Selected d1Repo
        zaifProvenance).edges 18 19 ∧
      (organiseAttributingMirror (Policy := Unit) trivialPolicyCascade d1Selected d1Repo
        zaifProvenance).edges 18 19 := by
  have hmem : ∀ n : Nat, n < 20 → n ∈ d1Selected ∪ {p | (zaifProvenance p).isSome} := by
    intro n hn
    simp [zaifProvenance, d1Selected]
    omega
  refine ⟨⟨?_, ?_, ReachOutside.direct trivial⟩, ⟨?_, ?_, ReachOutside.direct trivial⟩⟩ <;>
    simpa using hmem _ (by omega)

/-- F12 slice 8 review addition, and the slice's actual content: at the WIDENED signature, with the provenance argument present and supplied with the recorded map, slice 7's split survives untouched as long as `oattr` is absent -- two functions conformant on the four laws, agreeing on nodes and on edges, disagreeing on admission at recorded vertex 11.  So it is the added clause and nothing else about the enlarged argument list that determines the third origin. -/
theorem attributingSplitSurvivesWithoutOattr :
    ConformantOrganiseAttributingSansAttr
        (organiseAttributing (Policy := Unit) (P := Nat) (Rule := ZaifPolicyRule)) ∧
      ConformantOrganiseAttributingSansAttr
        (organiseAttributingMirror (Policy := Unit) (P := Nat) (Rule := ZaifPolicyRule)) ∧
      (organiseAttributing trivialPolicyCascade d1Selected d1Repo zaifProvenance).admittedBy ≠
        (organiseAttributingMirror trivialPolicyCascade d1Selected d1Repo
          zaifProvenance).admittedBy := by
  refine ⟨organiseAttributingConformantSansAttr, organiseAttributingMirrorConformantSansAttr, ?_⟩
  intro h
  have h11 := Set.ext_iff.mp h 11
  simp [organiseAttributing, organiseAttributingMirror, zaifProvenance] at h11

/-- F12 slice 8 recorded policy-grain input: `budgeted-temperament` as it ran, both nodes and the recorded precedence order `{:halt-on-budget 1, :widen-the-cascade-only-on-evidence 2}` (`futon3:checks/construct_cascade.clj:324-327`).  It authors no edge between its rules, so the acyclicity shape at `F12Conformance.lean:99` carries over. -/
def zaifPolicyCascade : Cascade ZaifPolicyRule where
  nodes := {.haltOnBudget, .widenTheCascadeOnlyOnEvidence}
  addedByOrganise := ∅
  edges := fun _ _ => False
  acyclic := by intro x path; cases path with | single h => exact h | tail p h => exact h
  precedence := [.haltOnBudget, .widenTheCascadeOnlyOnEvidence]

/-- F12 slice 8 review addition, the general form of the refutation below: NO temperament fixes the attribution.  The recorded instance is one case of this, and the fact that the proof never reads `zaifPolicyCascade`'s nodes, edges or precedence is the content of the claim -- `Cascade Policy` carries a set of rule ids and nothing mapping a rule to the patterns it admitted, and that map is a run fact. -/
theorem attributionNotFixedByAnyTemperament :
    ∀ t : Cascade ZaifPolicyRule,
      (organiseAdmitting t d1Selected d1Repo).admittedBy ≠
        (organiseAdmittingMirror t d1Selected d1Repo).admittedBy := by
  intro t h
  have h11 := Set.ext_iff.mp h 11
  simp [organiseAdmitting, organiseAdmittingMirror, zaifAdmittedFor, d1Admitted] at h11

/-- F12 slice 8 temperament refutation at the RECORDED temperament: the two slice-7 witnesses at `F12AdmittingArm.lean:52,87` remain conformant for `Policy := ZaifPolicyRule` yet disagree at admitted vertex 11, so the policy cascade the type already takes does not supply the run's rule-to-pattern map. -/
theorem attributionNotFixedByTemperament :
    ConformantOrganiseAdmitting (organiseAdmitting (Policy := ZaifPolicyRule)) ∧
      ConformantOrganiseAdmitting (organiseAdmittingMirror (Policy := ZaifPolicyRule)) ∧
      (organiseAdmitting zaifPolicyCascade d1Selected d1Repo).admittedBy ≠
        (organiseAdmittingMirror zaifPolicyCascade d1Selected d1Repo).admittedBy := by
  refine ⟨organiseAdmittingConformant, organiseAdmittingMirrorConformant, ?_⟩
  intro h
  have h11 := Set.ext_iff.mp h 11
  simp [organiseAdmitting, organiseAdmittingMirror, zaifAdmittedFor,
    d1Admitted] at h11

end


end DarkTower.WarMachine.Holes
