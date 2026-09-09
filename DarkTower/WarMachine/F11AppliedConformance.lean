import DarkTower.WarMachine.F11RuledReadings

/-! # Named applied-carrier implementation: SnatchThreePatternRound2

Provenance: futon3/checks/find_snatch_choices.clj, its
checks/F11-find-comparison-manifest.edn (experimental/f11-find-comparison-manifest-v1),
and checks/find_snatch_evidence.clj:84-135. This is a named three-pattern
restriction of the g4/snatcher round-2 experiment, NOT a canonical carrier or
full 24-pattern replay. Clause is a nonempty collection of kind/label pairs;
AsOf carries scenario, round, state digest and source/manifest pins; TextCitation
carries the per-clause authored spans, bytes and pins as one citation bundle.

The model selects by the existing IF AND HOWEVER predicates (an absent
executable HOWEVER adds no test), without consulting the external designation.
It emits content from the manifest table. Expected content and citation validation
are independently declared below, not read back from emitted receipts. The
state digest is supplied in the input, as in the experiment's query binding;
this module proves no cryptographic hashing or live source-loading claim.
The named query supplies matching fires; arbitrary query.fires is not interpreted
as a second predicate override. The model's interpretation is the three guards below.

The claim is: a conformant implementation of the applied interface EXISTS at
this named instantiation. F2/F3 hold for every model input and repository;
F4 holds for every repository at the recorded query and its reviewer designation.
No claim is made that the same designation is appropriate to other states.
The proofs target FindResult predicates ONLY. No claim
about opaque find, correspondence axiom, unfolding, or marker retirement occurs.
-/
namespace DarkTower.WarMachine.Holes.F11AppliedConformance
open Set Classical
noncomputable section

inductive Pattern where
  | ask | repair | probe
  deriving DecidableEq, Repr

abbrev Clause := List (FindClauseKind × String)

structure SourcePin where
  file : String
  blob : String
  sha256 : String
  deriving DecidableEq

structure AsOf where
  scenario : String
  round : Nat
  stateDigest : String
  manifestDigest : String
  pins : List SourcePin
  deriving DecidableEq

structure TextSpan where
  pattern : Pattern
  kind : FindClauseKind
  file : String
  firstLine : Nat
  lastLine : Nat
  text : String
  blob : String
  sha256 : String
  deriving DecidableEq

abbrev TextCitation := List TextSpan

structure State where
  play : Bool
  tokens : Nat
  snatched : Bool
  repairObserved : Bool
  dispositionKnown : Bool
  seized : Nat
  stamp : AsOf

-- Executable IF/HOWEVER table from the pinned interpretation rows.
def eligible (s : State) : Pattern → Bool
  | .ask => s.play && decide (s.tokens > 0)
  | .repair => s.play && s.snatched && s.repairObserved &&
      decide (s.tokens > 0) && decide (s.seized = 0)
  | .probe => s.play && !s.dispositionKnown && decide (s.tokens > 1)

def emittedClauses : Pattern → Clause
  | .ask => [(.ifClause, "available-resources")]
  | .repair => [(.ifClause, "observed-repair-with-resources"), (.howeverClause, "seizure-cleared")]
  | .probe => [(.ifClause, "unknown-prior-response"), (.howeverClause, "resources-above-floor")]

def emittedCitations : Pattern → TextCitation
  | .ask => [⟨.ask, .ifClause, "library/snatch/ask-for-surplus-not-surrender.flexiarg", 16, 17, "    You are offering a positive number of your tokens and may still choose what\n    to ask in return.", "c6312c59e7e333a044043f571d7dfec27302af08", "d4b59fe05b98d0a3faa041714e0ea05a9ac11feaa1997efcff1da17db7288733"⟩]
  | .repair => [⟨.repair, .ifClause, "library/snatch/re-enter-after-observed-repair.flexiarg", 16, 17, "    The seized tokens were restored or compensated, the remedy is recorded, and\n    a small new offer can test whether play changed.", "1cba24a28107a89e3845a7b210e3791fd8dbe89b", "4293feb4d644d7d6661a622839b156ecc8a89e56a3bc3c66858a351a6feb30f6"⟩,
      ⟨.repair, .howeverClause, "library/snatch/re-enter-after-observed-repair.flexiarg", 20, 21, "    Permanent exit discards any improvement the institution achieved, while\n    re-entry on a promise alone repeats the original exposure.", "1cba24a28107a89e3845a7b210e3791fd8dbe89b", "4293feb4d644d7d6661a622839b156ecc8a89e56a3bc3c66858a351a6feb30f6"⟩]
  | .probe => [⟨.probe, .ifClause, "library/snatch/probe-before-committing.flexiarg", 17, 18, "    You face a counterpart whose disposition you do not know, and an offer of any\n    size is available to you.", "93747b0b114f96f65599ebfe48623307d3873686", "2e12af8463e82db8333157f79448b911ead1bcc71b5ca25e8510d8463757bdc9"⟩,
      ⟨.probe, .howeverClause, "library/snatch/probe-before-committing.flexiarg", 21, 22, "    A large first offer is unrecoverable if they snatch, and a zero offer buys\n    nothing — you end the round knowing exactly what you knew at its start.", "93747b0b114f96f65599ebfe48623307d3873686", "2e12af8463e82db8333157f79448b911ead1bcc71b5ca25e8510d8463757bdc9"⟩]

/-- Independent clause expectation from the pre-run manifest's query mappings.
    Pattern ids and clause labels are different types; no identity expectation. -/
def expectedClauses : Pattern → Clause
  | .ask => [(.ifClause, "available-resources")]
  | .repair => [(.ifClause, "observed-repair-with-resources"), (.howeverClause, "seizure-cleared")]
  | .probe => [(.ifClause, "unknown-prior-response"), (.howeverClause, "resources-above-floor")]

/-- Independent authored-source table, checked against source bytes when transcribed. -/
def authoredCitations : Pattern → TextCitation
  | .ask => [⟨.ask, .ifClause, "library/snatch/ask-for-surplus-not-surrender.flexiarg", 16, 17, "    You are offering a positive number of your tokens and may still choose what\n    to ask in return.", "c6312c59e7e333a044043f571d7dfec27302af08", "d4b59fe05b98d0a3faa041714e0ea05a9ac11feaa1997efcff1da17db7288733"⟩]
  | .repair => [⟨.repair, .ifClause, "library/snatch/re-enter-after-observed-repair.flexiarg", 16, 17, "    The seized tokens were restored or compensated, the remedy is recorded, and\n    a small new offer can test whether play changed.", "1cba24a28107a89e3845a7b210e3791fd8dbe89b", "4293feb4d644d7d6661a622839b156ecc8a89e56a3bc3c66858a351a6feb30f6"⟩,
      ⟨.repair, .howeverClause, "library/snatch/re-enter-after-observed-repair.flexiarg", 20, 21, "    Permanent exit discards any improvement the institution achieved, while\n    re-entry on a promise alone repeats the original exposure.", "1cba24a28107a89e3845a7b210e3791fd8dbe89b", "4293feb4d644d7d6661a622839b156ecc8a89e56a3bc3c66858a351a6feb30f6"⟩]
  | .probe => [⟨.probe, .ifClause, "library/snatch/probe-before-committing.flexiarg", 17, 18, "    You face a counterpart whose disposition you do not know, and an offer of any\n    size is available to you.", "93747b0b114f96f65599ebfe48623307d3873686", "2e12af8463e82db8333157f79448b911ead1bcc71b5ca25e8510d8463757bdc9"⟩,
      ⟨.probe, .howeverClause, "library/snatch/probe-before-committing.flexiarg", 21, 22, "    A large first offer is unrecoverable if they snatch, and a zero offer buys\n    nothing — you end the round knowing exactly what you knew at its start.", "93747b0b114f96f65599ebfe48623307d3873686", "2e12af8463e82db8333157f79448b911ead1bcc71b5ca25e8510d8463757bdc9"⟩]

def expected (s : State) (p : Pattern) : FindReceiptExpectation Clause AsOf :=
  ⟨.ifClause, expectedClauses p, .structuredAntecedent, s.stamp⟩

def validText (p : Pattern) (text : TextCitation) : Prop := text = authoredCitations p

/-- Real membership computation from repository membership and the three guards;
    receipts are emitted for the actual selected members. No designation input. -/
def model (q : FindQuery State Pattern) (R : Repository Pattern) :
    FindResult Pattern Clause AsOf TextCitation R :=
  { selected := {p | p ∈ R.patterns ∧ eligible q.tension.context p = true}
    receipts := fun p _ =>
      { clauseKind := .ifClause, acknowledgedClause := emittedClauses p
        route := .structuredAntecedent, asOf := q.tension.context.stamp
        citation := .patternText (emittedCitations p) }
    absence := if ∃ p ∈ R.patterns, eligible q.tension.context p = true
      then none else some .noPatternAddressesThisTension }

theorem modelContainment (q : FindQuery State Pattern) (R : Repository Pattern) :
    (model q R).selected ⊆ R.patterns := by
  intro p hp
  exact hp.1

theorem modelTypedAbsence (q : FindQuery State Pattern) (R : Repository Pattern)
    (h : (model q R).selected = ∅) :
    (model q R).absence = some .noPatternAddressesThisTension := by
  have hn : ¬ ∃ p ∈ R.patterns, eligible q.tension.context p = true := by
    rintro ⟨p, hr, he⟩
    have hp : p ∈ (model q R).selected := ⟨hr, he⟩
    rw [h] at hp
    exact hp
  simp [model, hn]

theorem modelContentF2 (q : FindQuery State Pattern) (R : Repository Pattern) :
    (model q R).contentF2 (expected q.tension.context) := by
  intro p hp
  cases p <;> simp [model, expected, emittedClauses, expectedClauses]

theorem modelCitationF3 (q : FindQuery State Pattern) (R : Repository Pattern) :
    (model q R).citationF3 validText := by
  intro p hp
  cases p <;> rfl

theorem modelClausesNonempty (p : Pattern) : emittedClauses p ≠ [] := by
  cases p <;> simp [emittedClauses]

def repository : Repository Pattern where
  patterns := Set.univ
  standsOn := fun _ _ => False
  acyclic := by
    intro x path
    cases path with
    | single h => exact h
    | tail _ h => exact h

def recordedStamp : AsOf :=
  ⟨"g4/snatcher", 2, "a8427cd0bdfd0c90c7991c5ee8bbf33de5289bd157307fbf2e3b8b777c0493e2",
   "3e65d6d50157255a119b16e0c8641b43f4f1720190a5d1001fe1ca97423670ca",
   [⟨"library/snatch/a-free-mark-is-always-worth-assigning.flexiarg", "15121ecaf3970e4ab4a4d0914f0b8323ccb411be", "90245f0c725bd1486dee752c4f9fccfb8f42b452c85654da35ba0f65fe25edb0"⟩,
    ⟨"library/snatch/accept-an-offer-that-beats-holding.flexiarg", "fd6f95bf1f0366ef640677c500f1b90ab8e23d2e", "3a2efbf7ccff4a1048921abd55ee598e3b3f482968c6611ea52f40aec822dc5e"⟩,
    ⟨"library/snatch/an-unmodelled-response-stops-the-line.flexiarg", "402f6db1435d6d0205679ff215c1e5f28d21fd5d", "a89918211d7700f73121c97decec2060d899131a80c3c2b865cf7ae79be8d00b"⟩,
    ⟨"library/snatch/ask-for-surplus-not-surrender.flexiarg", "c6312c59e7e333a044043f571d7dfec27302af08", "d4b59fe05b98d0a3faa041714e0ea05a9ac11feaa1997efcff1da17db7288733"⟩,
    ⟨"library/snatch/consult-the-remedy-before-exiting.flexiarg", "a050a12d2c3f02ddd876910fd675f16e7e0f761d", "6a01b7f17af02168f6a396722bd168aaf725428a0ae7447b5716c31c1cf5f221"⟩,
    ⟨"library/snatch/escalate-only-as-far-as-you-can-lose.flexiarg", "3b9be2691b438edd7739e5cea0386d13ad772bc0", "1a45d0aa5f3f25d3e8f30d9183c462ed05fe4c1317c7c8df82a87646b87ae05b"⟩,
    ⟨"library/snatch/exchange-when-both-sides-gain.flexiarg", "02ebe2f6c2cefa83a73128e2bc9e9d4b0c0d048f", "5f64f812b0ffc28ea3a31db93916fdd274aefc529fac09c48bb2babd20f3f7d9"⟩,
    ⟨"library/snatch/forced-play-needs-a-loss-floor.flexiarg", "041ae06749b3cc62267ce50a0f3a93ace36087c2", "4caa611c2fb20f6a700d1ebe294357807e472ee6b989bba4a6bc182a53362092"⟩,
    ⟨"library/snatch/grim-cuts-the-cascade-and-never-widens-it.flexiarg", "047a11c23a70253e6bac0174394ed33f34abe791", "1526f002ced1c4b93c59513272afa0e56cf9b38d8e9984efa9398f5c3c2e67c0"⟩,
    ⟨"library/snatch/have-a-temperament.flexiarg", "4e411f3d49c26df6664642de6fc00a5c73594b4d", "c78442dc9d8fd7cda018034f7ed639d5936efc586db6002d2f9e14e3ffbfdb10"⟩,
    ⟨"library/snatch/institutions-vary-by-position-and-force.flexiarg", "d3e57d665f6be3870e16c7186ad2593d1051d92f", "92fbccc8c41757fab2a087c993270bbd9b6f96fa0489e3dcd72fa1317d85c41a"⟩,
    ⟨"library/snatch/lead-with-the-exchange-rule.flexiarg", "d8bd4a8fb752985d1a5a3e687162b20cd5db375d", "341fa7e31cce51da7efa0463e7335982ca71df19a76b5b6c51cc2412e416bcee"⟩,
    ⟨"library/snatch/mark-without-force.flexiarg", "75b1976022782d95c00c45bc4298aba9b1ff43c3", "2bf4e20151c425bc49dd48f25b8fd90a67f95d8e63638d08f7f6f668345f125c"⟩,
    ⟨"library/snatch/non-binding-talk-still-moves-play.flexiarg", "cf9b2c1abc7e143f6ba8310ba8ba80495fa81671", "6790bfd9259ce7098e713826b1e7999e708d072583cf23d17b2f926fda40117f"⟩,
    ⟨"library/snatch/play-the-authored-order-first.flexiarg", "6bb19659d25b52c0b6a14345406d56b1b9be4959", "b21b7dd993ee1ad54cd66b4330b1ef6a2e111a682edd849f96bd384de1db1419"⟩,
    ⟨"library/snatch/preserve-the-right-to-abstain.flexiarg", "0f68d4df95e0b5875899f7ac27a54637e3e26043", "95de16a04f4b9b23d3e63eac614008337c0943fec86a4d65e8363c872f4ff862"⟩,
    ⟨"library/snatch/price-the-final-round-as-final.flexiarg", "e51c1b5bcbd5e88f1b0703c4b0656baf5236c7a6", "8ef954d197172721c081bb43cd1b8fdb2396589ddec9d91b50921a90328e3892"⟩,
    ⟨"library/snatch/probe-before-committing.flexiarg", "93747b0b114f96f65599ebfe48623307d3873686", "2e12af8463e82db8333157f79448b911ead1bcc71b5ca25e8510d8463757bdc9"⟩,
    ⟨"library/snatch/promote-the-remedy-before-the-exit.flexiarg", "72274f40973663768a0047ab2eb2dd5841e63b6a", "cad1c935a1e3fe753febd9b13d04359c040660186539ac3bb3336a2f3a4ccf6c"⟩,
    ⟨"library/snatch/protect-the-unprotected-move.flexiarg", "5e7a70a39eb9b2f8a7754679a88136f10cb3b76e", "b75cc3b81ed7b6955d39e91e89f5bcb9ed29d6393202a9ef01c23456a655bfb4"⟩,
    ⟨"library/snatch/re-enter-after-observed-repair.flexiarg", "1cba24a28107a89e3845a7b210e3791fd8dbe89b", "4293feb4d644d7d6661a622839b156ecc8a89e56a3bc3c66858a351a6feb30f6"⟩,
    ⟨"library/snatch/revert-then-invert.flexiarg", "97a6eb51efce9725c7df0f2339f61a6072cafb31", "f7c579980a27c61738290951bde788ab0ecd75808d9fdeaa03ce69d154ad6f1d"⟩,
    ⟨"library/snatch/use-talk-to-make-a-testable-offer.flexiarg", "8421c53a1a40c517993a56e461a267d2a4789f09", "b48a3edc5d9986c22fdd1672ecfd7c32130e3b04b772296923779b32574edc14"⟩,
    ⟨"library/snatch/widen-the-cascade-only-on-evidence.flexiarg", "a3b3b21b8b82957bf0ed491874954cabdfe05e8d", "2e879dd5b43db450d97fed2c0dfff0f8710196cb60b76e238e4516b6c15f8fd6"⟩,
    ⟨"checks/playout_snatch.clj", "90e9f65ae3d548842d7ea4df288eabac79c7e66d", "82770b78b422d5355c6abcf4fba0f757e7eefdbe48d84591236ab123f663dc59"⟩,
    ⟨"checks/find_snatch.clj", "0a43712bb8d2f8a378c14e09053239c4dab6b5ed", "35cde326e9cfcb03abeb4ec5401cbd7dbcc124bcc93e1e3a953d5dbe1d8da9ee"⟩,
    ⟨"checks/find_snatch_evidence.clj", "ca7ab9ea7eee38c13b637b29c8b2a967a14f0760", "b6b3d2547e47f862f35e9b12a934e679a54f24e2e9f343c3f4ef374c4b64a415"⟩,
    ⟨"checks/find_organise.clj", "c6ea2dd60f226bbf76d82e9bee4df9c0ad67fbef", "64c3abb4a5a8655736ffc6391cbf7cbae17a76cdc3e026cfc3e6adcf0da1d9ce"⟩,
    ⟨"checks/snatch-cascade.edn", "68a7c56597587440c21b90be49ad947dba9dc2dc", "00397dbe6fea4b58f63a13594bd9e4f53dbfa17a2a2cf0e07844c726e2e69069"⟩,
    ⟨"library/process-coherence/refusal-becomes-pattern.flexiarg", "141c4a741bee5485733bc2f62acb0a869d20b1ef", "34832402cab254934b22f00ce073fc1cdb3e1a4df3257c587b7f5676e3eb0223"⟩]⟩

/-- Projected fields of the committed g4/snatcher round-2 state. -/
def recordedState : State := ⟨true, 9, true, false, true, 1, recordedStamp⟩

def recordedQuery : FindQuery State Pattern :=
  { tension := ⟨recordedState, True, True⟩
    fires := fun p s => eligible s p = true }

/-- Reviewer-pinned external C designation, scoped here to recordedQuery. -/
def designation : Set Pattern := {.repair, .probe}

theorem modelSelectsAsk : Pattern.ask ∈ (model recordedQuery repository).selected := by
  simp [model, recordedQuery, recordedState, eligible, repository]

theorem modelNonempty : (model recordedQuery repository).selected.Nonempty :=
  ⟨.ask, modelSelectsAsk⟩

theorem modelExclusionF4 (R : Repository Pattern) :
    (model recordedQuery R).exclusionF4 designation := by
  intro p hp hr hs
  cases p <;> simp_all [designation, model, recordedQuery, recordedState, eligible]

theorem modelDiscriminatingF4 :
    (model recordedQuery repository).discriminatingF4 designation := by
  exact ⟨⟨.repair, by simp [designation, repository]⟩, modelExclusionF4 repository⟩

theorem modelVacuous : (model recordedQuery repository).exclusionF4 ∅ := by
  simp [FindResult.exclusionF4]

theorem modelVacuousEarnsNothing :
    ¬ (model recordedQuery repository).discriminatingF4 ∅ := by
  simp [FindResult.discriminatingF4]

/-- Existence at this instantiation, with a nonempty selected witness. -/
theorem conformantImplementationExists :
    ∃ f : (q : FindQuery State Pattern) → (R : Repository Pattern) →
        FindResult Pattern Clause AsOf TextCitation R,
      (∀ q R, (f q R).contentF2 (expected q.tension.context)) ∧
      (∀ q R, (f q R).citationF3 validText) ∧
      (f recordedQuery repository).discriminatingF4 designation ∧
      (f recordedQuery repository).selected.Nonempty :=
  ⟨model, modelContentF2, modelCitationF3, modelDiscriminatingF4, modelNonempty⟩

/-- Counterfactual output variant: selects a reviewer-designated excluded pattern. -/
def badModel : FindResult Pattern Clause AsOf TextCitation repository :=
  { selected := Set.univ
    receipts := fun p _ =>
      { clauseKind := .ifClause, acknowledgedClause := emittedClauses p
        route := .structuredAntecedent, asOf := recordedStamp
        citation := .patternText (emittedCitations p) }
    absence := none }

theorem badModelRefuted : ¬ badModel.exclusionF4 designation := by
  intro h
  exact h .repair (by simp [designation]) (by simp [repository]) (by simp [badModel])

/-- error: unsolved goals
⊢ ∀ (p : Pattern), ¬p = Pattern.repair ∧ ¬p = Pattern.probe -/
#guard_msgs in
example : badModel.exclusionF4 designation := by
  simp [FindResult.exclusionF4, badModel, designation, repository]


#print axioms Pattern
#print axioms Clause
#print axioms SourcePin
#print axioms AsOf
#print axioms TextSpan
#print axioms TextCitation
#print axioms State
#print axioms eligible
#print axioms emittedClauses
#print axioms emittedCitations
#print axioms expectedClauses
#print axioms authoredCitations
#print axioms expected
#print axioms validText
#print axioms model
#print axioms modelContainment
#print axioms modelTypedAbsence
#print axioms modelContentF2
#print axioms modelCitationF3
#print axioms modelClausesNonempty
#print axioms repository
#print axioms recordedStamp
#print axioms recordedState
#print axioms recordedQuery
#print axioms designation
#print axioms modelSelectsAsk
#print axioms modelNonempty
#print axioms modelExclusionF4
#print axioms modelDiscriminatingF4
#print axioms modelVacuous
#print axioms modelVacuousEarnsNothing
#print axioms conformantImplementationExists
#print axioms badModel
#print axioms badModelRefuted

end
end DarkTower.WarMachine.Holes.F11AppliedConformance
