import DarkTower.WarMachine.F11ReceiptCarrier

/-! # F11: measuring non-self-certification at the finder grain

The law says that a receipt cites the selected pattern's text or authored edges
(`futon2/holes/problems/P-validated-R5.md:487`).  Today's carrier instead stores
two propositions (`DarkTower/WarMachine/Holes.lean:240-245`).
-/

open Set Classical
namespace DarkTower.WarMachine.Holes
noncomputable section

/-- The F3 proposition applied to a finder's own output
(`DarkTower/WarMachine/F11Conformance.lean:21-29`). -/
def FinderF3 {State P : Type*} (f : FindType State P) : Prop :=
  ∀ t repo p r, p ∈ (f t repo).selected →
    (f t repo).receipts p = some r → r.nonSelfCertifying

/-- Presence-only F2, split out to test independence from F3
(`DarkTower/WarMachine/F11Conformance.lean:25-26`). -/
def FinderF2 {State P : Type*} (f : FindType State P) : Prop :=
  ∀ t repo p, p ∈ (f t repo).selected → ((f t repo).receipts p).isSome

/-- A receipt whose two propositions merely assert the desired conclusion;
the carrier has no citation data (`DarkTower/WarMachine/Holes.lean:240-245`). -/
def assertedNonSelfCertifyingReceipt : Receipt where
  citesTextOrEdges := True
  scoreAlone := False

/-- M1 finder: replay the recorded selection and assert F3 in every receipt,
without carrying a citation (`DarkTower/WarMachine/Holes.lean:247-250`). -/
def findAssertingF3 : FindType FindSnatchScenario SnatchPattern :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun p => if p ∈ selected then some assertedNonSelfCertifyingReceipt else none
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- M1 nondegeneracy: the assertion-only finder selects a recorded member on
the 18-pattern repository (`DarkTower/WarMachine/F11Conformance.lean:35-38`). -/
theorem findAssertingF3_nonempty :
    (findAssertingF3 { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected.Nonempty := by
  exact ⟨.askForSurplusNotSurrender, by
    simp [findAssertingF3, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]⟩

/-- M1: proposition-only assertions suffice for all of today's F1--F3
(`DarkTower/WarMachine/F11Conformance.lean:21-29`). -/
theorem findAssertingF3_conformant : ConformantFind findAssertingF3 where
  f1Containment := by intro t repo p hp; exact hp.2
  f1TypedAbsence := by
    intro t repo h
    have hs : findSnatchSelected t.context ∩ repo.patterns = ∅ := by
      simpa [findAssertingF3] using h
    simp [findAssertingF3, hs]
  f2Receipted := by
    intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
    change p ∈ findSnatchSelected t.context ∧ p ∈ repo.patterns at hp'
    simp [findAssertingF3, hp']
  f3NonSelfCertifying := by
    intro t repo p r hp hr
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
    change p ∈ findSnatchSelected t.context ∧ p ∈ repo.patterns at hp'
    simp [findAssertingF3, hp'] at hr
    rw [← hr]
    simp [assertedNonSelfCertifyingReceipt, Receipt.nonSelfCertifying]

/-- M2 nondegeneracy for the faithful data-carrying finder
(`DarkTower/WarMachine/F11ReceiptCarrier.lean:150-164`). -/
theorem findRFaithful_nonempty :
    (findRFaithful { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected.Nonempty := by
  exact ⟨.askForSurplusNotSurrender, by
    simp [findRFaithful, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]⟩

/-- M2 nondegeneracy for the misciting data-carrying finder
(`DarkTower/WarMachine/F11ReceiptCarrier.lean:166-180`). -/
theorem findRMisattributing_nonempty :
    (findRMisattributing { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected.Nonempty := by
  exact ⟨.askForSurplusNotSurrender, by
    simp [findRMisattributing, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]⟩

/-- M2: the faithful erasure satisfies F1--F3
(`DarkTower/WarMachine/F11ReceiptCarrier.lean:197-216`). -/
theorem faithfulErasure_conformant : ConformantFind (eraseFinder findRFaithful) :=
  findRFaithfulErasureConformant

/-- M2: the misciting erasure also satisfies F1--F3
(`DarkTower/WarMachine/F11ReceiptCarrier.lean:218-221`). -/
theorem miscitingErasure_conformant : ConformantFind (eraseFinder findRMisattributing) :=
  findRMisattributingErasureConformant

/-- M2: after erasing the cited owner, the nonempty faithful and misciting
finders are equal (`DarkTower/WarMachine/F11ReceiptCarrier.lean:182-195`). -/
theorem faithful_misciting_erasure_eq :
    eraseFinder findRFaithful = eraseFinder findRMisattributing :=
  findRErasuresAreEqual

/-- Data fields tested by the two Clojure F3 predicates
(`futon3/checks/find_organise.clj:567-571`). -/
structure WarrantData where
  routeNotScoreAlone : Bool
  file : Option String
  ifLines : Option (Nat × Nat)
  ifText : Option String
  deriving DecidableEq, Repr

/-- The check's two-conjunct reading: route plus file
(`futon3/checks/find_snatch.clj:167-171`). -/
def F3Two (w : WarrantData) : Bool :=
  w.routeNotScoreAlone && w.file.isSome

/-- The find-organise column's four-conjunct reading
(`futon3/checks/find_organise.clj:567-571`). -/
def F3Four (w : WarrantData) : Bool :=
  F3Two w && w.ifLines.isSome && w.ifText.isSome

/-- A data receipt accepted by the two-conjunct check but rejected by the
four-conjunct producer (`futon3/checks/find_organise.clj:567-571`). -/
def twoOnlyWarrant : WarrantData where
  routeNotScoreAlone := true
  file := some "recorded-pattern.md"
  ifLines := none
  ifText := none

/-- M3: the two- and four-conjunct predicates are not equivalent
(`futon3/checks/find_snatch.clj:167-171`). -/
theorem f3Two_not_equivalent_f3Four :
    F3Two twoOnlyWarrant = true ∧ F3Four twoOnlyWarrant = false := by decide

/-- The warrant of the first receipt of the first recorded round, transcribed
field by field from `futon3/checks/find-snatch.edn` (the receipt for
`:ask-for-surplus-not-surrender` in `[:g1 :snatcher]` round 1): file, `:if-lines`
`[15 16]`, and the `:if-text` string. It is ONE receipt, hand-carried, because no
Lean literal carries warrant data -- see the REVIEW FINDING section below. -/
def recordedWarrant : WarrantData where
  routeNotScoreAlone := true
  file := some "library/snatch/ask-for-surplus-not-surrender.flexiarg"
  ifLines := some (15, 16)
  ifText :=
    some "You are offering a positive number of your tokens and may still choose what to ask in return."

/-- M3: the transcribed receipt passes both readings, so this receipt does not
choose between them. Stated of the ONE receipt it is about and NOT quantified
over the rounds: the rounds carry no warrant to quantify over
(`FindSnatchRowLit`, `DarkTower/WarMachine/Holes.lean:354-361`). -/
theorem recordedWarrant_passes_both_f3_readings :
    F3Two recordedWarrant = true ∧ F3Four recordedWarrant = true := by decide

/-! ### REVIEW FINDING (slice 7): the record's F3 data is not in Lean

`FindSnatchRowLit` (`DarkTower/WarMachine/Holes.lean:354-361`) carries scenario,
round, `selected`, `receipted`, `nonSelfCertifying` and `absence`, and NO warrant,
route or as-of field -- the same omission slice 4 recorded of F2
(`F11ReceiptCarrier.lean:101-102`). So the two fields either F3 reading is decided
by are exactly the fields the transcription drops, and NO theorem over
`findSnatchRounds` can decide either reading. The fixture facts that carry the
measurement were therefore checked OUTSIDE Lean, against
`futon3/checks/find-snatch.edn` (sha256
`839897ef8fe44952403700bd237389449ae4735d3da7df8239b1b94dc7ef4dfa`): 96 receipts,
96 with `:route :structured-antecedent`, 0 with `:score-alone`, and 96 each with
`:file`, `:if-lines`, `:if-text`, `:however-lines` and `:however-text`. Both
readings are true of all 96, which is why the record cannot arbitrate between them.
What IS decidable in Lean about the record is the column equality below.
-/

/-! ### REVIEW CORRECTION (slice 7): only ONE of M5's two separations was ever
available to the record

The dispatched report says the record could have exhibited either separation. It
could not. The `nonSelfCertifying` column is computed as a FILTER of the receipts
map (`futon2/holes/labs/wm-contract/u46_find_transcribe.bb:113-121`), so the column
is a subset of the receipted column by construction and a round witnessing
F3-without-receipted cannot be produced by that transcriber at all. Only
receipted-without-F3 was ever available, and on these rows the record does not
witness even that -- the two columns are equal
(`recordedRounds_f2_f3_columns_equal`). This is a fact about the PRODUCER, not
about the rows, so it is stated here with its pointer rather than as a theorem: a
subset claim over `findSnatchRounds` would follow from the equality below and would
measure nothing.
-/

/-- M3: the transcribed F2 and F3 columns coincide on every round
(`futon2/holes/labs/wm-contract/u46_find_transcribe.bb:113-121`). -/
theorem recordedRounds_f2_f3_columns_equal :
    ∀ row ∈ findSnatchRounds, row.receipted = row.nonSelfCertifying := by decide

/-- REVIEW ADDITION (slice 7): and the SELECTED column coincides with them too, in
all 34 rounds. The producer receipts exactly the firing patterns
(`futon3/checks/find_organise.clj:246-251`, where `:receipts` and `:selected` are
both built from `firing`), so `selected = receipted = nonSelfCertifying` throughout
and the record separates no two of F1, F2 and F3 from each other. Every separation
in this module is therefore carried by a constructed finder, never by a row. -/
theorem recordedRounds_all_three_columns_equal :
    ∀ row ∈ findSnatchRounds,
      row.selected = row.receipted ∧ row.receipted = row.nonSelfCertifying := by decide

/-! ### REVIEW FINDING (slice 7): the delivered M2/M4 witnesses are slice 4's

`findRFaithful` and `findRMisattributing` (`F11ReceiptCarrier.lean:158-186`) differ
in `acknowledgedClause`, which is F2's first ask (`P-validated-R5.md:486`), and
`RelationalReceipt` (`F11ReceiptCarrier.lean:95-99`) carries clause, route and as-of
and NO citation field. F3's datum is the CITED TEXT (`P-validated-R5.md:487`), so a
finder that names the wrong CLAUSE is not a finder that cites the wrong TEXT, and the
four theorems above re-export slice 4's result under F3 names. The predicate and the
witnesses F3 asks for are built below, over a carrier that has the field F3 names.
`AttributedF3` is kept, renamed to what it is, because the re-export is what makes
the substitution auditable.
-/

/-- Slice 4's content-F2, unfolded at the identity expectation
(`F11ReceiptCarrier.lean:154-157`). Named here as F2's datum, not F3's. -/
def ClauseAttributedF2
    (f : FindTypeR FindSnatchScenario SnatchPattern SnatchPattern Unit Unit) : Prop :=
  ∀ t repo p, p ∈ (f t repo).selected →
    ∃ r, (f t repo).receipts p = some r ∧ r.acknowledgedClause = p

/-- Slice 4 re-exported: the faithful finder acknowledges its own clause
(`DarkTower/WarMachine/F11ReceiptCarrier.lean:150-164`). -/
theorem faithful_clauseAttributedF2 : ClauseAttributedF2 findRFaithful :=
  findRFaithfulContentF2

/-- Slice 4 re-exported: the misattributing finder does not
(`DarkTower/WarMachine/F11ReceiptCarrier.lean:223-235`). -/
theorem misattributing_not_clauseAttributedF2 : ¬ ClauseAttributedF2 findRMisattributing :=
  findRMisattributingFailsContentF2

/-! ### REVIEW ADDITION (slice 7): the carrier that has F3's field -/

/-- A receipt that carries WHOSE text it cites. `Receipt`
(`Holes.lean:240-242`) has no such field, and neither has `RelationalReceipt`
(`F11ReceiptCarrier.lean:95-99`): this is the smallest carrier at which F3's
`the pattern's text` can be stated (`P-validated-R5.md:487`). -/
structure CitingReceipt (P : Type*) extends Receipt where
  citedText : P

/-- `find`'s result carrier with citing receipts; as in slice 4 this moves
`find`'s own RETURN TYPE, not only `Receipt` (`Holes.lean:247-250`). -/
structure FindResultC (P : Type*) where
  selected : Set P
  receipts : P → Option (CitingReceipt P)
  absence : Option TypedAbsence

/-- The citing analogue of `FindType` (`F11Conformance.lean:18`). -/
abbrev FindTypeC (State P : Type*) :=
  Tension State → Repository P → FindResultC P

/-- Forgetting the citation gives exactly today's `FindResult`. -/
def FindResultC.erase {P : Type*} (r : FindResultC P) : FindResult P where
  selected := r.selected
  receipts := fun p => (r.receipts p).map (·.toReceipt)
  absence := r.absence

/-- The citation erasure lifted to finders (`F11ReceiptCarrier.lean:147-149`). -/
def eraseFinderC {State P : Type*} (f : FindTypeC State P) : FindType State P :=
  fun t repo => (f t repo).erase

/-- M4, F3's own WHICH, stated of the finder's OWN output and of nothing supplied
from outside it -- the failure `receiptContentAttributedHoldsOfEveryFinder`
(`F11ReceiptCarrier.lean:126-128`) records and this slice must not repeat. -/
def CitesTheSelectedPattern {State P : Type*} (f : FindTypeC State P) : Prop :=
  ∀ t repo p, p ∈ (f t repo).selected →
    ∃ r, (f t repo).receipts p = some r ∧ r.citedText = p

/-- The recorded producer builds each warrant as `warrant repository id`, the
SELECTED pattern's own entry (`futon3/checks/find_organise.clj:213-220`,
`:241-252`), so this finder is the record's citation discipline. -/
def findCFaithful : FindTypeC FindSnatchScenario SnatchPattern :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun p =>
        if p ∈ selected then
          some { citesTextOrEdges := True, scoreAlone := False, citedText := p }
        else none
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- The same selection, citing a DIFFERENT recorded pattern's text
(`misattributedReceiptOwner`, `F11ReceiptCarrier.lean:13-14`). Nothing in
`find_snatch.clj:167-171`, in `find_organise.clj:567-571` or in
`Receipt.nonSelfCertifying` compares the citation to the pattern it is for. -/
def findCMisciting : FindTypeC FindSnatchScenario SnatchPattern :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun p =>
        if p ∈ selected then
          some { citesTextOrEdges := True, scoreAlone := False,
                 citedText := misattributedReceiptOwner p }
        else none
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- M2 nondegeneracy: the faithful citing finder selects a recorded member of the
18-pattern repository (`F11Conformance.lean:35-38`). -/
theorem findCFaithful_nonempty :
    (findCFaithful { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected.Nonempty :=
  ⟨.askForSurplusNotSurrender, by
    simp [findCFaithful, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]⟩

/-- M2 nondegeneracy: so does the misciting one. -/
theorem findCMisciting_nonempty :
    (findCMisciting { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected.Nonempty :=
  ⟨.askForSurplusNotSurrender, by
    simp [findCMisciting, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]⟩

/-- M4: F3's WHICH is inhabited by a FINDER, not only by a hand-built receipt. -/
theorem findCFaithfulCites : CitesTheSelectedPattern findCFaithful := by
  intro t repo p hp
  have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
  exact ⟨{ citesTextOrEdges := True, scoreAlone := False, citedText := p },
    by simp only [findCFaithful, if_pos hp'], rfl⟩

/-- M4: and it REFUTES the misciting finder, witnessed on the recorded repository
at a pattern the record selects. -/
theorem findCMiscitingFailsCitation : ¬ CitesTheSelectedPattern findCMisciting := by
  intro h
  have hp : SnatchPattern.askForSurplusNotSurrender ∈
      (findCMisciting { context := .g1Snatcher, want := True, however := True }
        findSnatchRepository).selected := by
    simp [findCMisciting, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]
  obtain ⟨r, hr, hcite⟩ := h { context := .g1Snatcher, want := True, however := True }
    findSnatchRepository .askForSurplusNotSurrender hp
  have key : (findCMisciting { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).receipts .askForSurplusNotSurrender =
      some { citesTextOrEdges := True, scoreAlone := False,
             citedText := misattributedReceiptOwner .askForSurplusNotSurrender } := by
    have hp' : SnatchPattern.askForSurplusNotSurrender ∈
        findSnatchSelected FindSnatchScenario.g1Snatcher ∩ findSnatchRepository.patterns := hp
    simp only [findCMisciting, if_pos hp']
  rw [key, Option.some.injEq] at hr
  subst hr
  simp [misattributedReceiptOwner] at hcite

/-- M2/M4, THE MEASUREMENT: the two finders are EQUAL after erasing the citation,
so no predicate whatever on today's `FindResult` separates a finder that cites the
selected pattern's text from one that cites another pattern's. F3's blindness is a
fact about the CARRIER, exactly as slice 4 found of F2
(`F11ReceiptCarrier.lean:182-195`) -- and it is a SECOND blindness, on a second
field, not that one re-exported. -/
theorem findCErasuresAreEqual : eraseFinderC findCFaithful = eraseFinderC findCMisciting := by
  funext t repo
  simp only [eraseFinderC, findCFaithful, findCMisciting, FindResultC.erase,
    FindResult.mk.injEq, true_and, and_true]
  funext p
  by_cases hp : p ∈ findSnatchSelected t.context ∩ repo.patterns <;>
    simp [hp]

/-- M4: the faithful citing finder's erasure satisfies today's F1--F3. -/
theorem findCFaithfulErasureConformant : ConformantFind (eraseFinderC findCFaithful) where
  f1Containment := by intro t repo p hp; exact hp.2
  f1TypedAbsence := by
    intro t repo h
    have hs : findSnatchSelected t.context ∩ repo.patterns = ∅ := by
      simpa [eraseFinderC, findCFaithful, FindResultC.erase] using h
    simp [eraseFinderC, findCFaithful, FindResultC.erase, hs]
  f2Receipted := by
    intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
    simp [eraseFinderC, findCFaithful, FindResultC.erase]
    exact hp'
  f3NonSelfCertifying := by
    intro t repo p r hp hr
    simp [eraseFinderC, findCFaithful, FindResultC.erase] at hr
    rw [← hr.2]
    simp [Receipt.nonSelfCertifying]

/-- M4: and therefore so does the MISCITING finder's -- today's F3 returns the same
verdict on a finder whose every receipt cites the wrong pattern's text. -/
theorem findCMiscitingErasureConformant : ConformantFind (eraseFinderC findCMisciting) := by
  rw [← findCErasuresAreEqual]; exact findCFaithfulErasureConformant

/-- M4: erasure loses the separation: both erased finders satisfy the F3
predicate of their own output (`DarkTower/WarMachine/Holes.lean:240-250`). -/
theorem erasure_loses_f3_attribution :
    FinderF3 (eraseFinder findRFaithful) ∧ FinderF3 (eraseFinder findRMisattributing) :=
  ⟨findRFaithfulErasureConformant.f3NonSelfCertifying,
    findRMisattributingErasureConformant.f3NonSelfCertifying⟩

/-- REVIEW ADDITION (slice 7): the same, on F3's own field -- today's F3 holds of
both citing finders after erasure, so the separation `findCMiscitingFailsCitation`
makes is exactly what the carrier destroys. -/
theorem citationErasureLosesF3 :
    FinderF3 (eraseFinderC findCFaithful) ∧ FinderF3 (eraseFinderC findCMisciting) :=
  ⟨findCFaithfulErasureConformant.f3NonSelfCertifying,
    findCMiscitingErasureConformant.f3NonSelfCertifying⟩

/-- M5 finder satisfying F2 but not F3: it selects recorded members and gives
each a score-alone receipt (`DarkTower/WarMachine/F11Conformance.lean:25-29`). -/
def findF2NotF3 : FindType FindSnatchScenario SnatchPattern :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun p => if p ∈ selected then
        some { citesTextOrEdges := False, scoreAlone := True } else none
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- M5 nondegeneracy for the F2-not-F3 finder on the recorded repository
(`DarkTower/WarMachine/F11Conformance.lean:35-38`). -/
theorem findF2NotF3_nonempty :
    (findF2NotF3 { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected.Nonempty := by
  exact ⟨.askForSurplusNotSurrender, by
    simp [findF2NotF3, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]⟩

/-- M5: the score-alone finder satisfies receipt presence
(`DarkTower/WarMachine/F11Conformance.lean:25-26`). -/
theorem findF2NotF3_satisfies_f2 : FinderF2 findF2NotF3 := by
  intro t repo p hp
  have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
  change p ∈ findSnatchSelected t.context ∧ p ∈ repo.patterns at hp'
  simp [findF2NotF3, hp']

/-- M5: the score-alone finder refutes F3 at a selected recorded member
(`DarkTower/WarMachine/F11Conformance.lean:27-29`). -/
theorem findF2NotF3_refutes_f3 : ¬ FinderF3 findF2NotF3 := by
  intro h
  let t : Tension FindSnatchScenario :=
    { context := .g1Snatcher, want := True, however := True }
  have hp : SnatchPattern.askForSurplusNotSurrender ∈
      (findF2NotF3 t findSnatchRepository).selected := by
    simp [findF2NotF3, t, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]
  have hr : (findF2NotF3 t findSnatchRepository).receipts
      .askForSurplusNotSurrender = some { citesTextOrEdges := False, scoreAlone := True } := by
    simp [findF2NotF3, t, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]
  have := h t findSnatchRepository .askForSurplusNotSurrender _ hp hr
  simp [Receipt.nonSelfCertifying] at this

/-- M5 finder satisfying F3 vacuously but not F2: it selects recorded members
and returns no receipts (`DarkTower/WarMachine/F11Conformance.lean:25-29`). -/
def findF3NotF2 : FindType FindSnatchScenario SnatchPattern :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun _ => none
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- M5 nondegeneracy for the F3-not-F2 finder on the recorded repository
(`DarkTower/WarMachine/F11Conformance.lean:35-38`). -/
theorem findF3NotF2_nonempty :
    (findF3NotF2 { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected.Nonempty := by
  exact ⟨.askForSurplusNotSurrender, by
    simp [findF3NotF2, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]⟩

/-- M5: no receipt can witness a bad F3 assertion, so FinderF3 holds
(`DarkTower/WarMachine/F11Conformance.lean:27-29`). -/
theorem findF3NotF2_satisfies_f3 : FinderF3 findF3NotF2 := by
  intro t repo p r hp hr
  simp [findF3NotF2] at hr

/-- M5: the same nonempty finder refutes receipt-presence F2
(`DarkTower/WarMachine/F11Conformance.lean:25-26`). -/
theorem findF3NotF2_refutes_f2 : ¬ FinderF2 findF3NotF2 := by
  intro h
  let t : Tension FindSnatchScenario :=
    { context := .g1Snatcher, want := True, however := True }
  have hp : SnatchPattern.askForSurplusNotSurrender ∈
      (findF3NotF2 t findSnatchRepository).selected := by
    simp [findF3NotF2, t, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]
  simpa [findF3NotF2] using h t findSnatchRepository .askForSurplusNotSurrender hp

end
end DarkTower.WarMachine.Holes
