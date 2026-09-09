import DarkTower.WarMachine.F11Conformance

/-! # F11 receipt-carrier arms

This module prices presence-only, proposition-only, and relational readings of
F2 without changing `LegacyReceipt` at `Holes.lean:240-242`.
-/

open Set Classical
namespace DarkTower.WarMachine.Holes
noncomputable section

/-- F11 slice 4 M1: the deliberately wrong owner assigned to every receipt; current `LegacyReceipt` at `Holes.lean:240-242` has no field in which this attribution could appear. -/
def misattributedReceiptOwner (_ : SnatchPattern) : SnatchPattern :=
  .consultTheRemedyBeforeExiting

/-- F11 slice 4 M1: replay selection with a structured receipt present for every selected member, as required only by `ConformantFind.f2Receipted` at `F11Conformance.lean:25-26`. -/
def findSnatchMisattributing : FindType FindSnatchScenario SnatchPattern :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun p => if p ∈ selected then some findStructuredReceipt else none
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- F11 slice 4 M1: presence-only F2 accepts the misattributing finder; F1 and F3 also hold because `LegacyReceipt.nonSelfCertifying` at `Holes.lean:244-245` reads only two propositions. -/
theorem findSnatchMisattributingConformant : ConformantFind findSnatchMisattributing where
  f1Containment := by intro t repo p hp; exact hp.2
  f1TypedAbsence := by
    intro t repo h
    have hs : findSnatchSelected t.context ∩ repo.patterns = ∅ := by
      simpa [findSnatchMisattributing] using h
    simp [findSnatchMisattributing, hs]
  f2Receipted := by
    intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := by
      simpa [findSnatchMisattributing] using hp
    have hc : p ∈ findSnatchSelected t.context ∧ p ∈ repo.patterns := hp'
    simp [findSnatchMisattributing, hc]
  f3NonSelfCertifying := by
    intro t repo p r hp hr
    simp [findSnatchMisattributing] at hr
    rw [← hr.2]
    simp [LegacyReceipt.nonSelfCertifying, findStructuredReceipt]

/-- F11 slice 4 M1: on the full recorded repository (`F11Conformance.lean:35-38`) a selected pattern is assigned the different pattern's receipt owner. -/
theorem findSnatchMisattributingWitness :
    SnatchPattern.askForSurplusNotSurrender ∈
      (findSnatchMisattributing
        { context := .g1Snatcher, want := True, however := True }
        findSnatchRepository).selected ∧
    misattributedReceiptOwner .askForSurplusNotSurrender =
      .consultTheRemedyBeforeExiting ∧
    SnatchPattern.askForSurplusNotSurrender ≠ .consultTheRemedyBeforeExiting := by
  simp [findSnatchMisattributing, findSnatchSelected, findSnatchScenarios,
    findSnatchRepository, snatchRepository, misattributedReceiptOwner]

/-- F11 slice 4 M1/M2 relational F2: an independently carried receipt-owner datum must equal the selected pattern; presence and true proposition fields alone cannot state this equality. -/
def ReceiptContentAttributed {State P : Type*} (f : FindType State P)
    (owner : Tension State → Repository P → P → P) : Prop :=
  ∀ t repo p, p ∈ (f t repo).selected → owner t repo p = p

/-- F11 slice 4 M1: content-attributing F2 rejects the witnessed misattributor on the recorded repository, unlike `findSnatchMisattributingConformant`. -/
theorem findSnatchMisattributingFailsContentF2 :
    ¬ ReceiptContentAttributed findSnatchMisattributing
      (fun _ _ p => misattributedReceiptOwner p) := by
  intro h
  have hp := findSnatchMisattributingWitness.1
  have := h { context := .g1Snatcher, want := True, however := True }
    findSnatchRepository .askForSurplusNotSurrender hp
  simp [misattributedReceiptOwner] at this

/-- F11 slice 4 M2 proposition-field arm, adding exactly the three propositions requested by F2 at `P-validated-R5.md:486`; none carries which clause, route, or date. -/
structure ReceiptWithAssertions extends LegacyReceipt where
  acknowledgesClause : Prop
  hasRoute : Prop
  hasAsOf : Prop

/-- F11 slice 4 M2: all three new propositions can be true on the same wrongly attributed witness, so this arm does not imply relational F2. -/
def misattributedReceiptWithAssertions : ReceiptWithAssertions where
  citesTextOrEdges := True
  scoreAlone := False
  acknowledgesClause := True
  hasRoute := True
  hasAsOf := True

/-- F11 slice 4 M2: the proposition-only arm is inhabited with every assertion true while `misattributedReceiptOwner` remains unequal to the selected pattern. -/
theorem assertionFieldsDoNotFixAttribution :
    misattributedReceiptWithAssertions.acknowledgesClause ∧
    misattributedReceiptWithAssertions.hasRoute ∧
    misattributedReceiptWithAssertions.hasAsOf ∧
    misattributedReceiptOwner .askForSurplusNotSurrender ≠
      SnatchPattern.askForSurplusNotSurrender := by
  simp [misattributedReceiptWithAssertions, misattributedReceiptOwner]

/-- F11 slice 4 M2/M3 relational carrier: unlike three propositions, this stores clause, route, and fixture as-of data and can equate the clause to an input-derived expectation. -/
structure RelationalReceipt (Clause Route AsOf : Type*) extends LegacyReceipt where
  acknowledgedClause : Clause
  retrievalRoute : Route
  asOf : AsOf

/-- F11 slice 4 M3 small hand-carried content witness, necessary because `FindSnatchRowLit` at `Holes.lean:354-360` transcribes no warrant, route, or as-of field. -/
def handCarriedReceipt : RelationalReceipt SnatchPattern Unit Unit where
  citesTextOrEdges := True
  scoreAlone := False
  acknowledgedClause := .askForSurplusNotSurrender
  retrievalRoute := ()
  asOf := ()

/-- F11 slice 4 M3: the hand-carried relational receipt satisfies actual equality with its selected pattern, showing content-F2 is inhabited without claiming the omitted record was transcribed. -/
theorem handCarriedReceiptHasRightClause :
    handCarriedReceipt.acknowledgedClause =
      SnatchPattern.askForSurplusNotSurrender := rfl

/-! ## Review addition: where the attribution has to live

`ReceiptContentAttributed` above takes its `owner` from OUTSIDE the finder, and
the next theorem is why that cannot price F2: instantiated at the identity it
holds of every finder in the type, the misattributing one included.  So
`findSnatchMisattributingFailsContentF2` refutes a choice of auxiliary function
and not a property of `findSnatchMisattributing`.  The rest of this section
restates the measurement of the finder's OWN output, which is where F2 asks the
attribution to be (`P-validated-R5.md:486`).
-/

/-- F11 slice 4 review: the externally-supplied-owner reading is degenerate -- at the identity it is satisfied by every finder of the type, so it separates owner functions rather than finders. -/
theorem receiptContentAttributedHoldsOfEveryFinder {State P : Type*}
    (f : FindType State P) : ReceiptContentAttributed f (fun _ _ p => p) := by
  intro t repo p _; rfl

/-- F11 slice 4 review: `find`'s result carrier with receipts that CARRY data, the shape a content-stating F2 needs; `LegacyFindResult` at `Holes.lean:247-250` types its receipts by `LegacyReceipt`, so this is a change to `find`'s own return type and not only to `LegacyReceipt`. -/
structure FindResultR (P Clause Route AsOf : Type*) where
  selected : Set P
  receipts : P → Option (RelationalReceipt Clause Route AsOf)
  absence : Option TypedAbsence

/-- F11 slice 4 review: the data-carrying analogue of `FindType` at `F11Conformance.lean:18`. -/
abbrev FindTypeR (State P Clause Route AsOf : Type*) :=
  Tension State → Repository P → FindResultR P Clause Route AsOf

/-- F11 slice 4 review: forgetting the carried data gives exactly today's `LegacyFindResult`, via the `toLegacyReceipt` projection `extends LegacyReceipt` supplies. -/
def FindResultR.erase {P Clause Route AsOf : Type*}
    (r : FindResultR P Clause Route AsOf) : LegacyFindResult P where
  selected := r.selected
  receipts := fun p => (r.receipts p).map (·.toLegacyReceipt)
  absence := r.absence

/-- F11 slice 4 review: the erasure lifted to finders, so a data-carrying finder can be judged by today's `ConformantFind` at `F11Conformance.lean:21-29`. -/
def eraseFinder {State P Clause Route AsOf : Type*}
    (f : FindTypeR State P Clause Route AsOf) : FindType State P :=
  fun t repo => (f t repo).erase

/-- F11 slice 4 review: F2 stated of the finder's OWN output -- every selected pattern's returned receipt carries the clause an independently given expectation assigns it. Unlike `ReceiptContentAttributed` this quantifies over what `f` returns, so it separates finders. -/
def ContentF2 {State P Clause Route AsOf : Type*}
    (f : FindTypeR State P Clause Route AsOf) (clauseOf : P → Clause) : Prop :=
  ∀ t repo p, p ∈ (f t repo).selected →
    ∃ r, (f t repo).receipts p = some r ∧ r.acknowledgedClause = clauseOf p

/-- F11 slice 4 review: the recorded replay selection, receipting each selected pattern with a receipt that names THAT pattern. -/
def findRFaithful :
    FindTypeR FindSnatchScenario SnatchPattern SnatchPattern Unit Unit :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun p =>
        if p ∈ selected then
          some { citesTextOrEdges := True, scoreAlone := False,
                 acknowledgedClause := p, retrievalRoute := (), asOf := () }
        else none
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- F11 slice 4 review: the same selection, receipting every selected pattern with a receipt that names a DIFFERENT pattern (`misattributedReceiptOwner`). -/
def findRMisattributing :
    FindTypeR FindSnatchScenario SnatchPattern SnatchPattern Unit Unit :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun p =>
        if p ∈ selected then
          some { citesTextOrEdges := True, scoreAlone := False,
                 acknowledgedClause := misattributedReceiptOwner p,
                 retrievalRoute := (), asOf := () }
        else none
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- F11 slice 4 review, THE MEASUREMENT: the faithful and the misattributing finder are EQUAL after erasure -- not merely both conformant. So no predicate whatever on today's `LegacyFindResult` can separate them, and F2's blindness to attribution is a fact about the carrier rather than about how F2 is phrased. -/
theorem findRErasuresAreEqual :
    eraseFinder findRFaithful = eraseFinder findRMisattributing := by
  funext t repo
  simp only [eraseFinder, findRFaithful, findRMisattributing, FindResultR.erase,
    LegacyFindResult.mk.injEq, true_and, and_true]
  funext p
  by_cases hp : p ∈ findSnatchSelected t.context ∩ repo.patterns <;>
    simp [hp]

/-- F11 slice 4 review: the erased misattributing finder satisfies today's F1-F3, by the equality above and the faithful finder's own conformance. -/
theorem findRFaithfulErasureConformant : ConformantFind (eraseFinder findRFaithful) where
  f1Containment := by
    intro t repo p hp
    exact hp.2
  f1TypedAbsence := by
    intro t repo h
    have hs : findSnatchSelected t.context ∩ repo.patterns = ∅ := by
      simpa [eraseFinder, findRFaithful, FindResultR.erase] using h
    simp [eraseFinder, findRFaithful, FindResultR.erase, hs]
  f2Receipted := by
    intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
    simp [eraseFinder, findRFaithful, FindResultR.erase]
    exact hp'
  f3NonSelfCertifying := by
    intro t repo p r hp hr
    simp [eraseFinder, findRFaithful, FindResultR.erase] at hr
    rw [← hr.2]
    simp [LegacyReceipt.nonSelfCertifying]

/-- F11 slice 4 review: and therefore so does the misattributing one -- the same conformance verdict on a finder whose every receipt names the wrong pattern. -/
theorem findRMisattributingErasureConformant :
    ConformantFind (eraseFinder findRMisattributing) := by
  rw [← findRErasuresAreEqual]; exact findRFaithfulErasureConformant

/-- F11 slice 4 review: content-F2 is INHABITED by a finder, not only by a hand-built receipt -- the faithful finder satisfies it at the identity expectation. -/
theorem findRFaithfulContentF2 : ContentF2 findRFaithful id := by
  intro t repo p hp
  have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
  refine ⟨{ citesTextOrEdges := True, scoreAlone := False,
            acknowledgedClause := p, retrievalRoute := (), asOf := () }, ?_, rfl⟩
  simp only [findRFaithful, if_pos hp']

/-- F11 slice 4 review: and content-F2 REFUTES the misattributing finder, witnessed on the full recorded repository (`F11Conformance.lean:35-38`) at a pattern the record selects -- so the two laws disagree exactly where the carrier is blind. -/
theorem findRMisattributingFailsContentF2 : ¬ ContentF2 findRMisattributing id := by
  have key : ∀ (t : Tension FindSnatchScenario) (repo : Repository SnatchPattern) p,
      p ∈ (findRMisattributing t repo).selected →
      (findRMisattributing t repo).receipts p =
        some { citesTextOrEdges := True, scoreAlone := False,
               acknowledgedClause := misattributedReceiptOwner p,
               retrievalRoute := (), asOf := () } := by
    intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
    simp only [findRMisattributing, if_pos hp']
  intro h
  have hp : SnatchPattern.askForSurplusNotSurrender ∈
      (findRMisattributing
        { context := .g1Snatcher, want := True, however := True }
        findSnatchRepository).selected := findSnatchMisattributingWitness.1
  obtain ⟨r, hr, hclause⟩ := h { context := .g1Snatcher, want := True, however := True }
    findSnatchRepository .askForSurplusNotSurrender hp
  rw [key _ _ _ hp, Option.some.injEq] at hr
  subst hr
  simp [misattributedReceiptOwner] at hclause
end
end DarkTower.WarMachine.Holes
