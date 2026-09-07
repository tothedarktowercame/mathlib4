import DarkTower.WarMachine.F11Conformance

/-! # F11 receipt-carrier arms

This module prices presence-only, proposition-only, and relational readings of
F2 without changing `Receipt` at `Holes.lean:240-242`.
-/

open Set Classical
namespace DarkTower.WarMachine.Holes
noncomputable section

/-- F11 slice 4 M1: the deliberately wrong owner assigned to every receipt; current `Receipt` at `Holes.lean:240-242` has no field in which this attribution could appear. -/
def misattributedReceiptOwner (_ : SnatchPattern) : SnatchPattern :=
  .consultTheRemedyBeforeExiting

/-- F11 slice 4 M1: replay selection with a structured receipt present for every selected member, as required only by `ConformantFind.f2Receipted` at `F11Conformance.lean:25-26`. -/
def findSnatchMisattributing : FindType FindSnatchScenario SnatchPattern :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun p => if p ∈ selected then some findStructuredReceipt else none
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- F11 slice 4 M1: presence-only F2 accepts the misattributing finder; F1 and F3 also hold because `Receipt.nonSelfCertifying` at `Holes.lean:244-245` reads only two propositions. -/
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
    simp [Receipt.nonSelfCertifying, findStructuredReceipt]

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
structure ReceiptWithAssertions extends Receipt where
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
structure RelationalReceipt (Clause Route AsOf : Type*) extends Receipt where
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

end
end DarkTower.WarMachine.Holes
