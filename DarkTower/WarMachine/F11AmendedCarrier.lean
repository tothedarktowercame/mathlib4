import DarkTower.WarMachine.F11F4Reading
import DarkTower.WarMachine.F11ReceiptCarrier

/-! # F11 slice 6: the joint amended-carrier arm

This module combines the data-carrying receipt from
`F11ReceiptCarrier.lean:96-100` with the zero-mass result field absent from
`Holes.lean:247-250`.  It measures the combined arm without changing `find`.
-/

open Set Classical

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- F11 slice 6 M1: receipt data requested by `P-validated-R5.md:486`, extending the two proposition fields at `Holes.lean:240-242`. -/
structure AmendedReceipt (Clause Route AsOf : Type*) extends Receipt where
  acknowledgedClause : Clause
  retrievalRoute : Route
  asOf : AsOf

/-- F11 slice 6 M1: joint result carrier, adding data receipts and the zero-mass field found only on `FindReceiptRow` at `Holes.lean:252-259`. -/
structure AmendedFindResult (P Clause Route AsOf : Type*) where
  selected : Set P
  receipts : P → Option (AmendedReceipt Clause Route AsOf)
  zeroMass : Set P
  absence : Option TypedAbsence

/-- F11 slice 6 M1: function signature corresponding to `FindType` at `F11Conformance.lean:18` with the joint amended result. -/
abbrev AmendedFindType (State P Clause Route AsOf : Type*) :=
  Tension State → Repository P → AmendedFindResult P Clause Route AsOf

/-- F11 slice 6 M1: F1--F4 jointly stated on the amended function result. F4 is returned-designation exclusion, not forall-inputs reading A at `F11Conformance.lean:31-32`. -/
structure ConformantAmendedFind {State P Route AsOf : Type*}
    (f : AmendedFindType State P P Route AsOf) : Prop where
  f1Containment : ∀ t repo, (f t repo).selected ⊆ repo.patterns
  f1TypedAbsence : ∀ t repo, (f t repo).selected = ∅ →
    (f t repo).absence = some .noPatternAddressesThisTension
  f2Content : ∀ t repo p, p ∈ (f t repo).selected →
    ∃ r, (f t repo).receipts p = some r ∧ r.acknowledgedClause = p
  f3NonSelfCertifying : ∀ t repo p r, p ∈ (f t repo).selected →
    (f t repo).receipts p = some r → r.nonSelfCertifying
  f4ReturnedZeroMass : ∀ t repo p, p ∈ (f t repo).zeroMass →
    p ∈ repo.patterns ∧ p ∉ (f t repo).selected

/-- F11 slice 6 M1: erase the joint carrier to today's `FindResult` at `Holes.lean:247-250`. -/
def AmendedFindResult.erase {P Clause Route AsOf : Type*}
    (r : AmendedFindResult P Clause Route AsOf) : FindResult P where
  selected := r.selected
  receipts := fun p => (r.receipts p).map (·.toReceipt)
  absence := r.absence

/-- F11 slice 6 M1: erase a joint amended finder to today's function signature at `F11Conformance.lean:18`. -/
def eraseAmendedFinder {State P Clause Route AsOf : Type*}
    (f : AmendedFindType State P Clause Route AsOf) : FindType State P :=
  fun t repo => (f t repo).erase

/-- F11 slice 6 M1: fixing the returned field to the recorded designation from `Holes.lean:342-348` makes amended F4 imply reading B at `F11DischargeArm.lean:59-62`. -/
theorem amendedF4ImpliesRecordedReadingB
    {Route AsOf : Type*}
    {f : AmendedFindType FindSnatchScenario SnatchPattern SnatchPattern Route AsOf}
    (hf : ConformantAmendedFind f)
    (hz : ∀ t, (f t findSnatchRepository).zeroMass = findSnatchZeroMassSet t.context) :
    FindExcludesRecordedZeroMass (eraseAmendedFinder f) := by
  intro t p hp
  simpa [eraseAmendedFinder, AmendedFindResult.erase] using
    hf.f4ReturnedZeroMass t findSnatchRepository p (hz t ▸ hp)

/-- F11 slice 6 M1: when the returned designation equals an external designation on every input, amended F4 implies reading C at `F11F4Reading.lean:26-29`. -/
theorem amendedF4ImpliesReadingC
    {State P Route AsOf : Type*} {zm : State → Set P}
    {f : AmendedFindType State P P Route AsOf}
    (hf : ConformantAmendedFind f)
    (hz : ∀ t repo, (f t repo).zeroMass = zm t.context) :
    FindRespectsZeroMass zm (eraseAmendedFinder f) := by
  intro t repo p hp hrepo
  exact (hf.f4ReturnedZeroMass t repo p (hz t repo ▸ hp)).2

/-- F11 slice 6 M1: at the recorded repository, reading B supplies the converse returned-designation F4 clause when the returned field is pinned to the recorded designation. -/
theorem recordedReadingBImpliesAmendedF4AtRecord
    {Route AsOf : Type*}
    {f : AmendedFindType FindSnatchScenario SnatchPattern SnatchPattern Route AsOf}
    (hz : ∀ t, (f t findSnatchRepository).zeroMass = findSnatchZeroMassSet t.context)
    (hb : FindExcludesRecordedZeroMass (eraseAmendedFinder f)) :
    ∀ t p, p ∈ (f t findSnatchRepository).zeroMass →
      p ∈ findSnatchRepository.patterns ∧ p ∉ (f t findSnatchRepository).selected := by
  intro t p hp
  have hp' : p ∈ findSnatchZeroMass t.context := by simpa [hz t, findSnatchZeroMassSet] using hp
  simpa [eraseAmendedFinder, AmendedFindResult.erase] using hb t p hp'

/-- F11 slice 6 M1: at the same nonempty recorded designation, reading C also supplies the converse F4 clause; repository membership comes from the recorded designation theorem at `F11Conformance.lean:176-180`. -/
theorem recordedReadingCImpliesAmendedF4AtRecord
    {Route AsOf : Type*}
    {f : AmendedFindType FindSnatchScenario SnatchPattern SnatchPattern Route AsOf}
    (hz : ∀ t, (f t findSnatchRepository).zeroMass = findSnatchZeroMassSet t.context)
    (hc : FindRespectsZeroMass findSnatchZeroMassSet (eraseAmendedFinder f)) :
    ∀ t p, p ∈ (f t findSnatchRepository).zeroMass →
      p ∈ findSnatchRepository.patterns ∧ p ∉ (f t findSnatchRepository).selected := by
  intro t p hp
  have hp' : p ∈ findSnatchZeroMass t.context := by simpa [hz t, findSnatchZeroMassSet] using hp
  have hin := (findSnatchReplayExcludesDeclaredZeroMass t p hp').1
  exact ⟨hin, hc t findSnatchRepository p hp' hin⟩

/-- F11 slice 6 M1/M2: faithful amended replay, using the recorded selection and recorded nonempty zero-mass designation at `Holes.lean:342-348`. -/
def amendedFaithful : AmendedFindType FindSnatchScenario SnatchPattern SnatchPattern Unit Unit :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun p => if p ∈ selected then some
        { citesTextOrEdges := True, scoreAlone := False, acknowledgedClause := p,
          retrievalRoute := (), asOf := () } else none
      zeroMass := findSnatchZeroMassSet t.context ∩ repo.patterns
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- F11 slice 6 M1/M2: misattributing amended replay, differing only in carried receipt ownership from `amendedFaithful`. -/
def amendedMisattributing : AmendedFindType FindSnatchScenario SnatchPattern SnatchPattern Unit Unit :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun p => if p ∈ selected then some
        { citesTextOrEdges := True, scoreAlone := False,
          acknowledgedClause := misattributedReceiptOwner p,
          retrievalRoute := (), asOf := () } else none
      zeroMass := findSnatchZeroMassSet t.context ∩ repo.patterns
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- F11 slice 6 M1: faithful replay satisfies all four joint laws, including returned-designation F4. -/
theorem amendedFaithfulConformant : ConformantAmendedFind amendedFaithful where
  f1Containment := by intro t repo p hp; exact hp.2
  f1TypedAbsence := by
    intro t repo h
    have hs : findSnatchSelected t.context ∩ repo.patterns = ∅ := by
      simpa [amendedFaithful] using h
    simp [amendedFaithful, hs]
  f2Content := by
    intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := by
      simpa [amendedFaithful] using hp
    let rr : AmendedReceipt SnatchPattern Unit Unit :=
      { citesTextOrEdges := True, scoreAlone := False, acknowledgedClause := p,
        retrievalRoute := (), asOf := () }
    refine ⟨rr, ?_, rfl⟩
    change (if p ∈ findSnatchSelected t.context ∩ repo.patterns then some _ else none) = some rr
    rw [if_pos hp']
  f3NonSelfCertifying := by
    intro t repo p r hp hr
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := by
      simpa [amendedFaithful] using hp
    simp only [amendedFaithful, if_pos hp'] at hr
    have hre := Option.some.inj hr
    rw [← hre]
    simp [Receipt.nonSelfCertifying]
  f4ReturnedZeroMass := by
    intro t repo p hp
    refine ⟨hp.2, ?_⟩
    intro hs
    have hz := findSnatchReplayExcludesDeclaredZeroMass t p hp.1
    exact hz.2 ⟨hs.1, hz.1⟩

/-- F11 slice 6 M1: erasing faithful amended replay preserves exactly the recorded replay selection at `F11Conformance.lean:70-78`. -/
theorem eraseAmendedFaithful_selected (t) (repo) :
    (eraseAmendedFinder amendedFaithful t repo).selected =
      (findSnatchReplay t repo).selected := rfl

/-- F11 slice 6 M1: returned-designation F4 does not imply reading A; faithful amended replay is conformant but its erasure refutes A by `F11Conformance.lean:207-218`. -/
theorem amendedF4DoesNotImplyReadingA :
    ConformantAmendedFind amendedFaithful ∧
      ¬ FindFalsifiable (eraseAmendedFinder amendedFaithful) := by
  refine ⟨amendedFaithfulConformant, ?_⟩
  intro h
  apply findSnatchReplayNotFalsifiable
  intro t repo hn
  simpa only [eraseAmendedFaithful_selected] using h t repo hn

/-- F11 slice 6 M1: faithful amended replay satisfies reading B at `F11DischargeArm.lean:59-62`. -/
theorem amendedFaithfulReadingB :
    FindExcludesRecordedZeroMass (eraseAmendedFinder amendedFaithful) := by
  intro t p hp
  simpa only [eraseAmendedFaithful_selected] using
    findSnatchReplayExcludesDeclaredZeroMass t p hp

/-- F11 slice 6 M1: faithful amended replay satisfies reading C at the nonempty recorded designation from `F11F4Reading.lean:31-32`. -/
theorem amendedFaithfulReadingC :
    FindRespectsZeroMass findSnatchZeroMassSet (eraseAmendedFinder amendedFaithful) := by
  intro t repo p hp hrepo
  simpa only [eraseAmendedFaithful_selected] using
    findSnatchReplayRespectsRecordedZeroMass t repo p hp hrepo

/-- F11 slice 6 M1 reverse-A witness: a content-receipted `findAllBut` result deliberately returns its inhabited selection as zero mass. -/
def amendedAllButBad (q : SnatchPattern) :
    AmendedFindType FindSnatchScenario SnatchPattern SnatchPattern Unit Unit :=
  fun _ repo =>
    let selected := if q ∈ repo.patterns then repo.patterns \ {q} else ∅
    { selected := selected
      receipts := fun p => if p ∈ selected then some
        { citesTextOrEdges := True, scoreAlone := False, acknowledgedClause := p,
          retrievalRoute := (), asOf := () } else none
      zeroMass := selected
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- F11 slice 6 M1 floor: the reverse-A witness selects a named non-q member on the recorded repository. -/
theorem amendedAllButBadSelectionNonempty :
    ((amendedAllButBad .consultTheRemedyBeforeExiting
      { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected).Nonempty :=
  ⟨.askForSurplusNotSurrender, by
    simp [amendedAllButBad, findSnatchRepository, snatchRepository]⟩

/-- F11 slice 6 M1: reading A does not imply returned-designation F4; this witness is A-falsifiable yet its selected named member is also returned as zero mass. -/
theorem readingADoesNotImplyAmendedF4 :
    FindFalsifiable (eraseAmendedFinder
      (amendedAllButBad .consultTheRemedyBeforeExiting)) ∧
      ¬ ConformantAmendedFind (amendedAllButBad .consultTheRemedyBeforeExiting) := by
  constructor
  · intro t repo hn
    by_cases hq : SnatchPattern.consultTheRemedyBeforeExiting ∈ repo.patterns
    · exact ⟨.consultTheRemedyBeforeExiting, hq, by
        simp [eraseAmendedFinder, AmendedFindResult.erase, amendedAllButBad, hq]⟩
    · obtain ⟨p, hp⟩ := hn
      exact ⟨p, hp, by simp [eraseAmendedFinder, AmendedFindResult.erase,
        amendedAllButBad, hq]⟩
  · intro h
    have hm := amendedAllButBadSelectionNonempty.choose_spec
    exact (h.f4ReturnedZeroMass
      { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository amendedAllButBadSelectionNonempty.choose hm).2 hm

/-- F11 slice 6 floor: faithful amended replay selects a named pattern on the recorded 18-pattern repository, using `F11Conformance.lean:221-228`. -/
theorem amendedFaithfulSelectionNonempty :
    ((amendedFaithful { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected).Nonempty :=
  ⟨.askForSurplusNotSurrender, by
    exact ⟨(findSnatchReplaySelectsNamedPattern True True).1,
      (findSnatchReplaySelectsNamedPattern True True).2⟩⟩

/-- F11 slice 6 floor: the misattributing amended replay has the same inhabited recorded selection. -/
theorem amendedMisattributingSelectionNonempty :
    ((amendedMisattributing { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected).Nonempty :=
  ⟨.askForSurplusNotSurrender, by
    exact ⟨(findSnatchReplaySelectsNamedPattern True True).1,
      (findSnatchReplaySelectsNamedPattern True True).2⟩⟩

/-- F11 slice 6 M2: content F2 rejects the amended misattributor on the inhabited recorded selection. -/
theorem amendedMisattributingNotConformant : ¬ ConformantAmendedFind amendedMisattributing := by
  intro h
  obtain ⟨r, hr, hc⟩ := h.f2Content
    { context := .g1Snatcher, want := True, however := True }
    findSnatchRepository .askForSurplusNotSurrender
    (by exact ⟨(findSnatchReplaySelectsNamedPattern True True).1,
      (findSnatchReplaySelectsNamedPattern True True).2⟩)
  simp [amendedMisattributing, findSnatchSelected, findSnatchScenarios,
    findSnatchRepository, snatchRepository] at hr
  rw [← hr] at hc
  simp [misattributedReceiptOwner] at hc

/-- F11 slice 6 M2: unlike the erasure equality at `F11ReceiptCarrier.lean:186-193`, the joint carrier separates faithful and misattributing receipts on the recorded input. -/
theorem amendedReceiptDataSeparates : amendedFaithful ≠ amendedMisattributing := by
  intro h
  have he := congrArg (fun f =>
    (f { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).receipts .askForSurplusNotSurrender) h
  simp [amendedFaithful, amendedMisattributing, findSnatchSelected,
    findSnatchScenarios, findSnatchRepository, snatchRepository,
    misattributedReceiptOwner] at he

/-- F11 slice 6 M2/M3: zero-mass-only variant; receipt data and every visible current-carrier field remain faithful. -/
def amendedDifferentZeroMass := fun t repo =>
  let r := amendedFaithful t repo
  { r with zeroMass := ∅ }

/-- F11 slice 6 floor: the zero-mass-only variant still selects the same named recorded pattern. -/
theorem amendedDifferentZeroMassSelectionNonempty :
    ((amendedDifferentZeroMass
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).selected).Nonempty := by
  simpa [amendedDifferentZeroMass] using amendedFaithfulSelectionNonempty

/-- F11 slice 6 M3: changing only zero mass to empty preserves all four joint laws. -/
theorem amendedDifferentZeroMassConformant : ConformantAmendedFind amendedDifferentZeroMass := by
  refine { amendedFaithfulConformant with f4ReturnedZeroMass := ?_ }
  simp [amendedDifferentZeroMass]

/-- F11 slice 6 M2: the zero-mass field alone separates two finders erased to equal current `FindResult` values. -/
theorem amendedZeroMassSeparates : amendedFaithful ≠ amendedDifferentZeroMass := by
  intro h
  have hm : SnatchPattern.consultTheRemedyBeforeExiting ∈
      (amendedFaithful
        { context := .g1Snatcher, want := True, however := True }
        findSnatchRepository).zeroMass := by
    simp [amendedFaithful, findSnatchZeroMassSet, findSnatchZeroMass,
      findSnatchRepository, snatchRepository]
  rw [h] at hm
  simp [amendedDifferentZeroMass] at hm

/-- F11 slice 6 M3: receipt-data separation leaves zero mass equal, so the receipt amendment buys a distinction the zero-mass amendment does not. -/
theorem amendedReceiptPairAgreesOnZeroMass (t) (repo) :
    (amendedFaithful t repo).zeroMass = (amendedMisattributing t repo).zeroMass := rfl

/-- F11 slice 6 M3: zero-mass separation leaves receipts equal, so the zero-mass amendment buys a distinction the receipt amendment does not. -/
theorem amendedZeroMassPairAgreesOnReceipts (t) (repo) :
    (amendedFaithful t repo).receipts = (amendedDifferentZeroMass t repo).receipts := rfl

/-- F11 slice 6 M1: faithful returned designation is nonempty on the recorded repository, preventing a vacuous F4 comparison. -/
theorem amendedRecordedDesignationNonempty :
    ((amendedFaithful { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).zeroMass).Nonempty :=
  ⟨.consultTheRemedyBeforeExiting, by
    simp [amendedFaithful, findSnatchZeroMassSet, findSnatchZeroMass,
      findSnatchRepository, snatchRepository]⟩

/-- F11 slice 6 M5: the amended F4 admits an empty-selection finder; its returned zero-mass field is the repository itself and is therefore nonvacuous whenever the repository is. -/
def amendedRefusing {State P : Type*} : AmendedFindType State P P Unit Unit :=
  fun _ repo =>
    { selected := ∅, receipts := fun _ => none, zeroMass := repo.patterns,
      absence := some .noPatternAddressesThisTension }

/-- F11 slice 6 M5: the empty-selection amended finder satisfies all four laws. -/
theorem amendedRefusingConformant {State P : Type*} :
    ConformantAmendedFind (amendedRefusing (State := State) (P := P)) where
  f1Containment := by simp [amendedRefusing]
  f1TypedAbsence := by simp [amendedRefusing]
  f2Content := by simp [amendedRefusing]
  f3NonSelfCertifying := by simp [amendedRefusing]
  f4ReturnedZeroMass := by simp [amendedRefusing]

/-- F11 slice 6 M5 floor: the refusing finder's returned designation is inhabited on the recorded repository even though its selection is empty. -/
theorem amendedRefusingRecordedDesignationNonempty :
    ((amendedRefusing
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).zeroMass).Nonempty := by
  simpa [amendedRefusing] using findSnatchRepositoryNonempty

end

end DarkTower.WarMachine.Holes
