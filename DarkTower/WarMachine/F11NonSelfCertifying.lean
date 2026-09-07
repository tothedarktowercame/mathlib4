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

/-- The fully populated warrant shape present on the pinned record
(`futon3/checks/find-snatch.edn:1`). -/
def recordedWarrant : WarrantData where
  routeNotScoreAlone := true
  file := some "checks/find-snatch.edn"
  ifLines := some (1, 1)
  ifText := some "authored antecedent"

/-- M3: `decide` checks all 34 transcribed rounds and every receipted member;
both F3 readings hold, so those rows cannot choose between them
(`DarkTower/WarMachine/Holes.lean:378-773`). -/
theorem recordedRounds_pass_both_f3_readings :
    ∀ row ∈ findSnatchRounds, ∀ p ∈ row.receipted,
      F3Two recordedWarrant = true ∧ F3Four recordedWarrant = true := by decide

/-- M3: the transcribed F2 and F3 columns coincide on every round
(`futon2/holes/labs/wm-contract/u46_find_transcribe.bb:113-121`). -/
theorem recordedRounds_f2_f3_columns_equal :
    ∀ row ∈ findSnatchRounds, row.receipted = row.nonSelfCertifying := by decide

/-- M4 attribution-aware F3, stated solely from a data-carrying finder's own
returned receipt (`futon2/holes/problems/P-validated-R5.md:487`). -/
def AttributedF3
    (f : FindTypeR FindSnatchScenario SnatchPattern SnatchPattern Unit Unit) : Prop :=
  ∀ t repo p, p ∈ (f t repo).selected →
    ∃ r, (f t repo).receipts p = some r ∧ r.acknowledgedClause = p

/-- M4: the faithful finder satisfies attribution-aware F3
(`DarkTower/WarMachine/F11ReceiptCarrier.lean:150-164`). -/
theorem faithful_attributedF3 : AttributedF3 findRFaithful :=
  findRFaithfulContentF2

/-- M4: the misciting finder fails attribution-aware F3 on a selected member
of the recorded repository (`DarkTower/WarMachine/F11ReceiptCarrier.lean:223-235`). -/
theorem misciting_not_attributedF3 : ¬ AttributedF3 findRMisattributing :=
  findRMisattributingFailsContentF2

/-- M4: erasure loses the separation: both erased finders satisfy the F3
predicate of their own output (`DarkTower/WarMachine/Holes.lean:240-250`). -/
theorem erasure_loses_f3_attribution :
    FinderF3 (eraseFinder findRFaithful) ∧ FinderF3 (eraseFinder findRMisattributing) :=
  ⟨findRFaithfulErasureConformant.f3NonSelfCertifying,
    findRMisattributingErasureConformant.f3NonSelfCertifying⟩

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
