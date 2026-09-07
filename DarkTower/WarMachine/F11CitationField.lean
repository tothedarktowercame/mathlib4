import DarkTower.WarMachine.F11AmendedCarrier
import DarkTower.WarMachine.F11NonSelfCertifying

/-! # F11 citation field: clause attribution versus cited-text attribution -/

open Set Classical
namespace DarkTower.WarMachine.Holes
noncomputable section

/-- D1: `CitesTheSelectedPattern` (`F11NonSelfCertifying.lean:267-269`)
restated on the priced `AmendedReceipt` output, interpreting its
`acknowledgedClause : SnatchPattern` as the cited pattern. -/
def AmendedCitesSelected
    (f : AmendedFindType FindSnatchScenario SnatchPattern SnatchPattern Unit Unit) : Prop :=
  ∀ t repo p, p ∈ (f t repo).selected →
    ∃ r, (f t repo).receipts p = some r ∧ r.acknowledgedClause = p

/-- D1: the priced faithful finder satisfies the cited-pattern reading. This
restates `ConformantAmendedFind.f2Content` (`F11AmendedCarrier.lean:36-37`) at
the slice-6 `Clause := SnatchPattern` instantiation. -/
theorem amendedFaithful_citesSelected : AmendedCitesSelected amendedFaithful :=
  amendedFaithfulConformant.f2Content

/-- D1: the priced misattributor refutes the same reading on the named selected
pattern in the recorded repository (`F11AmendedCarrier.lean:245-257`). -/
theorem amendedMisattributing_not_citesSelected :
    ¬ AmendedCitesSelected amendedMisattributing := by
  intro h
  obtain ⟨r, hr, hc⟩ := h
    { context := .g1Snatcher, want := True, however := True }
    findSnatchRepository .askForSurplusNotSurrender
    (by simp [amendedMisattributing, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository])
  simp [amendedMisattributing, findSnatchSelected, findSnatchScenarios,
    findSnatchRepository, snatchRepository] at hr
  rw [← hr] at hc
  simp [misattributedReceiptOwner] at hc

/-- D1 floor: both priced finders select the named recorded pattern. This
packages the two existing nonemptiness theorems at
`F11AmendedCarrier.lean:229-243`. -/
theorem amendedCitationPair_nonempty :
    (amendedFaithful { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected.Nonempty ∧
    (amendedMisattributing { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected.Nonempty :=
  ⟨amendedFaithfulSelectionNonempty, amendedMisattributingSelectionNonempty⟩

/-- D1 buy: the priced pair is separated before erasure
(`F11AmendedCarrier.lean:259-267`) and equal afterward
(`F11AmendedCarrier.lean:340-347`). -/
theorem amendedCitationBuy :
    amendedFaithful ≠ amendedMisattributing ∧
      eraseAmendedFinder amendedFaithful = eraseAmendedFinder amendedMisattributing :=
  ⟨amendedReceiptDataSeparates, amendedReceiptPairErasuresAreEqual⟩

/-- D2 carrier holding the two candidate data independently: acknowledged
pattern and cited-text owner (`F11AmendedCarrier.lean:18-21` and
`F11NonSelfCertifying.lean:240-243`). -/
structure DualReceipt extends Receipt where
  acknowledgedClause : SnatchPattern
  citedText : SnatchPattern

/-- D2 finder result whose own receipts carry both candidate data. -/
structure DualResult where
  selected : Set SnatchPattern
  receipts : SnatchPattern → Option DualReceipt
  absence : Option TypedAbsence

/-- D2 finder type over the recorded scenario and repository types. -/
abbrev DualFind := Tension FindSnatchScenario → Repository SnatchPattern → DualResult

/-- D2 erasure to today's `FindResult` (`Holes.lean:247-250`). -/
def eraseDual (f : DualFind) : FindType FindSnatchScenario SnatchPattern := fun t repo =>
  let r := f t repo
  { selected := r.selected, receipts := fun p => (r.receipts p).map (·.toReceipt),
    absence := r.absence }

/-- D2 clause predicate, stated only from the finder's own output. -/
def DualAcknowledgesSelected (f : DualFind) : Prop := ∀ t repo p,
  p ∈ (f t repo).selected → ∃ r, (f t repo).receipts p = some r ∧ r.acknowledgedClause = p

/-- D2 citation predicate, stated only from the finder's own output. -/
def DualCitesSelected (f : DualFind) : Prop := ∀ t repo p,
  p ∈ (f t repo).selected → ∃ r, (f t repo).receipts p = some r ∧ r.citedText = p

/-- The dual receipt selected by each comparison mode. -/
def dualReceipt (mode : Nat) (p : SnatchPattern) : DualReceipt where
  citesTextOrEdges := True
  scoreAlone := False
  acknowledgedClause := if mode = 2 then misattributedReceiptOwner p else p
  citedText := if mode = 1 then misattributedReceiptOwner p else p

/-- D2 three finders: `mode = 0` is faithful; mode 1 changes only citation;
mode 2 changes only acknowledged clause. -/
def dualFinder (mode : Nat) : DualFind := fun t repo =>
  let selected := findSnatchSelected t.context ∩ repo.patterns
  { selected := selected
    receipts := fun p => if p ∈ selected then some (dualReceipt mode p) else none
    absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- D2 floor: every finder used in either separation selects the named recorded
pattern on `findSnatchRepository` (`F11Conformance.lean:35-38`). -/
theorem dualFinders_nonempty : ∀ mode : Fin 3,
    (dualFinder mode { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository).selected.Nonempty := by
  intro mode
  exact ⟨.askForSurplusNotSurrender, by
    simp [dualFinder, findSnatchSelected, findSnatchScenarios,
      findSnatchRepository, snatchRepository]⟩

/-- D2 citation-only change: modes 0 and 1 both acknowledge the selected
pattern, while citation accepts mode 0 and rejects mode 1 on the named record. -/
theorem citation_separates_without_clause :
    DualAcknowledgesSelected (dualFinder 0) ∧
    DualAcknowledgesSelected (dualFinder 1) ∧
    DualCitesSelected (dualFinder 0) ∧ ¬ DualCitesSelected (dualFinder 1) := by
  constructor
  · intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
    change p ∈ findSnatchSelected t.context ∧ p ∈ repo.patterns at hp'
    refine ⟨dualReceipt 0 p, ?_, by simp [dualReceipt]⟩
    simp [dualFinder, hp']
  constructor
  · intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
    change p ∈ findSnatchSelected t.context ∧ p ∈ repo.patterns at hp'
    refine ⟨dualReceipt 1 p, ?_, by simp [dualReceipt]⟩
    simp [dualFinder, hp']
  constructor
  · intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
    change p ∈ findSnatchSelected t.context ∧ p ∈ repo.patterns at hp'
    refine ⟨dualReceipt 0 p, ?_, by simp [dualReceipt]⟩
    simp [dualFinder, hp']
  · intro h
    obtain ⟨r, hr, hc⟩ := h
      { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository .askForSurplusNotSurrender
      (by simp [dualFinder, findSnatchSelected, findSnatchScenarios,
        findSnatchRepository, snatchRepository])
    simp [dualFinder, findSnatchSelected, findSnatchScenarios, findSnatchRepository,
      snatchRepository] at hr
    rw [← hr] at hc
    simp [dualReceipt, misattributedReceiptOwner] at hc

/-- D2 clause-only change: modes 0 and 2 both cite the selected pattern, while
acknowledgement accepts mode 0 and rejects mode 2 on the named record. -/
theorem clause_separates_without_citation :
    DualCitesSelected (dualFinder 0) ∧ DualCitesSelected (dualFinder 2) ∧
    DualAcknowledgesSelected (dualFinder 0) ∧ ¬ DualAcknowledgesSelected (dualFinder 2) := by
  constructor
  · intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
    change p ∈ findSnatchSelected t.context ∧ p ∈ repo.patterns at hp'
    refine ⟨dualReceipt 0 p, ?_, by simp [dualReceipt]⟩
    simp [dualFinder, hp']
  constructor
  · intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
    change p ∈ findSnatchSelected t.context ∧ p ∈ repo.patterns at hp'
    refine ⟨dualReceipt 2 p, ?_, by simp [dualReceipt]⟩
    simp [dualFinder, hp']
  constructor
  · intro t repo p hp
    have hp' : p ∈ findSnatchSelected t.context ∩ repo.patterns := hp
    change p ∈ findSnatchSelected t.context ∧ p ∈ repo.patterns at hp'
    refine ⟨dualReceipt 0 p, ?_, by simp [dualReceipt]⟩
    simp [dualFinder, hp']
  · intro h
    obtain ⟨r, hr, hc⟩ := h
      { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository .askForSurplusNotSurrender
      (by simp [dualFinder, findSnatchSelected, findSnatchScenarios,
        findSnatchRepository, snatchRepository])
    simp [dualFinder, findSnatchSelected, findSnatchScenarios, findSnatchRepository,
      snatchRepository] at hr
    rw [← hr] at hc
    simp [dualReceipt, misattributedReceiptOwner] at hc

/-- D2 buy floor: both independently separated pairs become equal after erasure
to today's carrier. -/
theorem dualPairErasuresEqual :
    eraseDual (dualFinder 0) = eraseDual (dualFinder 1) ∧
    eraseDual (dualFinder 0) = eraseDual (dualFinder 2) := by
  constructor <;> funext t repo <;>
    simp only [eraseDual, dualFinder, FindResult.mk.injEq, true_and, and_true] <;>
    funext p <;> by_cases hp : p ∈ findSnatchSelected t.context ∩ repo.patterns <;>
    simp [hp, dualReceipt]

end
end DarkTower.WarMachine.Holes
