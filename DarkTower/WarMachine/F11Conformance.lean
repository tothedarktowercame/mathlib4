import DarkTower.WarMachine.Holes

/-! # F11 find-function conformance

This module states F1--F3 of `find` at the function grain from
`P-validated-R5.md:443-560`. F4 is separate because it quantifies over a
finder's possible inputs; `FindResult` (`Holes.lean:250-253`) has no `zeroMass`
field from which a single returned value could state it.
-/

open Set

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- F11 slice 2 signature, identical to refused `find` at `Holes.lean:264`. -/
abbrev FindType (State P : Type*) := Tension State → Repository P → FindResult P

/-- F11 slice 2 laws F1--F3 at the function grain of `P-validated-R5.md:471-479`; F4 is separately quantified by `FindFalsifiable`. -/
structure ConformantFind {State P : Type*} (f : FindType State P) : Prop where
  f1Containment : ∀ t repo, (f t repo).selected ⊆ repo.patterns
  f1TypedAbsence : ∀ t repo, (f t repo).selected = ∅ →
    (f t repo).absence = some .noPatternAddressesThisTension
  f2Receipted : ∀ t repo p, p ∈ (f t repo).selected →
    ((f t repo).receipts p).isSome
  f3NonSelfCertifying : ∀ t repo p r, p ∈ (f t repo).selected →
    (f t repo).receipts p = some r → r.nonSelfCertifying

/-- F11 slice 2 F4 at `P-validated-R5.md:478-479`: for each input with a nonempty repository, at least one repository member is excluded. This rules out a finder that may return the whole repository; it does not encode the row-only `zeroMass` field at `Holes.lean:259`. -/
def FindFalsifiable {State P : Type*} (f : FindType State P) : Prop :=
  ∀ t repo, repo.patterns.Nonempty → ∃ p ∈ repo.patterns, p ∉ (f t repo).selected

/-- F11 slice 2 recorded Snatch repository, converting `snatchRepository` at `Holes.lean:319` to the `Repository` carrier at `Holes.lean:121-124`. -/
def findSnatchRepository : Repository SnatchPattern where
  patterns := {p | p ∈ snatchRepository}
  standsOn := fun _ _ => False
  acyclic := by intro x path; cases path with | single h => exact h | tail _ h => exact h

/-- F11 slice 2 scenario-grain selection, read only from `findSnatchScenarios` at `Holes.lean:626`. -/
def findSnatchSelected (scenario : FindSnatchScenario) : Set SnatchPattern :=
  {p | ∃ row ∈ findSnatchScenarios, row.scenario = scenario ∧ p ∈ row.selected}

/-- F11 slice 2 structured-antecedent receipt corresponding to `find_snatch.clj:47-71`: it cites authored text/edges and is not score-alone. -/
def findStructuredReceipt : Receipt where
  citesTextOrEdges := True
  scoreAlone := False

/-- F11 slice 2 recorded replay implementation: scenario selection from `Holes.lean:626`, intersected with the repository argument for F1, with structured-antecedent receipts from `find_snatch.clj:47-71`. -/
def findSnatchReplay : FindType FindSnatchScenario SnatchPattern :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun _ => some findStructuredReceipt
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- F11 slice 2 F1--F3 conformance of the recorded replay at `P-validated-R5.md:471-477`. -/
theorem findSnatchReplayConformant : ConformantFind findSnatchReplay where
  f1Containment := by intro t repo p hp; exact hp.2
  f1TypedAbsence := by
    intro t repo h
    have hs : findSnatchSelected t.context ∩ repo.patterns = ∅ := by
      simpa [findSnatchReplay] using h
    simp [findSnatchReplay, hs]
  f2Receipted := by intro t repo p hp; simp [findSnatchReplay]
  f3NonSelfCertifying := by
    intro t repo p r hp hr
    simp [findSnatchReplay] at hr
    rw [← hr]
    simp [Receipt.nonSelfCertifying, findStructuredReceipt]

/-- F11 slice 2 total refusal: the empty selection carries F1's typed absence from `P-validated-R5.md:471-473`. -/
def findRefusing {State P : Type*} : FindType State P :=
  fun _ _ => { selected := ∅, receipts := fun _ => none,
               absence := some .noPatternAddressesThisTension }

/-- F11 slice 2 F1--F3 conformance of the refusing implementation at `P-validated-R5.md:471-477`. -/
theorem findRefusingConformant {State P : Type*} :
    ConformantFind (findRefusing (State := State) (P := P)) where
  f1Containment := by simp [findRefusing]
  f1TypedAbsence := by simp [findRefusing]
  f2Receipted := by simp [findRefusing]
  f3NonSelfCertifying := by simp [findRefusing]

/-- F11 slice 2 F4: refusal excludes every member of every nonempty repository, following `P-validated-R5.md:478-479`. -/
theorem findRefusingFalsifiable {State P : Type*} :
    FindFalsifiable (findRefusing (State := State) (P := P)) := by
  intro t repo h
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp, by simp [findRefusing]⟩

/-- F11 slice 2 identity implementation corresponding to the hand-authored Snatch row in `P-validated-R5.md:512-516`. -/
def findIdentity {State P : Type*} : FindType State P :=
  fun _ repo =>
    { selected := repo.patterns
      receipts := fun _ => some findStructuredReceipt
      absence := if repo.patterns = ∅ then some .noPatternAddressesThisTension else none }

/-- F11 slice 2 F1--F3 conformance of identity search, separating those laws from F4 at `P-validated-R5.md:471-479`. -/
theorem findIdentityConformant {State P : Type*} :
    ConformantFind (findIdentity (State := State) (P := P)) where
  f1Containment := by simp [findIdentity]
  f1TypedAbsence := by
    intro t repo h
    have hs : repo.patterns = ∅ := by simpa [findIdentity] using h
    simp [findIdentity, hs]
  f2Receipted := by simp [findIdentity]
  f3NonSelfCertifying := by
    intro t repo p r hp hr
    simp [findIdentity] at hr
    subst r
    simp [Receipt.nonSelfCertifying, findStructuredReceipt]

/-- F11 slice 2 F4 measurement from `P-validated-R5.md:478-479`: identity on a nonempty repository is unfalsifiable. -/
theorem findIdentityNotFalsifiable :
    ¬ FindFalsifiable (findIdentity (State := Unit) (P := SnatchPattern)) := by
  intro h
  let t : Tension Unit := { context := (), want := True, however := True }
  obtain ⟨p, hp, hnot⟩ := h t findSnatchRepository (by
    exact ⟨.aFreeMarkIsAlwaysWorthAssigning, by simp [findSnatchRepository, snatchRepository]⟩)
  exact hnot (by simpa [findIdentity] using hp)

/-- F11 slice 2 scenario-grain F4 on the committed Snatch table (`Holes.lean:817`): each recorded scenario has a repository member excluded by replay. -/
theorem findSnatchReplayFalsifiableOnRecordedRepository
    (t : Tension FindSnatchScenario) :
    ∃ p ∈ findSnatchRepository.patterns, p ∉ (findSnatchReplay t findSnatchRepository).selected := by
  cases t.context <;>
    simp [findSnatchReplay, findSnatchSelected, findSnatchRepository,
      findSnatchScenarios, snatchRepository]

/-- F11 slice 2 non-vacuity at the recorded `g1Snatcher` scenario (`Holes.lean:626`): replay selects the named recorded pattern `askForSurplusNotSurrender`. -/
theorem findSnatchReplaySelectsNamedPattern
    (want however : Prop) :
    SnatchPattern.askForSurplusNotSurrender ∈
      (findSnatchReplay
        { context := FindSnatchScenario.g1Snatcher, want := want, however := however }
        findSnatchRepository).selected := by
  simp [findSnatchReplay, findSnatchSelected, findSnatchRepository,
    findSnatchScenarios, snatchRepository]

/-- F11 slice 2 swappability witness from `P-validated-R5.md:501-518`: two F1--F3-conformant implementations differ on the recorded `g1Snatcher` input. -/
theorem findConformantImplementationsDifferOnSnatch :
    (findSnatchReplay
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).selected ≠
    (findRefusing
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).selected := by
  intro h
  have selected := findSnatchReplaySelectsNamedPattern True True
  rw [h] at selected
  simp [findRefusing] at selected

end

end DarkTower.WarMachine.Holes
