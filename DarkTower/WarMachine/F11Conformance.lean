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

/-- F11 slice 2 scenario-grain RECEIPTED column, read from the same rows of
`findSnatchScenarios` (`Holes.lean:626`) as `findSnatchSelected`.  Review
addition: without this the replay's `receipts` was a constant function that
returned a receipt for every pattern in the type, so F2 and F3 were witnessed
about a constant rather than about the record, and the fixture's `receipted`
and `nonSelfCertifying` columns went unread. -/
def findSnatchReceipted (scenario : FindSnatchScenario) : Set SnatchPattern :=
  {p | ∃ row ∈ findSnatchScenarios, row.scenario = scenario ∧ p ∈ row.receipted}

/-- F11 slice 2 review addition: on this record every selected member is
receipted, row by row -- the scenario-grain reading of `wmFindSnatchF2Receipted`
(`Holes.lean:788`).  This is what makes the replay's receipts total on its own
selection while remaining partial on the repository. -/
theorem findSnatchSelectedSubsetReceipted (scenario : FindSnatchScenario) :
    findSnatchSelected scenario ⊆ findSnatchReceipted scenario := by
  rintro p ⟨row, hrow, hsc, hmem⟩
  refine ⟨row, hrow, hsc, ?_⟩
  have hcases := hrow
  simp only [findSnatchScenarios, List.mem_cons, List.not_mem_nil, or_false] at hcases
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa using hmem

/-- F11 slice 2 structured-antecedent receipt corresponding to `find_snatch.clj:47-71`: it cites authored text/edges and is not score-alone. -/
def findStructuredReceipt : Receipt where
  citesTextOrEdges := True
  scoreAlone := False

open Classical in
/-- F11 slice 2 recorded replay implementation: scenario selection from `Holes.lean:626`, intersected with the repository argument for F1, with structured-antecedent receipts from `find_snatch.clj:47-71` issued exactly to the recorded receipted members. -/
def findSnatchReplay : FindType FindSnatchScenario SnatchPattern :=
  fun t repo =>
    let selected := findSnatchSelected t.context ∩ repo.patterns
    { selected := selected
      receipts := fun p =>
        if p ∈ findSnatchReceipted t.context then some findStructuredReceipt else none
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- F11 slice 2 F1--F3 conformance of the recorded replay at `P-validated-R5.md:471-477`. -/
theorem findSnatchReplayConformant : ConformantFind findSnatchReplay where
  f1Containment := by intro t repo p hp; exact hp.2
  f1TypedAbsence := by
    intro t repo h
    have hs : findSnatchSelected t.context ∩ repo.patterns = ∅ := by
      simpa [findSnatchReplay] using h
    simp [findSnatchReplay, hs]
  f2Receipted := by
    intro t repo p hp
    have hrec : p ∈ findSnatchReceipted t.context :=
      findSnatchSelectedSubsetReceipted t.context hp.1
    simp [findSnatchReplay, hrec]
  f3NonSelfCertifying := by
    intro t repo p r hp hr
    by_cases hrec : p ∈ findSnatchReceipted t.context
    · simp [findSnatchReplay, hrec] at hr
      rw [← hr]
      simp [Receipt.nonSelfCertifying, findStructuredReceipt]
    · simp [findSnatchReplay, hrec] at hr

/-- F11 slice 2 review addition: the replay's receipts are PARTIAL on the
repository -- `consultTheRemedyBeforeExiting` is one of the eighteen recorded
patterns and gets no receipt under `g1Snatcher`.  This is what the constant
receipt function could not say, and it is why F2 is now a claim about the
record.  Measured bound on how much it says: at the scenario grain the recorded
receipted column EQUALS the recorded selection in all six scenarios
(`futon3:checks/find-snatch.edn`), so what the partiality separates here is
repository from selection, not receipted from selected -- the same coincidence
`wmFindSnatchF3NonSelfCertifying` (`Holes.lean:803`) records for F3. -/
theorem findSnatchReplayReceiptsArePartial :
    (findSnatchReplay
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).receipts SnatchPattern.consultTheRemedyBeforeExiting = none ∧
    SnatchPattern.consultTheRemedyBeforeExiting ∈ findSnatchRepository.patterns := by
  constructor
  · simp [findSnatchReplay, findSnatchReceipted, findSnatchScenarios]
  · simp [findSnatchRepository, snatchRepository]

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

/-- F11 slice 2 review addition: the DECLARED zero-mass member is the one the
replay excludes.  `wmFindSnatchF4Falsifiable` (`Holes.lean:817`) is not the
claim that some pattern is missing -- any finder that is not the identity
satisfies that -- but that the pattern `find_snatch.clj:25-31` declared in
advance as zero-mass is in the repository and out of the selection.  Proved
over all six recorded scenarios. -/
theorem findSnatchReplayExcludesDeclaredZeroMass
    (t : Tension FindSnatchScenario) :
    ∀ p ∈ findSnatchZeroMass t.context,
      p ∈ findSnatchRepository.patterns ∧
        p ∉ (findSnatchReplay t findSnatchRepository).selected := by
  cases hc : t.context <;>
    simp [hc, findSnatchZeroMass, findSnatchReplay, findSnatchSelected,
      findSnatchRepository, findSnatchScenarios, snatchRepository]

/-- F11 slice 2 review addition: every recorded scenario declares a zero-mass
pattern, so the witness above is never drawn from an empty list. -/
theorem findSnatchZeroMassNonempty (scenario : FindSnatchScenario) :
    (findSnatchZeroMass scenario) ≠ [] := by
  cases scenario <;> simp [findSnatchZeroMass]

/-- F11 slice 2 scenario-grain F4 on the committed Snatch table (`Holes.lean:817`): each recorded scenario has a repository member excluded by replay.  Review change: the witness is now the declared zero-mass member rather than whichever pattern `simp` happened to find. -/
theorem findSnatchReplayFalsifiableOnRecordedRepository
    (t : Tension FindSnatchScenario) :
    ∃ p ∈ findSnatchRepository.patterns, p ∉ (findSnatchReplay t findSnatchRepository).selected := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (findSnatchZeroMassNonempty t.context)
  obtain ⟨hin, hout⟩ := findSnatchReplayExcludesDeclaredZeroMass t p hp
  exact ⟨p, hin, hout⟩

/-- F11 slice 2 review addition, and the measurement that bounds `FindFalsifiable`
itself: the recorded replay does NOT satisfy the universally quantified reading of
F4.  On a repository holding only `askForSurplusNotSurrender` -- a pattern every
recorded scenario selects -- the replay returns the whole repository and excludes
nothing.  So the ∀-over-inputs reading is refuted by the finder that replays the
committed record, while the scenario-grain instance
(`findSnatchReplayExcludesDeclaredZeroMass`) holds.  Which of the two readings
F4 is remains a choice, and this slice does not take it. -/
theorem findSnatchReplayNotFalsifiable : ¬ FindFalsifiable findSnatchReplay := by
  intro h
  let onePattern : Repository SnatchPattern :=
    { patterns := {SnatchPattern.askForSurplusNotSurrender}
      standsOn := fun _ _ => False
      acyclic := by intro x path; cases path with | single h => exact h | tail _ h => exact h }
  obtain ⟨p, hp, hout⟩ :=
    h { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      onePattern ⟨SnatchPattern.askForSurplusNotSurrender, rfl⟩
  have hpe : p = SnatchPattern.askForSurplusNotSurrender := hp
  subst hpe
  exact hout ⟨by simp [findSnatchSelected, findSnatchScenarios], hp⟩

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
