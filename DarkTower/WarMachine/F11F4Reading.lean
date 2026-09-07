import DarkTower.WarMachine.F11DischargeArm

/-! # F11 slice 5: measuring the three readings of F4

The prose law says that a finder must not return a designated zero-mass pattern
(`futon2:holes/problems/P-validated-R5.md:488`).  The executable record declares
exactly one such pattern per scenario (`futon3:checks/find_snatch.clj:25-31`) and
checks only that declared pattern (`futon3:checks/find_snatch.clj:172-177`).
No second reason for an excluded pattern is recorded in the F4 leg: not found in
`futon3:checks/find_snatch.clj:100-113,172-177` or the scenario F4 fields in
`futon3:checks/find-snatch.edn`.

This module measures readings A, B, and C without selecting one.  Reading A is
`FindFalsifiable` (`F11Conformance.lean:31-32`); reading B is
`FindExcludesRecordedZeroMass` (`F11DischargeArm.lean:59-62`).
-/

open Set Classical

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- Reading C of `P-validated-R5.md:488`: zero mass is designated outside the
finder, indexed only by the tension context. -/
def FindRespectsZeroMass {State P : Type*} (zm : State → Set P)
    (f : FindType State P) : Prop :=
  ∀ t repo, ∀ p ∈ zm t.context, p ∈ repo.patterns → p ∉ (f t repo).selected

/-- The recorded designation is the set form of the list at `Holes.lean:342-348`. -/
def findSnatchZeroMassSet (s : FindSnatchScenario) : Set SnatchPattern :=
  {p | p ∈ findSnatchZeroMass s}

/-- M1a: reading C at the recorded designation implies reading B because B
tests only `findSnatchRepository` (`F11DischargeArm.lean:59-62`). -/
theorem findReadingCImpliesReadingB {f : FindType FindSnatchScenario SnatchPattern}
    (h : FindRespectsZeroMass findSnatchZeroMassSet f) :
    FindExcludesRecordedZeroMass f := by
  intro t p hp
  exact ⟨(findSnatchReplayExcludesDeclaredZeroMass t p hp).1,
    h t findSnatchRepository p hp
      (findSnatchReplayExcludesDeclaredZeroMass t p hp).1⟩

/-- M1a: replay satisfies reading C on every repository, strengthening its
recorded reading-B theorem at `F11Conformance.lean:176-180`. -/
theorem findSnatchReplayRespectsRecordedZeroMass :
    FindRespectsZeroMass findSnatchZeroMassSet findSnatchReplay := by
  intro t repo p hp hrepo hsel
  exact (findSnatchReplayExcludesDeclaredZeroMass t p hp).2
    ⟨hsel.1, (findSnatchReplayExcludesDeclaredZeroMass t p hp).1⟩

/-- M1a counterexample finder: it replays only on the exact recorded pattern set
from `F11Conformance.lean:35-39` and otherwise returns the whole repository. -/
def findReplayRecordedElseIdentity : FindType FindSnatchScenario SnatchPattern :=
  fun t repo =>
    if repo.patterns = findSnatchRepository.patterns then findSnatchReplay t repo
    else findIdentity t repo

/-- M1a named nondegenerate repository: g1's designated zero-mass pattern from
`Holes.lean:342-344` is its sole member. -/
def findG1ZeroMassSingleton : Repository SnatchPattern where
  patterns := {.consultTheRemedyBeforeExiting}
  standsOn := fun _ _ => False
  acyclic := by intro x path; cases path with | single h => exact h | tail _ h => exact h

/-- M1a exact gap: reading B does not imply reading C because B observes only
the recorded repository (`F11DischargeArm.lean:59-62`). -/
theorem findReadingBDoesNotImplyReadingC :
    FindExcludesRecordedZeroMass findReplayRecordedElseIdentity ∧
      ¬ FindRespectsZeroMass findSnatchZeroMassSet findReplayRecordedElseIdentity := by
  constructor
  · intro t p hp
    simpa [findReplayRecordedElseIdentity] using
      (findSnatchReplayExcludesDeclaredZeroMass t p hp)
  · intro h
    have hne : findG1ZeroMassSingleton.patterns ≠ findSnatchRepository.patterns := by
      intro heq
      have : SnatchPattern.askForSurplusNotSurrender ∈ findG1ZeroMassSingleton.patterns :=
        heq ▸ (by simp [findSnatchRepository, snatchRepository])
      simp [findG1ZeroMassSingleton] at this
    have hout := h
      { context := .g1Snatcher, want := True, however := True }
      findG1ZeroMassSingleton .consultTheRemedyBeforeExiting
      (by simp [findSnatchZeroMassSet, findSnatchZeroMass])
      (by simp [findG1ZeroMassSingleton])
    apply hout
    rw [findReplayRecordedElseIdentity, if_neg hne]
    simp [findIdentity, findG1ZeroMassSingleton]

/-- M1 floor: the B-not-C counterexample selects its designated pattern on the
named nonempty repository at `F11F4Reading.lean:61-64`. -/
theorem findReplayRecordedElseIdentitySelectionNonempty :
    ((findReplayRecordedElseIdentity
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findG1ZeroMassSingleton).selected).Nonempty := by
  have hne : findG1ZeroMassSingleton.patterns ≠ findSnatchRepository.patterns := by
    intro heq
    have : SnatchPattern.askForSurplusNotSurrender ∈ findG1ZeroMassSingleton.patterns :=
      heq ▸ (by simp [findSnatchRepository, snatchRepository])
    simp [findG1ZeroMassSingleton] at this
  exact ⟨.consultTheRemedyBeforeExiting, by
    rw [findReplayRecordedElseIdentity, if_neg hne]
    simp [findG1ZeroMassSingleton, findIdentity]⟩

/-- M1 floor: replay selects a pattern on the recorded repository, as witnessed
at `F11Conformance.lean:221-228`. -/
theorem findSnatchReplaySelectionNonempty :
    ((findSnatchReplay
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).selected).Nonempty :=
  ⟨.askForSurplusNotSurrender, findSnatchReplaySelectsNamedPattern True True⟩

/-- M1b: C does not imply A.  With the empty external designation C is
vacuous, while identity refutes A at `F11Conformance.lean:162-169`. -/
theorem findReadingCDoesNotImplyReadingA :
    FindRespectsZeroMass (fun _ : Unit => (∅ : Set SnatchPattern)) findIdentity ∧
      ¬ FindFalsifiable (findIdentity (State := Unit) (P := SnatchPattern)) := by
  exact ⟨by simp [FindRespectsZeroMass], findIdentityNotFalsifiable⟩

/-- M1b, review addition: the separation above is proved at the EMPTY
designation, where C asserts nothing, so on its own it says only that a vacuous
C does not imply A.  At the RECORDED designation (`Holes.lean:342-348`) the
separation still holds and is witnessed by a finder that selects: replay
satisfies C on every repository (`F11F4Reading.lean:44-49`) and refutes A
(`F11Conformance.lean:207-218`), and its selection on the recorded repository is
nonempty (`F11F4Reading.lean:107-112`).  Without this the C-not-A verdict was
the vacuous form the packet's floor was written against, in its DESIGNATION
guise rather than its finder guise. -/
theorem findRecordedReadingCDoesNotImplyReadingA :
    FindRespectsZeroMass findSnatchZeroMassSet findSnatchReplay ∧
      ¬ FindFalsifiable findSnatchReplay :=
  ⟨findSnatchReplayRespectsRecordedZeroMass, findSnatchReplayNotFalsifiable⟩

/-- M1b: A does not imply C at the recorded designation: the `findAllBut`
witness from `F11DischargeArm.lean:207-214` returns g4's designated member. -/
theorem findReadingADoesNotImplyRecordedReadingC :
    FindFalsifiable
        (findAllBut (State := FindSnatchScenario)
          SnatchPattern.consultTheRemedyBeforeExiting) ∧
      ¬ FindRespectsZeroMass findSnatchZeroMassSet
        (findAllBut (State := FindSnatchScenario)
          SnatchPattern.consultTheRemedyBeforeExiting) := by
  refine ⟨findAllButFalsifiable _, ?_⟩
  intro h
  have hout := h
    { context := FindSnatchScenario.g4Snatcher, want := True, however := True }
    findSnatchRepository .forcedPlayNeedsALossFloor (by simp [findSnatchZeroMassSet, findSnatchZeroMass])
    (by simp [findSnatchRepository, snatchRepository])
  exact hout (by simp [findAllBut, findSnatchRepository, snatchRepository])

/-- M1 floor: the non-vacuous A-not-C witness selects on the recorded repository
(`F11DischargeArm.lean:225-244`). -/
theorem findAllButConsultSelectionNonempty :
    ((findAllBut (State := FindSnatchScenario)
      SnatchPattern.consultTheRemedyBeforeExiting
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).selected).Nonempty := by
  exact ⟨.askForSurplusNotSurrender,
    by simp [findAllBut, findSnatchRepository, snatchRepository]⟩

/-- M2 verdict: replay satisfies B but not A, by
`F11Conformance.lean:176-180,207-218`. -/
theorem findSnatchReplayNotBothReadings :
    FindExcludesRecordedZeroMass findSnatchReplay ∧
      ¬ FindFalsifiable findSnatchReplay :=
  ⟨findSnatchReplayExcludesDeclaredZeroMass, findSnatchReplayNotFalsifiable⟩

/-- M2 verdict: total refusal satisfies both A and B
(`F11Conformance.lean:133-138`; `F11DischargeArm.lean:140-147`). -/
theorem findRefusingSatisfiesBothReadings :
    FindFalsifiable (findRefusing (State := FindSnatchScenario) (P := SnatchPattern)) ∧
      FindExcludesRecordedZeroMass
        (findRefusing (State := FindSnatchScenario) (P := SnatchPattern)) :=
  ⟨findRefusingFalsifiable, findRefusingExcludesRecordedZeroMass⟩

/-- M2 verdict: identity refutes A and B on the nonempty recorded repository
(`F11Conformance.lean:162-169`; `Holes.lean:342-348`). -/
theorem findIdentitySatisfiesNeitherReading :
    ¬ FindFalsifiable (findIdentity (State := FindSnatchScenario) (P := SnatchPattern)) ∧
      ¬ FindExcludesRecordedZeroMass
        (findIdentity (State := FindSnatchScenario) (P := SnatchPattern)) := by
  constructor
  · intro h
    obtain ⟨p, hp, hout⟩ := h
      { context := .g1Snatcher, want := True, however := True }
      findSnatchRepository findSnatchRepositoryNonempty
    exact hout (by simpa [findIdentity] using hp)
  · intro h
    have := (h { context := .g1Snatcher, want := True, however := True }
      .consultTheRemedyBeforeExiting (by simp [findSnatchZeroMass])).2
    exact this (by simp [findIdentity, findSnatchRepository, snatchRepository])

/-- M2 verdict: the named `findAllBut` witness satisfies A and refutes B, exactly
as measured at `F11DischargeArm.lean:207-214`. -/
theorem findAllButConsultNotBothReadings :
    FindFalsifiable
        (findAllBut (State := FindSnatchScenario)
          SnatchPattern.consultTheRemedyBeforeExiting) ∧
      ¬ FindExcludesRecordedZeroMass
        (findAllBut (State := FindSnatchScenario)
          SnatchPattern.consultTheRemedyBeforeExiting) :=
  ⟨findAllButFalsifiable _, findAllButFailsReadingB⟩

/-- M2 verdict: silent output satisfies A and B, although it is not F1--F3
conformant (`F11DischargeArm.lean:26-42`). -/
theorem findSilentSatisfiesBothReadings :
    FindFalsifiable (findSilent (State := FindSnatchScenario) (P := SnatchPattern)) ∧
      FindExcludesRecordedZeroMass
        (findSilent (State := FindSnatchScenario) (P := SnatchPattern)) := by
  constructor
  · intro t repo hn
    obtain ⟨p, hp⟩ := hn
    exact ⟨p, hp, by simp [findSilent]⟩
  · intro t p hp
    exact ⟨(findSnatchReplayExcludesDeclaredZeroMass t p hp).1, by simp [findSilent]⟩

/-- M2 construction: replay on a repository with the recorded pattern set and
refuse elsewhere.  This tests the dispatch premise against the exact recorded
repository at `F11Conformance.lean:35-39`. -/
def findReplayRecordedElseRefuse : FindType FindSnatchScenario SnatchPattern :=
  fun t repo =>
    if repo.patterns = findSnatchRepository.patterns then findSnatchReplay t repo
    else findRefusing t repo

/-- M2 floor: the hybrid used in the reproduction claim selects the named
recorded member on `findSnatchRepository` (`F11Conformance.lean:221-228`). -/
theorem findReplayRecordedElseRefuseSelectionNonempty :
    ((findReplayRecordedElseRefuse
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).selected).Nonempty := by
  simpa [findReplayRecordedElseRefuse] using findSnatchReplaySelectionNonempty

/-- M2 cost, measured: the dispatch premise is refuted.  This finder is
F1--F3 conformant, satisfies A ∧ B, and reproduces every recorded selection;
its A obligation on other repositories is paid by refusal
(`F11Conformance.lean:120-138`). -/
theorem bothReadingFinderReproducesEveryRecordedSelection :
    ConformantFind findReplayRecordedElseRefuse ∧
      FindFalsifiable findReplayRecordedElseRefuse ∧
      FindExcludesRecordedZeroMass findReplayRecordedElseRefuse ∧
      ∀ t, (findReplayRecordedElseRefuse t findSnatchRepository).selected =
        (findSnatchReplay t findSnatchRepository).selected := by
  constructor
  · constructor
    · intro t repo p hp
      by_cases h : repo.patterns = findSnatchRepository.patterns
      · simp only [findReplayRecordedElseRefuse, h, if_true] at hp ⊢
        have hin := findSnatchReplayConformant.f1Containment t repo hp
        simpa [h] using hin
      · simp [findReplayRecordedElseRefuse, h, findRefusing] at hp
    · intro t repo hs
      by_cases h : repo.patterns = findSnatchRepository.patterns
      · simpa [findReplayRecordedElseRefuse, h] using
          (findSnatchReplayConformant.f1TypedAbsence t repo (by
            simpa [findReplayRecordedElseRefuse, h] using hs))
      · simp [findReplayRecordedElseRefuse, h, findRefusing]
    · intro t repo p hp
      by_cases h : repo.patterns = findSnatchRepository.patterns
      · simp only [findReplayRecordedElseRefuse, h, if_true] at hp ⊢
        exact findSnatchReplayConformant.f2Receipted t repo p hp
      · simp [findReplayRecordedElseRefuse, h, findRefusing] at hp
    · intro t repo p r hp hr
      by_cases h : repo.patterns = findSnatchRepository.patterns
      · exact findSnatchReplayConformant.f3NonSelfCertifying t repo p r
          (by simpa [findReplayRecordedElseRefuse, h] using hp)
          (by simpa [findReplayRecordedElseRefuse, h] using hr)
      · simp [findReplayRecordedElseRefuse, h, findRefusing] at hp
  · constructor
    · intro t repo hn
      by_cases h : repo.patterns = findSnatchRepository.patterns
      · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _
          (findSnatchZeroMassNonempty t.context)
        exact ⟨p, h ▸ (findSnatchReplayExcludesDeclaredZeroMass t p hp).1,
          by simpa [findReplayRecordedElseRefuse, h, findSnatchReplay] using
            (findSnatchReplayExcludesDeclaredZeroMass t p hp).2⟩
      · obtain ⟨p, hp⟩ := hn
        exact ⟨p, hp, by simp [findReplayRecordedElseRefuse, h, findRefusing]⟩
    · constructor
      · intro t p hp
        simpa [findReplayRecordedElseRefuse] using
          (findSnatchReplayExcludesDeclaredZeroMass t p hp)
      · intro t
        simp [findReplayRecordedElseRefuse]

/-- M2, review addition, leg 1: every pattern any recorded row selects is in the
recorded repository -- F1 containment at the record grain, decided over the rows
of `findSnatchScenarios` (`Holes.lean:626`) against `snatchRepository`
(`Holes.lean:319`). -/
theorem findSnatchRecordedSelectionsAreInRepository :
    ∀ row ∈ findSnatchScenarios, ∀ p ∈ row.selected, p ∈ snatchRepository := by decide

/-- M2, review addition, leg 2: so intersecting with the repository drops
nothing the record selected. -/
theorem findSnatchSelectedSubsetRepository (scenario : FindSnatchScenario) :
    findSnatchSelected scenario ⊆ findSnatchRepository.patterns := by
  rintro p ⟨row, hrow, _, hmem⟩
  exact findSnatchRecordedSelectionsAreInRepository row hrow p hmem

/-- M2, review addition: what makes the reproduction claim a claim about the
RECORD.  The theorem above states that the hybrid's selection equals REPLAY's,
which is one step short: `findSnatchReplay` intersects with `repo.patterns`
(`F11Conformance.lean:72-78`), so equality with replay would still hold if the
record had selected a pattern outside its own repository and replay had silently
dropped it.  It did not -- and here the hybrid's selection on the recorded
repository is the recorded scenario-grain selection itself
(`F11Conformance.lean:41-44`), read from the rows at `Holes.lean:626`. -/
theorem bothReadingFinderSelectionIsTheRecordedSelection (t : Tension FindSnatchScenario) :
    (findReplayRecordedElseRefuse t findSnatchRepository).selected
      = findSnatchSelected t.context := by
  simp only [findReplayRecordedElseRefuse, findSnatchReplay]
  exact Set.inter_eq_left.mpr (findSnatchSelectedSubsetRepository t.context)

/-- M3: the executable F4 leg carries a designated member and tests precisely
repository membership plus exclusion (`futon3:checks/find_snatch.clj:172-177`). -/
theorem recordedReadingBCarriesItsDeclaredWitness (t : Tension FindSnatchScenario) :
    ∀ p ∈ findSnatchZeroMass t.context,
      p ∈ findSnatchRepository.patterns ∧
        p ∉ (findSnatchReplay t findSnatchRepository).selected :=
  findSnatchReplayExcludesDeclaredZeroMass t

/-- M4A: F1--F3 plus reading A admits a finder selecting nothing
(`F11Conformance.lean:120-138`). -/
theorem readingAAdmitsNothingFinder :
    ConformantFind (findRefusing (State := FindSnatchScenario) (P := SnatchPattern)) ∧
      FindFalsifiable (findRefusing (State := FindSnatchScenario) (P := SnatchPattern)) :=
  ⟨findRefusingConformant, findRefusingFalsifiable⟩

/-- M4B: F1--F3 plus reading B admits the same nothing finder
(`F11DischargeArm.lean:140-147`). -/
theorem readingBAdmitsNothingFinder :
    ConformantFind (findRefusing (State := FindSnatchScenario) (P := SnatchPattern)) ∧
      FindExcludesRecordedZeroMass
        (findRefusing (State := FindSnatchScenario) (P := SnatchPattern)) :=
  ⟨findRefusingConformant, findRefusingExcludesRecordedZeroMass⟩

/-- M4C: F1--F3 plus reading C admits a finder selecting nothing, for every
external designation (`P-validated-R5.md:488`). -/
theorem readingCAdmitsNothingFinder {State P : Type*} (zm : State → Set P) :
    ConformantFind (findRefusing (State := State) (P := P)) ∧
      FindRespectsZeroMass zm (findRefusing (State := State) (P := P)) := by
  exact ⟨findRefusingConformant, by simp [FindRespectsZeroMass, findRefusing]⟩

end

end DarkTower.WarMachine.Holes
