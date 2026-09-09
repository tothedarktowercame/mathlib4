import DarkTower.WarMachine.F11Conformance

/-! # F11 find discharge arm

This module measures inhabitance, two readings of F4, non-uniqueness, and
opacity at the exact refused `find` signature without selecting a discharge.
-/

open Set Classical

namespace DarkTower.WarMachine.Holes

noncomputable section

/-- F11 slice 3 R0.1: `FindType` at `F11Conformance.lean:18` is inhabited without assumptions by the refusal at `F11Conformance.lean:120`. -/
theorem findTypeNonempty {State P : Type*} : Nonempty (FindType State P) :=
  ⟨findRefusing⟩

/-- F11 slice 3 R0.2: unlike the empty organise inhabitant, the cheapest find inhabitant satisfies F1--F3 (`F11Conformance.lean:125`) and reading-A F4 (`F11Conformance.lean:133`). -/
theorem findRefusingMeetsConformanceAndReadingA {State P : Type*} :
    ConformantFind (findRefusing (State := State) (P := P)) ∧
      FindFalsifiable (findRefusing (State := State) (P := P)) :=
  ⟨findRefusingConformant, findRefusingFalsifiable⟩

/-- F11 slice 3 R0.3: silent empty output differs from the typed refusal at `F11Conformance.lean:120-122` by omitting F1's required absence. -/
def findSilent {State P : Type*} : FindType State P :=
  fun _ _ => { selected := ∅, receipts := fun _ => none, absence := none }

/-- F11 slice 3 R0.3, CORRECTED IN REVIEW: `findSilent` is not conformant because
`ConformantFind.f1TypedAbsence` at `F11Conformance.lean:23-24` fails.  As dispatched
this was witnessed on a repository with NO patterns, where the refutation is about a
degenerate input rather than about the record; it is now witnessed on the recorded
18-pattern `findSnatchRepository` (`F11Conformance.lean:35`), which
`findSnatchRepositoryNonempty` below shows is not empty. -/
theorem findSilentNotConformant :
    ¬ ConformantFind (findSilent (State := FindSnatchScenario) (P := SnatchPattern)) := by
  intro h
  have := h.f1TypedAbsence
    { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
    findSnatchRepository (by simp [findSilent])
  simp [findSilent] at this

/-- F11 slice 3 review addition: the recorded repository the refutation above is
witnessed on is inhabited, so that refutation is not vacuous. -/
theorem findSnatchRepositoryNonempty : findSnatchRepository.patterns.Nonempty :=
  ⟨.askForSurplusNotSurrender, by simp [findSnatchRepository, snatchRepository]⟩

/-- F11 slice 3 R1.1: an F1--F3 conformant discharge exists at `F11Conformance.lean:18`, witnessed independently of either F4 reading. -/
theorem findDischargeExists {State P : Type*} :
    ∃ f : FindType State P, ConformantFind f :=
  ⟨findRefusing, findRefusingConformant⟩

/-- F11 slice 3 R1.2: a conformant discharge exists under forall-inputs reading A (`F11Conformance.lean:31-32`). -/
theorem findDischargeExistsReadingA {State P : Type*} :
    ∃ f : FindType State P, ConformantFind f ∧ FindFalsifiable f :=
  ⟨findRefusing, findRefusingConformant, findRefusingFalsifiable⟩

/-- F11 slice 3 R1.3: record-grain reading B is the declared-zero-mass exclusion proved for replay at `F11Conformance.lean:176-180`; it does not choose reading A. -/
def FindExcludesRecordedZeroMass
    (f : FindType FindSnatchScenario SnatchPattern) : Prop :=
  ∀ t, ∀ p ∈ findSnatchZeroMass t.context,
    p ∈ findSnatchRepository.patterns ∧ p ∉ (f t findSnatchRepository).selected

/-- F11 slice 3 R1.3: a conformant reading-B discharge exists, using replay conformance at `F11Conformance.lean:81` and declared-zero-mass exclusion at `F11Conformance.lean:176`. -/
theorem findDischargeExistsReadingB :
    ∃ f : FindType FindSnatchScenario SnatchPattern,
      ConformantFind f ∧ FindExcludesRecordedZeroMass f :=
  ⟨findSnatchReplay, findSnatchReplayConformant,
    findSnatchReplayExcludesDeclaredZeroMass⟩

/-- F11 slice 3 R2.1: reading-A alternative selects every repository member except `q`, or refuses when `q` is absent; receipts use `findStructuredReceipt` at `F11Conformance.lean:66`. -/
def findAllBut {State P : Type*} (q : P) : FindType State P :=
  fun _ repo =>
    let selected := if q ∈ repo.patterns then repo.patterns \ {q} else ∅
    { selected := selected
      receipts := fun p => if p ∈ selected then some findStructuredReceipt else none
      absence := if selected = ∅ then some .noPatternAddressesThisTension else none }

/-- F11 slice 3 R2.1: `findAllBut` satisfies F1--F3 at `F11Conformance.lean:21-28`. -/
theorem findAllButConformant {State P : Type*} (q : P) :
    ConformantFind (findAllBut (State := State) q) where
  f1Containment := by
    intro t repo p hp
    by_cases hq : q ∈ repo.patterns
    · have hmem : p ∈ repo.patterns \ {q} := by
        simpa [findAllBut, hq] using hp
      exact hmem.1
    · simp [findAllBut, hq] at hp
  f1TypedAbsence := by
    intro t repo h
    have hs : (if q ∈ repo.patterns then repo.patterns \ {q} else ∅) = ∅ := by
      simpa [findAllBut] using h
    simp [findAllBut, hs]
  f2Receipted := by
    intro t repo p hp
    by_cases hq : q ∈ repo.patterns
    · have hp' : p ∈ repo.patterns \ {q} := by simpa [findAllBut, hq] using hp
      simp only [findAllBut, hq, if_true, mem_diff, mem_singleton_iff] at hp' ⊢
      simp [hp']
    · simp [findAllBut, hq] at hp
  f3NonSelfCertifying := by
    intro t repo p r hp hr
    by_cases hq : q ∈ repo.patterns
    · have hp' : p ∈ repo.patterns \ {q} := by simpa [findAllBut, hq] using hp
      simp [findAllBut, hq] at hr
      rw [← hr.2]
      simp [LegacyReceipt.nonSelfCertifying, findStructuredReceipt]
    · simp [findAllBut, hq] at hp

/-- F11 slice 3 R2.1: `findAllBut` satisfies forall-inputs reading A from `F11Conformance.lean:31-32`. -/
theorem findAllButFalsifiable {State P : Type*} (q : P) :
    FindFalsifiable (findAllBut (State := State) q) := by
  intro t repo hrepo
  by_cases hq : q ∈ repo.patterns
  · exact ⟨q, hq, by simp [findAllBut, hq]⟩
  · obtain ⟨p, hp⟩ := hrepo
    exact ⟨p, hp, by simp [findAllBut, hq]⟩

/-- F11 slice 3 R2.2: reading A has two conformant, falsifiable discharges with different selections on the recorded input used at `F11Conformance.lean:231-237`. -/
theorem findDischargeNotUniqueReadingA :
    ∃ f g : FindType FindSnatchScenario SnatchPattern,
      ConformantFind f ∧ FindFalsifiable f ∧ ConformantFind g ∧ FindFalsifiable g ∧
      (f { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
          findSnatchRepository).selected ≠
        (g { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
          findSnatchRepository).selected := by
  refine ⟨findAllBut .consultTheRemedyBeforeExiting, findRefusing,
    findAllButConformant _, findAllButFalsifiable _, findRefusingConformant,
    findRefusingFalsifiable, ?_⟩
  intro h
  have hp : SnatchPattern.askForSurplusNotSurrender ∈
      (findAllBut .consultTheRemedyBeforeExiting
        { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
        findSnatchRepository).selected := by
    simp [findAllBut, findSnatchRepository, snatchRepository]
  rw [h] at hp
  simp [findRefusing] at hp

/-- F11 slice 3 R2.3: total refusal also satisfies record-grain reading B from `F11Conformance.lean:176-180`. -/
theorem findRefusingExcludesRecordedZeroMass :
    FindExcludesRecordedZeroMass
      (findRefusing (State := FindSnatchScenario) (P := SnatchPattern)) := by
  intro t p hp
  constructor
  · exact (findSnatchReplayExcludesDeclaredZeroMass t p hp).1
  · simp [findRefusing]

/-- F11 slice 3 R2.3: reading B has two conformant discharges with different recorded selections (`F11Conformance.lean:231`). -/
theorem findDischargeNotUniqueReadingB :
    ∃ f g : FindType FindSnatchScenario SnatchPattern,
      ConformantFind f ∧ FindExcludesRecordedZeroMass f ∧
      ConformantFind g ∧ FindExcludesRecordedZeroMass g ∧
      (f { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
          findSnatchRepository).selected ≠
        (g { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
          findSnatchRepository).selected :=
  ⟨findSnatchReplay, findRefusing, findSnatchReplayConformant,
    findSnatchReplayExcludesDeclaredZeroMass, findRefusingConformant,
    findRefusingExcludesRecordedZeroMass, findConformantImplementationsDifferOnSnatch⟩

/-- F11 slice 3 R2.4a, AMENDED IN REVIEW to say what it does not carry.  Both
reading-B witnesses exclude every declared zero-mass member and the disagreement is
inhabited by the named member at `F11Conformance.lean:221` -- but `findRefusing`
excludes every pattern whatever, so its half of that agreement is vacuous, exactly
as in the reading-A pair.  Unlike reading A, reading B has NO cheap second witness
that actually selects: `findAllButFailsReadingB` below shows why.  So on this record
the two reading-B discharges are the finder that replays the record and the finder
that refuses, and that is the measurement rather than a gap in the search. -/
theorem findReadingBWitnessesAgreeOnFloor :
    FindExcludesRecordedZeroMass findSnatchReplay ∧
      FindExcludesRecordedZeroMass
        (findRefusing (State := FindSnatchScenario) (P := SnatchPattern)) ∧
      SnatchPattern.askForSurplusNotSurrender ∈
        (findSnatchReplay
          { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
          findSnatchRepository).selected :=
  ⟨findSnatchReplayExcludesDeclaredZeroMass,
    findRefusingExcludesRecordedZeroMass, findSnatchReplaySelectsNamedPattern True True⟩

/-- F11 slice 3 R2.4b, WEAKENED BY REVIEW AND KEPT ONLY AS THE WEAK FORM.  Both
reading-A witnesses do exclude `consultTheRemedyBeforeExiting`, but `findRefusing`
excludes EVERY pattern, so its half of that agreement is vacuous and the pair does
not locate where the two finders disagree.  The located version is
`findAllButPairDisagreesExactlyOnTheTwoZeroMassMembers` below, whose two witnesses
both select on the record. -/
theorem findReadingAWitnessesAgreeOnFloor :
    let q := SnatchPattern.consultTheRemedyBeforeExiting
    q ∉ (findAllBut q
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).selected ∧
    q ∉ (findRefusing
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
      findSnatchRepository).selected ∧
    (findSnatchRepository.patterns \ {q}).Nonempty := by
  refine ⟨by simp [findAllBut, findSnatchRepository, snatchRepository],
    by simp [findRefusing], ?_⟩
  exact ⟨.askForSurplusNotSurrender,
    by simp [findSnatchRepository, snatchRepository]⟩

/-- F11 slice 3 review addition: reading B bites harder than reading A, and this is
why the reading-B pair has to include the total refusal.  `findAllBut` at the
`g1` scenarios' declared zero-mass member still SELECTS `forcedPlayNeedsALossFloor`,
which the record declares zero-mass at `g4Snatcher` (`Holes.lean:346`), so it
satisfies reading A (`findAllButFalsifiable`) and refutes reading B.  A finder can
therefore exclude one pattern from every repository, as reading A asks, and still
return a pattern the record said in advance it must not. -/
theorem findAllButFailsReadingB :
    ¬ FindExcludesRecordedZeroMass
        (findAllBut (State := FindSnatchScenario) SnatchPattern.consultTheRemedyBeforeExiting) := by
  intro h
  have := (h { context := FindSnatchScenario.g4Snatcher, want := True, however := True }
    SnatchPattern.forcedPlayNeedsALossFloor (by simp [findSnatchZeroMass])).2
  exact this (by simp [findAllBut, findSnatchRepository, snatchRepository])

/-- F11 slice 3 review addition, and the reading-A floor the dispatched pair could not
carry.  Non-uniqueness under reading A was witnessed by `findAllBut` against
`findRefusing`, which selects nothing at all; "they differ" is then only the
observation that one of them refuses.  Here both witnesses are `findAllBut`
instances, at the two patterns the record declares zero-mass -- `consultTheRemedyBeforeExiting`
at `g1Snatcher` and `forcedPlayNeedsALossFloor` at `g4Snatcher`
(`find_snatch.clj:25-31`, transcribed at `Holes.lean:342`).  Both are conformant
(`findAllButConformant`) and reading-A falsifiable (`findAllButFalsifiable`), both
SELECT the recorded member `askForSurplusNotSurrender`, and the disagreement is
exactly the two excluded patterns: each finder selects the one the other drops. -/
theorem findAllButPairDisagreesExactlyOnTheTwoZeroMassMembers :
    let q := SnatchPattern.consultTheRemedyBeforeExiting
    let q' := SnatchPattern.forcedPlayNeedsALossFloor
    let t : Tension FindSnatchScenario :=
      { context := FindSnatchScenario.g1Snatcher, want := True, however := True }
    (SnatchPattern.askForSurplusNotSurrender ∈
        (findAllBut q t findSnatchRepository).selected ∧
      SnatchPattern.askForSurplusNotSurrender ∈
        (findAllBut q' t findSnatchRepository).selected) ∧
    (q ∉ (findAllBut q t findSnatchRepository).selected ∧
      q ∈ (findAllBut q' t findSnatchRepository).selected) ∧
    (q' ∈ (findAllBut q t findSnatchRepository).selected ∧
      q' ∉ (findAllBut q' t findSnatchRepository).selected) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
    simp [findAllBut, findSnatchRepository, snatchRepository]

/-- F11 slice 3 R3.1: opacity with an explicit refusing body hides that selected inhabitant; compare the bodiless measurement at `F12DischargeArm.lean:265-271`. -/
opaque findOpaqueRefusing : FindType Unit SnatchPattern := findRefusing

/-- F11 slice 3 R3.2: local inhabitance used only to elaborate the bodiless opaque declaration, following `F12DischargeArm.lean:258-263`. -/
local instance findTypeNonemptyInstance : Nonempty (FindType Unit SnatchPattern) :=
  findTypeNonempty

/-- F11 slice 3 R3.3: bodiless opacity requires only local `Nonempty`; `#print axioms` measures its `Classical.choice` cost as at `F12DischargeArm.lean:265-271`. -/
opaque findOpaqueNoBody : FindType Unit SnatchPattern

end


end DarkTower.WarMachine.Holes
