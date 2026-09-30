import DarkTower.WarMachine.CascadeSpec

/-! GENERATED FILE — DO NOT EDIT.
Source: /var/www/zone.hyperreal.enterprises/2026-09-30-what-a-cascade-is.json
Source SHA-256: 021a66e66d230deaccfbad1e40681d00ce86ac042ed9bc37b85ef9375e4db7c7
Generator: futon2/scripts/wm_policy_set_to_lean.py
Generator commit: 979c4b66c
Target: M-distributed-proofreaders
Theorems using `native_decide`: `real_reading_structurally_distinct_count`,
`real_policy_members_count`.

Pattern numbering:
  0 = agent/handoff-preserves-context
  1 = apparatus/new-failure-class-is-a-design-defect
  2 = peeragogy/use-or-make
  3 = relationship-coherence/rupture-repair
  4 = ukrns/publication-cadence
  5 = war-machine/operational-not-decorative
  6 = war-room/wr-18-war-machine-is-demonstrated-not-hypothesised
-/

namespace DarkTower.WarMachine.CascadeSpecExamples
open DarkTower.WarMachine.CascadeSpec

def realLibrary : Library := {0, 1, 2, 3, 4, 5, 6}

/-- Empty source fragments are retained; `supportedUnits` performs the same
skip as `analysis->cascades`. -/
def realReading : Reading realLibrary :=
  ⟨[
    ⟨[⟨5, by decide⟩]⟩,
    ⟨[]⟩,
    ⟨[]⟩,
    ⟨[⟨1, by decide⟩]⟩,
    ⟨[]⟩,
    ⟨[⟨4, by decide⟩]⟩,
    ⟨[]⟩,
    ⟨[]⟩
  ]⟩

/-- The export records graph kind but not numeric weight. Weight is set to one;
none of the provenance theorems observes it. -/
def realGraph : PatternGraph realLibrary where
  edges := {
    ⟨0, 1, by decide, (1 : ℚ), none, by simp⟩,
    ⟨0, 4, by decide, (1 : ℚ), none, by simp⟩,
    ⟨1, 2, by decide, (1 : ℚ), none, by simp⟩,
    ⟨1, 3, by decide, (1 : ℚ), none, by simp⟩,
    ⟨1, 6, by decide, (1 : ℚ), none, by simp⟩,
    ⟨2, 5, by decide, (1 : ℚ), none, by simp⟩,
    ⟨3, 5, by decide, (1 : ℚ), none, by simp⟩,
    ⟨5, 6, by decide, (1 : ℚ), none, by simp⟩
  }
  endpointsInLibrary := by simp [realLibrary]

def counts (c : Cascade realLibrary) : Nat × Nat × Nat :=
  (c.units.card, c.precedes.card, c.overlap.card)

theorem real_alternatives_counts :
    (readingCascades .alternatives realReading).map counts = [(3, 2, 0)] := by
  simp +decide [readingCascades, readingFactsB, rawReadingCascades, realReading,
    realLibrary, supportedUnits, fragmentUnitsAux, unitsAt, unitsAtAux, alternatives,
    cascadeOfUnits?, counts, directedEdges, adjacentFragments, overlapPairs, readingFragment]

theorem real_overlap_counts :
    (readingCascades .overlap realReading).map counts = [(3, 2, 0)] := by
  simp +decide [readingCascades, readingFactsB, rawReadingCascades, realReading,
    realLibrary, supportedUnits, fragmentUnitsAux, unitsAt, unitsAtAux, cascadeOfUnits?,
    counts, directedEdges, adjacentFragments, overlapPairs, readingFragment]

theorem real_reading_reported_count : (allReadingCascades realReading).length = 2 := by
  have ha := congrArg List.length real_alternatives_counts
  have ho := congrArg List.length real_overlap_counts
  simpa [allReadingCascades] using congrArg₂ (· + ·) ha ho

theorem real_reading_structurally_distinct_count :
    (structuralDedup (allReadingCascades realReading)).length = 1 := by
  simp +decide [allReadingCascades, readingCascades, readingFactsB, rawReadingCascades,
    realReading, realLibrary, supportedUnits, fragmentUnitsAux, unitsAt, unitsAtAux,
    alternatives, cascadeOfUnits?, directedEdges, adjacentFragments, overlapPairs,
    readingFragment]
  rw [structuralDedup.eq_def]
  native_decide

def realRetraction1Unit0 : Unit realLibrary :=
  ⟨0, 0, by decide, none⟩

def realRetraction1Unit1 : Unit realLibrary :=
  ⟨1, 1, by decide, none⟩

def realRetraction1Unit2 : Unit realLibrary :=
  ⟨2, 2, by decide, none⟩

def realRetraction1Unit3 : Unit realLibrary :=
  ⟨3, 4, by decide, none⟩

def realRetraction1Unit4 : Unit realLibrary :=
  ⟨4, 5, by decide, none⟩

def realRetraction1 : Cascade realLibrary where
  units := {realRetraction1Unit0, realRetraction1Unit1, realRetraction1Unit2, realRetraction1Unit3, realRetraction1Unit4}
  nonempty := by simp
  precedes := {}
  overlap := {⟨realRetraction1Unit0, realRetraction1Unit1, by decide⟩, ⟨realRetraction1Unit0, realRetraction1Unit3, by decide⟩, ⟨realRetraction1Unit1, realRetraction1Unit2, by decide⟩, ⟨realRetraction1Unit2, realRetraction1Unit4, by decide⟩}
  labelsInLibrary := fun u _ => u.inLibrary
  precedesEndpoints := by simp
  overlapEndpoints := by simp
  rank := fun u => u.id
  precedesForward := by simp [realRetraction1Unit0, realRetraction1Unit1, realRetraction1Unit2, realRetraction1Unit3, realRetraction1Unit4]

theorem realRetraction1_contains_usable_seeds :
    ∀ seed ∈ realReading.usableSeeds realGraph, realRetraction1.containsPattern seed := by
  simp [Reading.usableSeeds, Reading.citedPatterns, PatternGraph.incident,
    Cascade.containsPattern, realReading, realGraph, realRetraction1,
    realRetraction1Unit0, realRetraction1Unit1, realRetraction1Unit2, realRetraction1Unit3, realRetraction1Unit4]

theorem realRetraction1_precedes_authored :
    ∀ e ∈ realRetraction1.precedes, authoredGraphEdge realGraph e.1.pattern e.2.pattern := by
  simp [realRetraction1]

theorem realRetraction1_overlap_unauthored :
    ∀ e ∈ realRetraction1.overlap, overlapGraphEdge realGraph e.left.pattern e.right.pattern := by
  simp [overlapGraphEdge, realGraph, realRetraction1, realRetraction1Unit0, realRetraction1Unit1, realRetraction1Unit2, realRetraction1Unit3, realRetraction1Unit4]

def realRetraction2Unit0 : Unit realLibrary :=
  ⟨0, 0, by decide, none⟩

def realRetraction2Unit1 : Unit realLibrary :=
  ⟨1, 1, by decide, none⟩

def realRetraction2Unit2 : Unit realLibrary :=
  ⟨2, 3, by decide, none⟩

def realRetraction2Unit3 : Unit realLibrary :=
  ⟨3, 4, by decide, none⟩

def realRetraction2Unit4 : Unit realLibrary :=
  ⟨4, 5, by decide, none⟩

def realRetraction2 : Cascade realLibrary where
  units := {realRetraction2Unit0, realRetraction2Unit1, realRetraction2Unit2, realRetraction2Unit3, realRetraction2Unit4}
  nonempty := by simp
  precedes := {}
  overlap := {⟨realRetraction2Unit0, realRetraction2Unit1, by decide⟩, ⟨realRetraction2Unit0, realRetraction2Unit3, by decide⟩, ⟨realRetraction2Unit1, realRetraction2Unit2, by decide⟩, ⟨realRetraction2Unit2, realRetraction2Unit4, by decide⟩}
  labelsInLibrary := fun u _ => u.inLibrary
  precedesEndpoints := by simp
  overlapEndpoints := by simp
  rank := fun u => u.id
  precedesForward := by simp [realRetraction2Unit0, realRetraction2Unit1, realRetraction2Unit2, realRetraction2Unit3, realRetraction2Unit4]

theorem realRetraction2_contains_usable_seeds :
    ∀ seed ∈ realReading.usableSeeds realGraph, realRetraction2.containsPattern seed := by
  simp [Reading.usableSeeds, Reading.citedPatterns, PatternGraph.incident,
    Cascade.containsPattern, realReading, realGraph, realRetraction2,
    realRetraction2Unit0, realRetraction2Unit1, realRetraction2Unit2, realRetraction2Unit3, realRetraction2Unit4]

theorem realRetraction2_precedes_authored :
    ∀ e ∈ realRetraction2.precedes, authoredGraphEdge realGraph e.1.pattern e.2.pattern := by
  simp [realRetraction2]

theorem realRetraction2_overlap_unauthored :
    ∀ e ∈ realRetraction2.overlap, overlapGraphEdge realGraph e.left.pattern e.right.pattern := by
  simp [overlapGraphEdge, realGraph, realRetraction2, realRetraction2Unit0, realRetraction2Unit1, realRetraction2Unit2, realRetraction2Unit3, realRetraction2Unit4]

def realRetraction3Unit0 : Unit realLibrary :=
  ⟨0, 0, by decide, none⟩

def realRetraction3Unit1 : Unit realLibrary :=
  ⟨1, 1, by decide, none⟩

def realRetraction3Unit2 : Unit realLibrary :=
  ⟨2, 4, by decide, none⟩

def realRetraction3Unit3 : Unit realLibrary :=
  ⟨3, 5, by decide, none⟩

def realRetraction3Unit4 : Unit realLibrary :=
  ⟨4, 6, by decide, none⟩

def realRetraction3 : Cascade realLibrary where
  units := {realRetraction3Unit0, realRetraction3Unit1, realRetraction3Unit2, realRetraction3Unit3, realRetraction3Unit4}
  nonempty := by simp
  precedes := {}
  overlap := {⟨realRetraction3Unit0, realRetraction3Unit1, by decide⟩, ⟨realRetraction3Unit0, realRetraction3Unit2, by decide⟩, ⟨realRetraction3Unit1, realRetraction3Unit4, by decide⟩, ⟨realRetraction3Unit3, realRetraction3Unit4, by decide⟩}
  labelsInLibrary := fun u _ => u.inLibrary
  precedesEndpoints := by simp
  overlapEndpoints := by simp
  rank := fun u => u.id
  precedesForward := by simp [realRetraction3Unit0, realRetraction3Unit1, realRetraction3Unit2, realRetraction3Unit3, realRetraction3Unit4]

theorem realRetraction3_contains_usable_seeds :
    ∀ seed ∈ realReading.usableSeeds realGraph, realRetraction3.containsPattern seed := by
  simp [Reading.usableSeeds, Reading.citedPatterns, PatternGraph.incident,
    Cascade.containsPattern, realReading, realGraph, realRetraction3,
    realRetraction3Unit0, realRetraction3Unit1, realRetraction3Unit2, realRetraction3Unit3, realRetraction3Unit4]

theorem realRetraction3_precedes_authored :
    ∀ e ∈ realRetraction3.precedes, authoredGraphEdge realGraph e.1.pattern e.2.pattern := by
  simp [realRetraction3]

theorem realRetraction3_overlap_unauthored :
    ∀ e ∈ realRetraction3.overlap, overlapGraphEdge realGraph e.left.pattern e.right.pattern := by
  simp [overlapGraphEdge, realGraph, realRetraction3, realRetraction3Unit0, realRetraction3Unit1, realRetraction3Unit2, realRetraction3Unit3, realRetraction3Unit4]

def realRetractions : List (Cascade realLibrary) :=
  [realRetraction1, realRetraction2, realRetraction3]

theorem real_policy_members_count :
    (structuralDedup (allReadingCascades realReading ++ realRetractions)).length = 4 := by
  simp +decide [allReadingCascades, readingCascades, readingFactsB, rawReadingCascades,
    realReading, realLibrary, supportedUnits, fragmentUnitsAux, unitsAt, unitsAtAux,
    alternatives, cascadeOfUnits?, directedEdges, adjacentFragments, overlapPairs,
    readingFragment, realRetractions]
  rw [structuralDedup.eq_def]
  native_decide

#print axioms real_alternatives_counts
#print axioms real_overlap_counts
#print axioms real_reading_reported_count
#print axioms real_reading_structurally_distinct_count
#print axioms realRetraction1_contains_usable_seeds
#print axioms realRetraction1_precedes_authored
#print axioms realRetraction1_overlap_unauthored
#print axioms realRetraction2_contains_usable_seeds
#print axioms realRetraction2_precedes_authored
#print axioms realRetraction2_overlap_unauthored
#print axioms realRetraction3_contains_usable_seeds
#print axioms realRetraction3_precedes_authored
#print axioms realRetraction3_overlap_unauthored
#print axioms real_policy_members_count

end DarkTower.WarMachine.CascadeSpecExamples
