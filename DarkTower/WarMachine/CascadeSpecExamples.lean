import DarkTower.WarMachine.CascadeSpec

/-! GENERATED FILE — DO NOT EDIT.
Source: /var/www/zone.hyperreal.enterprises/2026-09-30-what-a-cascade-is.json
Source SHA-256: 021a66e66d230deaccfbad1e40681d00ce86ac042ed9bc37b85ef9375e4db7c7
Generator: futon2/scripts/wm_policy_set_to_lean.py
Generator commit: 26c7f9c2a
Target: M-distributed-proofreaders

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

#print axioms real_alternatives_counts
#print axioms real_overlap_counts
#print axioms real_reading_reported_count
#print axioms real_reading_structurally_distinct_count

end DarkTower.WarMachine.CascadeSpecExamples
