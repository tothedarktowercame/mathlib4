import DarkTower.WarMachine.Holes

/-! Item 20a/b/c, 2026-09-09. STATEMENT-ONLY controls on the applied carrier.
These synthetic results separate the readings; none is the opaque `find`,
and no implementation conformance or hole closure is claimed. -/
namespace DarkTower.WarMachine.Holes.F11RuledReadings

open Set

def repository : Repository Bool where
  patterns := Set.univ
  standsOn := fun _ _ => False
  acyclic := by
    intro x path
    cases path with
    | single h => exact h
    | tail _ h => exact h

def result (clause stamp : Nat) (text : Bool) : FindResult Bool Nat Nat Bool repository where
  selected := {false}
  receipts := fun _ _ =>
    { clauseKind := .ifClause, acknowledgedClause := clause
      route := .structuredAntecedent, asOf := stamp, citation := .patternText text }
  absence := none

def expected (clause stamp : Nat) : Bool → FindReceiptExpectation Nat Nat :=
  fun _ => ⟨.ifClause, clause, .structuredAntecedent, stamp⟩

def validText (p text : Bool) : Prop := text = p

theorem contentMatches : (result 7 1 false).contentF2 (expected 7 1) := by
  simp [FindResult.contentF2, result, expected]

theorem citationMatches : (result 7 1 false).citationF3 validText := by
  simp [FindResult.citationF3, FindCitation.validates, result, validText]

/-- Content succeeds with a different expectation; identity is not imposed. -/
theorem independentExpectation : (result 9 1 false).contentF2 (expected 9 1) := by
  simp [FindResult.contentF2, result, expected]

/-- Changing only citation preserves F2, but fails F3. -/
theorem citationSwapPreservesContent : (result 7 1 true).contentF2 (expected 7 1) := by
  simp [FindResult.contentF2, result, expected]

/-- Changing only clause preserves F3. -/
theorem clauseSwapPreservesCitation : (result 9 1 false).citationF3 validText := by
  simp [FindResult.citationF3, FindCitation.validates, result, validText]

/-- Finder-nominated exclusion succeeds, but is not external-designation F4. -/
theorem finderCanNominateExcluded :
    ∃ p ∈ repository.patterns, p ∉ (result 7 1 false).selected := by
  exact ⟨true, Set.mem_univ _, by simp [result]⟩

theorem emptyDesignationVacuous : (result 7 1 false).exclusionF4 ∅ := by
  simp [FindResult.exclusionF4]

theorem emptyDesignationEarnsNothing : ¬ (result 7 1 false).discriminatingF4 ∅ := by
  simp [FindResult.discriminatingF4]

/-- Vacuity depends on the applicable intersection, not on designation size. -/
theorem noApplicableDesignationEarnsNothing
    {P Clause AsOf TextCitation : Type*} {R : Repository P}
    (r : FindResult P Clause AsOf TextCitation R) (d : Set P)
    (h : d ∩ R.patterns = ∅) : ¬ r.discriminatingF4 d := by
  intro hd
  obtain ⟨p, hp⟩ := hd.1
  rw [h] at hp
  exact hp

theorem noApplicableDesignationVacuous
    {P Clause AsOf TextCitation : Type*} {R : Repository P}
    (r : FindResult P Clause AsOf TextCitation R) (d : Set P)
    (h : d ∩ R.patterns = ∅) : r.exclusionF4 d := by
  intro p hd hr
  have hp : p ∈ d ∩ R.patterns := ⟨hd, hr⟩
  rw [h] at hp
  exact hp.elim

-- Wrong acknowledged clause, despite a receipt and correct citation.
/-- error: unsolved goals
⊢ False -/
#guard_msgs in
example : (result 9 1 false).contentF2 (expected 7 1) := by
  simp [FindResult.contentF2, result, expected]

-- Wrong as-of, despite all other content matching.
/-- error: unsolved goals
⊢ False -/
#guard_msgs in
example : (result 7 2 false).contentF2 (expected 7 1) := by
  simp [FindResult.contentF2, result, expected]

-- F2 succeeds, but cannot substitute for the independently validated citation.
/-- error: unsolved goals
⊢ False -/
#guard_msgs in
example : (result 7 1 true).citationF3 validText := by
  simp [FindResult.citationF3, FindCitation.validates, result, validText]

-- The finder can nominate true as excluded; the external designation is false.
/-- error: unsolved goals
⊢ False -/
#guard_msgs in
example : (result 7 1 false).exclusionF4 {false} := by
  simp [FindResult.exclusionF4, result, repository]

-- Empty applicable designation earns no discrimination.
/-- error: unsolved goals
⊢ False -/
#guard_msgs in
example : (result 7 1 false).discriminatingF4 ∅ := by
  simp [FindResult.discriminatingF4]

#print axioms noApplicableDesignationEarnsNothing
#print axioms noApplicableDesignationVacuous
#print axioms contentMatches
#print axioms citationMatches
#print axioms independentExpectation
#print axioms citationSwapPreservesContent
#print axioms clauseSwapPreservesCitation
#print axioms finderCanNominateExcluded
#print axioms emptyDesignationVacuous
#print axioms emptyDesignationEarnsNothing

end DarkTower.WarMachine.Holes.F11RuledReadings
