import DarkTower.WarMachine.PatternTheta

/-!
# Supplied pattern-observation admission

This module makes explicit the conditional boundary already required by
`PatternTheta`: a caller supplies an authority decision for a guard-held fire,
and only a matching, observed Boolean may become an existing
`R15TemporalHierarchy.FastOutcome`. It does not derive authority from selection,
prediction mass, a mission-hole observation, or the existence of an effect.

The arithmetic remains the model in `PatternTheta`. Its source discussion cites
`refs/friston2017.txt:352` (`Q(B) = Dir(b)`) and da Costa 2020 Appendix A.1 for
transition Dirichlet counts. Those sources motivate the count update; they do
not establish this domain-specific authority premise. The predicate and its
checker are therefore supplied parameters here.

Occurrence/effect/revision identify the admitted event. The `pattern` is the
separate parameter key: different admitted occurrences with the same pattern
continue to pool exactly as `PatternTheta.witnessedOutcomes` already specifies.
An observed `false` is distinct from absence and is admitted as failure only
when authority accepts it. Zero prediction mass is deliberately not an input
or a gate.
-/

namespace DarkTower.WarMachine.PatternObservationAdmission

open R15TemporalHierarchy

/-- The requested event binding. `pattern` is the shared theta parameter key;
the remaining fields identify this event. -/
structure Request (PatternKey Occurrence Effect Revision : Type) where
  pattern : PatternKey
  occurrence : Occurrence
  effect : Effect
  revision : Revision
  deriving DecidableEq, Repr

/-- A supplied observation keeps absence distinct from an observed `false`.
Authority evidence is also optional and independent of the Boolean payload. -/
structure SuppliedObservation (PatternKey Occurrence Effect Revision Evidence : Type) where
  pattern : PatternKey
  occurrence : Occurrence
  effect : Effect
  revision : Revision
  observed : Option Bool
  authorityEvidence : Option Evidence
  deriving DecidableEq, Repr

/-- A domain-supplied authority predicate plus an executable checker proved to
decide exactly that predicate. This wrapper chooses no authority semantics. -/
structure AuthorityCheck (Evidence PatternKey Occurrence Effect Revision : Type) where
  Admits : Evidence → Request PatternKey Occurrence Effect Revision → Prop
  check : Evidence → Request PatternKey Occurrence Effect Revision → Bool
  check_iff : ∀ e r, check e r = true ↔ Admits e r

variable {PatternKey Occurrence Effect Revision Evidence : Type}
  [DecidableEq PatternKey] [DecidableEq Occurrence] [DecidableEq Effect]
  [DecidableEq Revision]

/-- Project one supplied observation only when every event binding matches, a
Boolean is present, evidence is present, and the supplied authority accepts. -/
def project (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence) :
    Option (FastOutcome PatternKey) :=
  if observation.pattern = requested.pattern ∧
      observation.occurrence = requested.occurrence ∧
      observation.effect = requested.effect ∧
      observation.revision = requested.revision then
    match observation.observed, observation.authorityEvidence with
    | some succeeded, some evidence =>
        if gate.check evidence requested then
          some ⟨requested.pattern, true, succeeded⟩
        else none
    | _, _ => none
  else none

theorem project_of_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (succeeded : Bool) (evidence : Evidence)
    (hadmitted : gate.Admits evidence requested) :
    project gate requested
      ⟨requested.pattern, requested.occurrence, requested.effect,
        requested.revision, some succeeded, some evidence⟩ =
      some ⟨requested.pattern, true, succeeded⟩ := by
  simp [project, (gate.check_iff evidence requested).2 hadmitted]

theorem missing_observation_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.observed = none) :
    project gate requested observation = none := by
  simp [project, h]

theorem missing_authority_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.authorityEvidence = none) :
    project gate requested observation = none := by
  simp [project, h]

theorem unqualified_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (succeeded : Bool) (evidence : Evidence)
    (hrejected : ¬ gate.Admits evidence requested) :
    project gate requested
      ⟨requested.pattern, requested.occurrence, requested.effect,
        requested.revision, some succeeded, some evidence⟩ = none := by
  have hcheck : gate.check evidence requested = false := by
    cases h : gate.check evidence requested
    · rfl
    · exact False.elim (hrejected ((gate.check_iff evidence requested).1 h))
  simp [project, hcheck]

theorem occurrence_mismatch_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.occurrence ≠ requested.occurrence) :
    project gate requested observation = none := by
  simp [project, h]

theorem effect_mismatch_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.effect ≠ requested.effect) :
    project gate requested observation = none := by
  simp [project, h]

theorem revision_mismatch_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.revision ≠ requested.revision) :
    project gate requested observation = none := by
  simp [project, h]

theorem pattern_mismatch_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.pattern ≠ requested.pattern) :
    project gate requested observation = none := by
  simp [project, h]

/-! ## Synthetic controls: these instantiate a caller premise, not runtime authority. -/

inductive Pattern where | shared | other deriving DecidableEq, Repr
inductive EffectKind where | emitted | other deriving DecidableEq, Repr

def controlGate : AuthorityCheck Bool Pattern Nat EffectKind Nat where
  Admits evidence _ := evidence = true
  check evidence _ := evidence
  check_iff evidence _ := by cases evidence <;> simp

def requested : Request Pattern Nat EffectKind Nat := ⟨.shared, 19, .emitted, 7⟩

def supplied (occurrence : Nat) (observed : Option Bool) (authority : Option Bool) :
    SuppliedObservation Pattern Nat EffectKind Nat Bool :=
  ⟨.shared, occurrence, .emitted, 7, observed, authority⟩

theorem admitted_success_exact :
    project controlGate requested (supplied 19 (some true) (some true)) =
      some ⟨.shared, true, true⟩ := by decide

theorem admitted_failure_exact :
    project controlGate requested (supplied 19 (some false) (some true)) =
      some ⟨.shared, true, false⟩ := by decide

theorem selected_without_authority_is_absent :
    project controlGate requested (supplied 19 (some true) none) = none := by decide

theorem occurrence_zero_cannot_relabel_as_nineteen :
    project controlGate requested (supplied 0 (some true) (some true)) = none := by decide

/-- An authority-admitted false reaches the existing failure arithmetic. -/
theorem witnessed_false_reaches_failure_update :
    let before : SlowState Pattern := [(.shared, ⟨2, 3⟩)]
    let event : FastOutcome Pattern := ⟨.shared, true, false⟩
    countsFor (advance before event) .shared = ⟨2, 4⟩ := by
  decide

/-- Distinct admitted occurrences retain their shared pattern key and therefore
pool under the existing `witnessedOutcomes`; no occurrence-local theta is added. -/
theorem admitted_occurrences_pool_by_pattern :
    let e0 : FastOutcome Pattern := ⟨.shared, true, true⟩
    let e19 : FastOutcome Pattern := ⟨.shared, true, false⟩
    PatternTheta.witnessedOutcomes .shared [e0, e19] = [true, false] := by
  decide

#print axioms project_of_admitted
#print axioms missing_observation_not_admitted
#print axioms missing_authority_not_admitted
#print axioms unqualified_not_admitted
#print axioms occurrence_mismatch_not_admitted
#print axioms witnessed_false_reaches_failure_update
#print axioms admitted_occurrences_pool_by_pattern

end DarkTower.WarMachine.PatternObservationAdmission
