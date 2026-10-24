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
  Admits : Evidence → Request PatternKey Occurrence Effect Revision → Bool → Prop
  check : Evidence → Request PatternKey Occurrence Effect Revision → Bool → Bool
  check_iff : ∀ e r outcome, check e r outcome = true ↔ Admits e r outcome

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
        if gate.check evidence requested succeeded then
          some ⟨requested.pattern, true, succeeded⟩
        else none
    | _, _ => none
  else none

theorem project_of_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (succeeded : Bool) (evidence : Evidence)
    (hadmitted : gate.Admits evidence requested succeeded) :
    project gate requested
      ⟨requested.pattern, requested.occurrence, requested.effect,
        requested.revision, some succeeded, some evidence⟩ =
      some ⟨requested.pattern, true, succeeded⟩ := by
  simp [project, (gate.check_iff evidence requested succeeded).2 hadmitted]

/-- Every emitted event recovers the matching identity, the actual supplied
Boolean, and authority for that same Boolean. -/
theorem project_eq_some_only_if
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (event : FastOutcome PatternKey)
    (hproject : project gate requested observation = some event) :
    observation.pattern = requested.pattern ∧
      observation.occurrence = requested.occurrence ∧
      observation.effect = requested.effect ∧
      observation.revision = requested.revision ∧
      ∃ evidence,
        observation.observed = some event.succeeded ∧
        observation.authorityEvidence = some evidence ∧
        gate.Admits evidence requested event.succeeded ∧
        event.policy = requested.pattern ∧ event.witnessed = true := by
  unfold project at hproject
  by_cases hbinding : observation.pattern = requested.pattern ∧
      observation.occurrence = requested.occurrence ∧
      observation.effect = requested.effect ∧
      observation.revision = requested.revision
  · have hb := hbinding
    obtain ⟨hp, ho, he, hr⟩ := hbinding
    cases hobserved : observation.observed with
    | none => simp [hb, hobserved] at hproject
    | some succeeded =>
      cases hevidence : observation.authorityEvidence with
      | none => simp [hb, hobserved, hevidence] at hproject
      | some evidence =>
        by_cases hcheck : gate.check evidence requested succeeded = true
        · simp [hb, hobserved, hevidence, hcheck] at hproject
          have hevent : (⟨requested.pattern, true, succeeded⟩ : FastOutcome PatternKey) = event :=
            hproject
          rw [← hevent]
          exact ⟨hp, ho, he, hr, evidence, rfl, rfl,
            (gate.check_iff evidence requested succeeded).1 hcheck, rfl, rfl⟩
        · simp [hb, hobserved, hevidence, hcheck] at hproject
  · simp [hbinding] at hproject

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
    (hrejected : ¬ gate.Admits evidence requested succeeded) :
    project gate requested
      ⟨requested.pattern, requested.occurrence, requested.effect,
        requested.revision, some succeeded, some evidence⟩ = none := by
  have hcheck : gate.check evidence requested succeeded = false := by
    cases h : gate.check evidence requested succeeded
    · rfl
    · exact False.elim (hrejected ((gate.check_iff evidence requested succeeded).1 h))
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

structure ControlEvidence where
  occurrence : Nat
  effect : EffectKind
  revision : Nat
  outcome : Bool
  deriving DecidableEq, Repr

def controlGate : AuthorityCheck ControlEvidence Pattern Nat EffectKind Nat where
  Admits evidence request outcome :=
    evidence.occurrence = request.occurrence ∧
    evidence.effect = request.effect ∧
    evidence.revision = request.revision ∧
    evidence.outcome = outcome
  check evidence request outcome := decide
    (evidence.occurrence = request.occurrence ∧
     evidence.effect = request.effect ∧
     evidence.revision = request.revision ∧
     evidence.outcome = outcome)
  check_iff _ _ _ := by simp

def requested : Request Pattern Nat EffectKind Nat := ⟨.shared, 19, .emitted, 7⟩

def requestedAt (occurrence : Nat) : Request Pattern Nat EffectKind Nat :=
  ⟨.shared, occurrence, .emitted, 7⟩

def evidence (occurrence : Nat) (outcome : Bool) : ControlEvidence :=
  ⟨occurrence, .emitted, 7, outcome⟩

def supplied (occurrence : Nat) (observed : Option Bool)
    (authority : Option ControlEvidence) :
    SuppliedObservation Pattern Nat EffectKind Nat ControlEvidence :=
  ⟨.shared, occurrence, .emitted, 7, observed, authority⟩

theorem admitted_success_exact :
    project controlGate requested (supplied 19 (some true) (some (evidence 19 true))) =
      some ⟨.shared, true, true⟩ := by decide

theorem admitted_failure_exact :
    project controlGate requested (supplied 19 (some false) (some (evidence 19 false))) =
      some ⟨.shared, true, false⟩ := by decide

theorem flipped_payload_is_rejected :
    project controlGate requested (supplied 19 (some false) (some (evidence 19 true))) = none := by
  decide

theorem selected_without_authority_is_absent :
    project controlGate requested (supplied 19 (some true) none) = none := by decide

theorem occurrence_zero_cannot_relabel_as_nineteen :
    project controlGate requested (supplied 0 (some true) (some (evidence 0 true))) = none := by
  decide

/-- An authority-admitted false reaches the existing failure arithmetic. -/
theorem witnessed_false_reaches_failure_update :
    let before : SlowState Pattern := [(.shared, ⟨2, 3⟩)]
    Option.map (fun event => countsFor (advance before event) .shared)
      (project controlGate requested
        (supplied 19 (some false) (some (evidence 19 false)))) = some ⟨2, 4⟩ := by
  decide

/-- Distinct admitted occurrences retain their shared pattern key and therefore
pool under the existing `witnessedOutcomes`; no occurrence-local theta is added. -/
theorem admitted_occurrences_pool_by_pattern :
    PatternTheta.witnessedOutcomes .shared
      ([project controlGate (requestedAt 0)
          (supplied 0 (some true) (some (evidence 0 true))),
        project controlGate (requestedAt 19)
          (supplied 19 (some false) (some (evidence 19 false)))].filterMap id) =
      [true, false] := by
  decide

#print axioms project_of_admitted
#print axioms project_eq_some_only_if
#print axioms missing_observation_not_admitted
#print axioms missing_authority_not_admitted
#print axioms unqualified_not_admitted
#print axioms occurrence_mismatch_not_admitted
#print axioms witnessed_false_reaches_failure_update
#print axioms admitted_occurrences_pool_by_pattern

end DarkTower.WarMachine.PatternObservationAdmission
