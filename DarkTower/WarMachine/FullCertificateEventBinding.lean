import DarkTower.WarMachine.FullCertificateRunBinding

/-!
# Exact selection and enaction event subjects

This additive row-24 layer binds both ordinary matches and authorized
divergences to externally fixed, occurrence-preserving event subjects.  It
checks supplied identities and pins; it does not authenticate their bytes.
-/

namespace DarkTower.WarMachine.FullCertificateEventBinding
open CertificateStates FullCertificatePredicate FullCertificateRunBinding

structure EventSubject where
  run : RunIdentity
  occurrenceId : String
  actionId : ActionId
  sourceRef : String
  sourcePin : ExactBytePin
  deriving DecidableEq, Repr

structure ExternallyFixedEventPair where
  selected : EventSubject
  enacted : EventSubject
  authorityRef : String
  authorityPin : ExactBytePin
  deriving DecidableEq, Repr

structure ActualEventPair where
  selected : EventSubject
  enacted : EventSubject
  deriving DecidableEq, Repr

structure ExactDivergenceSubject where
  selected : EventSubject
  enacted : EventSubject
  divergenceClass : String
  groundsRef : String
  evidenceSource : String
  authorityRef : String
  authorityPin : ExactBytePin
  deriving DecidableEq, Repr

structure EventBindingEvidence where
  actual : ActualEventPair
  divergenceSubject : Option ExactDivergenceSubject
  deriving DecidableEq, Repr

def EventSubject.validAt (fixed : ExternallyFixedRun) (s : EventSubject) : Prop :=
  s.run = fixed.identity ∧ s.occurrenceId ≠ "" ∧ s.actionId ≠ "" ∧
  s.sourceRef ≠ "" ∧ s.sourcePin.valid

def fixedPairValid (fixed : ExternallyFixedRun) (expected : ExternallyFixedEventPair) : Prop :=
  expected.selected.validAt fixed ∧ expected.enacted.validAt fixed ∧
  expected.authorityRef ≠ "" ∧ expected.authorityPin.valid

def eventSelectionExact (fixed : ExternallyFixedRun) (req : FullScopeRequirements)
    (expected : ExternallyFixedEventPair) (eb : EventBindingEvidence) :
    SelectionEnaction → Prop
  | .match selected enacted =>
      eb.actual.selected = expected.selected ∧ eb.actual.enacted = expected.enacted ∧
      selected = expected.selected.actionId ∧ enacted = expected.enacted.actionId ∧
      selected = enacted ∧ eb.divergenceSubject = none
  | .typedDivergence selected enacted cls grounds source =>
      eb.actual.selected = expected.selected ∧ eb.actual.enacted = expected.enacted ∧
      ∃ d, eb.divergenceSubject = some d ∧ d.selected = expected.selected ∧
        d.enacted = expected.enacted ∧ d.divergenceClass = cls ∧
        cls ∈ req.allowedDivergenceClasses ∧ d.groundsRef = grounds ∧
        d.evidenceSource = source ∧ d.authorityRef ≠ "" ∧ d.authorityPin.valid ∧
        selected = expected.selected.actionId ∧ enacted = expected.enacted.actionId
  | .refusedShape _ => False

def EventBoundQualifyingRun (fixed : ExternallyFixedRun)
    (expected : ExternallyFixedEventPair) (req : FullScopeRequirements)
    (ev : FullScopeEvidence) (rb : RunBindingEvidence) (eb : EventBindingEvidence)
    (att : FullAttestation) : Prop :=
  RunBoundQualifyingRun fixed req ev rb att ∧ fixedPairValid fixed expected ∧
  eventSelectionExact fixed req expected eb att.selectionEnaction

theorem eventBound_implies_runBound {fixed expected req ev rb eb att} :
    EventBoundQualifyingRun fixed expected req ev rb eb att →
      RunBoundQualifyingRun fixed req ev rb att := fun h => h.1

theorem eventBound_implies_full {fixed expected req ev rb eb att} :
    EventBoundQualifyingRun fixed expected req ev rb eb att →
      FullQualifyingRun req ev att := fun h => runBound_implies_full h.1

theorem rejects_cross_run_ordinary_match (fixed) (expected) (req) (ev) (rb) (eb) (att)
    (selected enacted : String)
    (hsel : att.selectionEnaction = .match selected enacted)
    (hrun : expected.selected.run ≠ fixed.identity) :
    ¬ EventBoundQualifyingRun fixed expected req ev rb eb att := by
  intro h
  exact hrun h.2.1.1.1

theorem rejects_same_action_wrong_occurrence (fixed) (expected) (req) (ev) (rb) (eb) (att)
    (selected enacted : String)
    (hsel : att.selectionEnaction = .match selected enacted)
    (haction : eb.actual.selected.actionId = expected.selected.actionId)
    (hocc : eb.actual.selected.occurrenceId ≠ expected.selected.occurrenceId) :
    ¬ EventBoundQualifyingRun fixed expected req ev rb eb att := by
  intro h
  have hs := h.2.2
  rw [hsel] at hs
  exact hocc (congrArg EventSubject.occurrenceId hs.1)

theorem rejects_borrowed_divergence_occurrence_pair (fixed) (expected) (req) (ev) (rb)
    (eb) (att) (selected enacted cls grounds source : String)
    (d : ExactDivergenceSubject)
    (hsel : att.selectionEnaction = .typedDivergence selected enacted cls grounds source)
    (hd : eb.divergenceSubject = some d)
    (hborrowed : d.selected ≠ expected.selected ∨ d.enacted ≠ expected.enacted) :
    ¬ EventBoundQualifyingRun fixed expected req ev rb eb att := by
  intro h
  have hs := h.2.2
  rw [hsel] at hs
  rcases hs.2.2 with ⟨d', hd', hselected, henacted, _⟩
  rw [hd] at hd'
  injection hd' with heq
  subst d'
  exact hborrowed.elim (fun hn => hn hselected) (fun hn => hn henacted)

theorem rejects_mismatched_exact_subject_pin (fixed) (expected) (req) (ev) (rb) (eb)
    (att) (selected enacted : String)
    (hsel : att.selectionEnaction = .match selected enacted)
    (hpin : eb.actual.selected.sourcePin ≠ expected.selected.sourcePin) :
    ¬ EventBoundQualifyingRun fixed expected req ev rb eb att := by
  intro h
  have hs := h.2.2
  rw [hsel] at hs
  exact hpin (congrArg EventSubject.sourcePin hs.1)

#print axioms eventBound_implies_runBound
#print axioms eventBound_implies_full
#print axioms rejects_cross_run_ordinary_match
#print axioms rejects_same_action_wrong_occurrence
#print axioms rejects_borrowed_divergence_occurrence_pair
#print axioms rejects_mismatched_exact_subject_pin

end DarkTower.WarMachine.FullCertificateEventBinding
