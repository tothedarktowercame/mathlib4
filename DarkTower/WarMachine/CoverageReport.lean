/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.WarMachine.GainChain

/-!
# R5 coverage reports

R5 requires an evaluator to declare the boundary of its criterion set and to
emit a typed `uncovered` report for an outcome outside that boundary.  Silence
is not a poor score and is not a coverage report.

The model is parametric in the outcome space.  Its intended carriers include
the seven Snatch flowchart leaves, the fourteen War Machine flight
dispositions, and the mathematics outcomes `closed`, `tier-a`, `tier-b`,
`defective`, plus series-level `void`.  None is built into this module.

This is the family-2/family-5 vocabulary from `GainChain` applied at criterion
grain.  `reportOccurrence` and `criterionSelection` adapt a criterion report to
the existing `inhabitedHandle`, `typedAbsence`, and `declaredDomain`
predicates; they do not introduce a parallel notion of presence or typed
absence.

The model rules out silent non-coverage and the naive repair that merely adds
one criterion.  It does not model probability, entropy, kernels, the quality
of a score, or whether a declared criterion is the right one.
-/

namespace DarkTower.WarMachine.CoverageReport

open DarkTower.WarMachine.GainChain

/-- A criterion set declares its boundary as data.  A Boolean function is
total: every outcome receives an explicit covered/not-covered answer. -/
structure CriterionSet (Outcome : Type) where
  covers : Outcome → Bool

/-- What evaluation emits.  `uncovered` is typed evidence; `absent` is the
silence that R5 refuses. -/
inductive Report where
  | scored (value : Int)
  | uncovered
  | absent
  deriving DecidableEq, Repr

/-- The declaration is total, including at outcomes outside the set. -/
def declaresCoverage {Outcome : Type} [DecidableEq Outcome]
    (criteria : CriterionSet Outcome) : Prop :=
  ∀ outcome, criteria.covers outcome = true ∨ criteria.covers outcome = false

/-- Adapt criterion membership to family 5's declared-domain predicate. -/
def criterionSelection {Outcome : Type} [DecidableEq Outcome]
    (criteria : CriterionSet Outcome)
    (outcome : Outcome) : ProducerSelection where
  tick := ⟨0⟩
  mission := ⟨"criterion-outcome"⟩
  producer := .groundedDial
  inDomain := fun _ => criteria.covers outcome
  preconditionDischarged := true

/-- Adapt the report to family 2's handle and family 5's typed absence. -/
def reportOccurrence : Report → FoldOccurrence
  | .scored value =>
      { tick := ⟨0⟩
        consumed := some
          { tick := ⟨0⟩
            mission := ⟨"criterion-outcome"⟩
            producer := .groundedDial
            expectedLeg := 0
            realizedLeg := .measured value
            durable := true }
        gainMoved := false }
  | .uncovered =>
      { tick := ⟨0⟩
        consumed := some
          { tick := ⟨0⟩
            mission := ⟨"criterion-outcome"⟩
            producer := .groundedDial
            expectedLeg := 0
            realizedLeg := .domainMismatch
            durable := true }
        gainMoved := false }
  | .absent =>
      { tick := ⟨0⟩, consumed := none, gainMoved := false }

/-- An outcome outside declared coverage is reported as `uncovered`, never as
`absent`. -/
def outsideIsTyped {Outcome : Type} [DecidableEq Outcome]
    (criteria : CriterionSet Outcome)
    (evaluate : Outcome → Report) : Prop :=
  ∀ outcome, criteria.covers outcome = false → evaluate outcome = .uncovered

/-- R5's chain property.  Coverage is declared; outside outcomes are typed;
every evaluation has family 2's inhabited handle; and every report agrees with
family 5's declared domain and typed-absence distinction. -/
def coverageReported {Outcome : Type} [DecidableEq Outcome]
    (criteria : CriterionSet Outcome)
    (evaluate : Outcome → Report) : Prop :=
  declaresCoverage criteria ∧
  outsideIsTyped criteria evaluate ∧
  ∀ outcome,
    inhabitedHandle (reportOccurrence (evaluate outcome)) ∧
    typedAbsence (reportOccurrence (evaluate outcome))
      (criterionSelection criteria outcome) ∧
    (criteria.covers outcome = true →
      declaredDomain (criterionSelection criteria outcome))

/-- A verdict keeps the problem result separate from what the instrument
learned while producing it. -/
structure Verdict (ProblemOutcome InstrumentFinding : Type) where
  problemOutcome : ProblemOutcome
  instrumentFinding : InstrumentFinding
  deriving DecidableEq, Repr

/-- A mark changes the problem reading without forcing the instrument reading
to change with it.  Two projections state the separation directly. -/
def markWithoutForce {ProblemOutcome InstrumentFinding : Type}
    [DecidableEq ProblemOutcome]
    (mark : Verdict ProblemOutcome InstrumentFinding →
      Verdict ProblemOutcome InstrumentFinding)
    (before : Verdict ProblemOutcome InstrumentFinding) : Prop :=
  (mark before).problemOutcome ≠ before.problemOutcome ∧
  (mark before).instrumentFinding = before.instrumentFinding

/-! ## Incident-shaped finite witnesses -/

inductive CustomerOutcome where
  | routineSale
  | warmCustomerPays
  | nextUnanticipatedSignal
  deriving DecidableEq, Repr

def customerCriteria : CriterionSet CustomerOutcome where
  covers
    | .routineSale => true
    | .warmCustomerPays => false
    | .nextUnanticipatedSignal => false

def silentCustomerEvaluation : CustomerOutcome → Report
  | .routineSale => .scored 1
  | .warmCustomerPays => .absent
  | .nextUnanticipatedSignal => .absent

/-- The ring's own case: a satisfied but uncovered outcome reported as nothing
cannot satisfy R5. -/
theorem warm_customer_pays_uncovered_and_unrecorded_is_refused :
    ¬ coverageReported customerCriteria silentCustomerEvaluation := by
  intro h
  have outside := h.2.1 CustomerOutcome.warmCustomerPays (by rfl)
  cases outside

/-- The naive repair adds the known missing channel, but the next outcome
outside the enlarged set is silent again.  Klarna is the external analogue:
four real metrics at scale did not make non-coverage report itself. -/
def oneChannelLarger : CriterionSet CustomerOutcome where
  covers
    | .routineSale => true
    | .warmCustomerPays => true
    | .nextUnanticipatedSignal => false

def oneChannelLargerEvaluation : CustomerOutcome → Report
  | .routineSale => .scored 1
  | .warmCustomerPays => .scored 1
  | .nextUnanticipatedSignal => .absent

theorem adding_a_channel_does_not_satisfy_coverage :
    ¬ outsideIsTyped oneChannelLarger oneChannelLargerEvaluation := by
  intro h
  have outside := h CustomerOutcome.nextUnanticipatedSignal (by rfl)
  cases outside

inductive ProblemOutcome where
  | solved
  | void
  deriving DecidableEq, Repr

inductive InstrumentFinding where
  | clean
  | defectiveProblem
  deriving DecidableEq, Repr

def defectiveVerdict : Verdict ProblemOutcome InstrumentFinding :=
  ⟨.solved, .defectiveProblem⟩

def voidProblem (verdict : Verdict ProblemOutcome InstrumentFinding) :
    Verdict ProblemOutcome InstrumentFinding :=
  { verdict with problemOutcome := .void }

/-- APM's defective-problem discipline: problem outcome VOID, instrument
findings RETAINED. -/
theorem void_retains_the_instrument_finding :
    markWithoutForce voidProblem defectiveVerdict := by
  constructor <;> decide

def reportingEvaluation : CustomerOutcome → Report
  | .routineSale => .scored 1
  | .warmCustomerPays => .uncovered
  | .nextUnanticipatedSignal => .uncovered

/-- Non-vacuity: a concrete finite criterion set emits a handle at every
outcome and explicitly reports both outcomes outside its coverage. -/
theorem coverage_reported_nonvacuous :
    coverageReported customerCriteria reportingEvaluation := by
  constructor
  · intro outcome
    cases outcome <;> simp [customerCriteria]
  constructor
  · intro outcome h
    cases outcome <;> simp [customerCriteria, reportingEvaluation] at h ⊢
  · intro outcome
    cases outcome <;>
      simp [reportingEvaluation, reportOccurrence, typedAbsence,
        criterionSelection, customerCriteria, inhabitedHandle, declaredDomain]

#print axioms warm_customer_pays_uncovered_and_unrecorded_is_refused
#print axioms adding_a_channel_does_not_satisfy_coverage
#print axioms void_retains_the_instrument_finding
#print axioms coverage_reported_nonvacuous

end DarkTower.WarMachine.CoverageReport
