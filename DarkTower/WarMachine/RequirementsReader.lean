import DarkTower.WarMachine.Requirements

/-! Partial run-record evidence. `nr` is evidence about exportability, never a
value of a `RunFacts` field. A requirement is evaluated only on `known` facts;
otherwise it is `unverifiable`, which appears in the alert. -/

namespace DarkTower.WarMachine.RequirementsReader
open Requirements

inductive Evidence (α : Type*) where
  | known (value : α)
  | nr (reason : String)
  deriving Repr

inductive Outcome where | holds | violated | unverifiable
  deriving DecidableEq, Repr

structure PartialRunFacts where
  q1 : Evidence RunFacts
  q2 : Evidence RunFacts
  q3 : Evidence RunFacts
  q4 : Evidence RunFacts
  q5 : Evidence RunFacts
  q6 : Evidence RunFacts
  q7 : Evidence RunFacts
  q9 : Evidence RunFacts
  /-- Absent from a projection that does not carry it: unverifiable, never holds. -/
  q11 : Evidence RunFacts := .nr "policyG, abstentionG, policyPrediction not projected"

def assess (check : RunFacts → Bool) : Evidence RunFacts → Outcome
  | .known facts => if check facts then .holds else .violated
  | .nr _ => .unverifiable

def outcomes (p : PartialRunFacts) : List (Requirement × Outcome) :=
  [(.q1, assess Q1 p.q1), (.q2, assess Q2 p.q2),
   (.q3, assess Q3 p.q3), (.q4, assess Q4 p.q4),
   (.q5, assess Q5 p.q5), (.q6, assess Q6 p.q6),
   (.q7, assess Q7 p.q7),
   (.q9, assess Q9 p.q9),
   (.q11, assess Q11 p.q11)]

def alert (p : PartialRunFacts) : List (Requirement × Outcome) :=
  (outcomes p).filter (fun (_, result) => result != .holds)

def conformsPartial (p : PartialRunFacts) : Bool := alert p = []

theorem nr_is_unverifiable (check : RunFacts → Bool) (reason : String) :
    assess check (.nr reason) = .unverifiable := rfl

theorem unverifiable_alerts (q : Requirement) (reason : String) :
    (q, assess (fun _ => true) (.nr reason : Evidence RunFacts)) =
      (q, .unverifiable) := rfl

/-- A projection predating the G carrier still elaborates, and Q11 then alerts
as unverifiable rather than passing unread. -/
def withoutGCarrier : PartialRunFacts where
  q1 := .known good
  q2 := .known good
  q3 := .known good
  q4 := .known good
  q5 := .known good
  q6 := .known good
  q7 := .known good
  q9 := .known good

theorem absent_G_carrier_alerts :
    (alert withoutGCarrier).map Prod.snd = [.unverifiable] := by native_decide

/-- A selection-only run has a known order and Q5 holds vacuously; the other
requirements continue to read the same `RunFacts`. -/
def noInterpretationRun : RunFacts :=
  { good with interpretationOrder := .noInterpretation }

def noInterpretationPartial : PartialRunFacts where
  q1 := .known noInterpretationRun
  q2 := .known noInterpretationRun
  q3 := .known noInterpretationRun
  q4 := .known noInterpretationRun
  q5 := .known noInterpretationRun
  q6 := .known noInterpretationRun
  q7 := .known noInterpretationRun
  q9 := .known noInterpretationRun
  q11 := .known noInterpretationRun

theorem no_interpretation_Q5_holds :
    assess Q5 noInterpretationPartial.q5 = .holds := by native_decide

#eval (Q5 noInterpretationRun, Q6 noInterpretationRun, Q11 noInterpretationRun)

#print axioms nr_is_unverifiable
#print axioms unverifiable_alerts

end DarkTower.WarMachine.RequirementsReader
