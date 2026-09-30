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
  q8 : Evidence RunFacts
  q9 : Evidence RunFacts
  q10 : Evidence RunFacts

def assess (check : RunFacts → Bool) : Evidence RunFacts → Outcome
  | .known facts => if check facts then .holds else .violated
  | .nr _ => .unverifiable

def outcomes (p : PartialRunFacts) : List (Requirement × Outcome) :=
  [(.q1, assess Q1 p.q1), (.q2, assess Q2 p.q2),
   (.q3, assess Q3 p.q3), (.q4, assess Q4 p.q4),
   (.q5, assess Q5 p.q5), (.q6, assess Q6 p.q6),
   (.q7, assess Q7 p.q7), (.q8, assess Q8 p.q8),
   (.q9, assess Q9 p.q9), (.q10, assess Q10 p.q10)]

def alert (p : PartialRunFacts) : List (Requirement × Outcome) :=
  (outcomes p).filter (fun (_, result) => result != .holds)

def conformsPartial (p : PartialRunFacts) : Bool := alert p = []

theorem nr_is_unverifiable (check : RunFacts → Bool) (reason : String) :
    assess check (.nr reason) = .unverifiable := rfl

theorem unverifiable_alerts (q : Requirement) (reason : String) :
    (q, assess (fun _ => true) (.nr reason : Evidence RunFacts)) =
      (q, .unverifiable) := rfl

#print axioms nr_is_unverifiable
#print axioms unverifiable_alerts

end DarkTower.WarMachine.RequirementsReader
