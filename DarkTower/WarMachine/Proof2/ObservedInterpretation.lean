import DarkTower.WarMachine.CascadeTransition

/-!
# Interpretations received as observations (W9-2, D3)

Joe's D3 (2026-09-27; futon2 9719202a0) places interpretations at R2: the
machine receives published readings; it does not supply a default pattern.
Who parses them (象 as annotator or the WM) is not decided here.

The reading's attestation level is its evidence (M-象-2000's ladder).
We record that attestation as opaque text, not a formalised ladder or a proof
of its truth. Publication/validation is the caller's responsibility.

The absence constructors mirror flight_runner.clj's ask-one / settle /
ask-threw outcomes, including pending and ask-threw omitted by ask-fn's
docstring. A not-dispatched Agency answer settles as not-answered; a poll
exception becomes ask-threw. Diagnostic payloads below are opaque text.
-/

namespace DarkTower.WarMachine.Proof2

open DarkTower.WarMachine.CascadeTransition

/-- Exactly the ask step's eight non-publication outcomes, each naming its want. -/
inductive InterpretationAbsence (W : Type*) where
  | noCriterion (want : W)
  | requestRefused (want : W) (refusal : String)
  | pending (want : W) (state : String)
  | notAnswered (want : W) (state : Option String)
  | unparseableResponse (want : W) (detail : String)
  | declined (want : W) (reason : String)
  | rejected (want : W) (reasons : List String)
  | askThrew (want : W) (failure : String)

/-- Published interpretations for every candidate unit index, with the reading's
recorded attestation. This type makes coverage an explicit caller obligation. -/
structure ObservedInterpretation (ι V : Type*) [Fintype V] [DecidableEq V] where
  pat : ι → InterpretedPattern V
  readingAttestation : String

namespace ObservedInterpretation

variable {ι V W : Type*} [Fintype V] [DecidableEq V]

/-- Receive a published supply or its non-publication outcome unchanged.
In particular, an absent want is never replaced by an interpreted pattern. -/
def observedInterpretation
    (supply : Except (InterpretationAbsence W) (ObservedInterpretation ι V)) :
    Except (InterpretationAbsence W) (ObservedInterpretation ι V) := supply

theorem observedInterpretation_published (ob : ObservedInterpretation ι V) :
    observedInterpretation (W := W) (.ok ob) = .ok ob := rfl

theorem observedInterpretation_absent (reason : InterpretationAbsence W) :
    observedInterpretation (ι := ι) (V := V) (.error reason) = .error reason := rfl

/-- The bad case: no absent supply can be read as any published pattern map. -/
theorem absent_is_not_published (reason : InterpretationAbsence W)
    (ob : ObservedInterpretation ι V) :
    observedInterpretation (.error reason) ≠ .ok ob := by
  simp [observedInterpretation]

#print axioms InterpretationAbsence
#print axioms ObservedInterpretation
#print axioms observedInterpretation
#print axioms observedInterpretation_published
#print axioms observedInterpretation_absent
#print axioms absent_is_not_published

end ObservedInterpretation

end DarkTower.WarMachine.Proof2
