import DarkTower.WarMachine.PreferenceRiskSeparation
import DarkTower.WarMachine.F10RuledCarrier

/-! Separated-risk successor witness, Joe's 2026-09-09 sitting.
The twelve-member seed is F10RuledCarrier.seed; the measured constant cohort
predicts groundedChange with mass one. Runtime correspondence is checked by a
separate executable receipt, not assumed here. No observation bridge is claimed. -/
namespace DarkTower.WarMachine.PreferenceRiskWitness
open Holes F10RuledCarrier PreferenceRiskSeparation
noncomputable section

def groundedPrediction : ProbabilityKernel Unit (Outcome SeedObs) where
  support := fun _ => FlightDisposition.all.map organisationOutcome
  mass := fun _ o => match o with
    | ⟨.organization, .groundedChange⟩ => 1
    | _ => 0
  nonnegative := by intro _ o; rcases o with ⟨v, o⟩; cases v <;> cases o <;> norm_num
  normalised := by intro _; norm_num [FlightDisposition.all, organisationOutcome]

theorem grounded_admissible : riskAdmissible groundedPrediction seed := by
  intro p o _ h
  rcases o with ⟨v, o⟩
  cases v <;> cases o <;> norm_num [groundedPrediction, seed] at *

theorem concrete_scalarKL :
    (scalarKL groundedPrediction seed grounded_admissible).value () = Real.log 2 := by
  norm_num [scalarKL, groundedPrediction, seed, FlightDisposition.all, organisationOutcome]

/-- The full named support, including zeros, remains in both distributions. -/
theorem same_twelve_support : groundedPrediction.support () = seed.support () ∧
    (groundedPrediction.support ()).length = 12 := by
  norm_num [groundedPrediction, seed, FlightDisposition.all]

/-- A positive prediction at a named zero is rejected independently of this cohort. -/
theorem abstained_refuses (Q : ProbabilityKernel Unit (Outcome SeedObs))
    (hs : organisationOutcome .abstained ∈ Q.support ())
    (hp : Q.mass () (organisationOutcome .abstained) ≠ 0) :
    ¬ riskAdmissible Q seed :=
  preferred_zero_refuses Q seed () _ hs hp (by rfl)

#print axioms concrete_scalarKL
#print axioms same_twelve_support
#print axioms abstained_refuses
end
end DarkTower.WarMachine.PreferenceRiskWitness
