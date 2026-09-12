import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.MachinePredictiveOutcomeWitness

open DarkTower.WarMachine.Holes

inductive Policy where
  | advanceTwice | advanceThenCascade | advanceTwiceRepeat
  deriving DecidableEq

inductive OrganizationOutcome where
  | abstained | agentUnavailable | artifactOnly | buildFailed | cancelled
  | dispatchFailed | groundedChange | groundedNoChange | guardrailRefusal
  | incomplete | noSelection | substrateUnavailable
  deriving DecidableEq

def Obs : Vertex → Type := fun
  | .organization => OrganizationOutcome
  | _ => Empty

def outcome (o : OrganizationOutcome) : Outcome Obs := ⟨.organization, o⟩

def outcomes : List (Outcome Obs) :=
  [outcome .abstained, outcome .agentUnavailable, outcome .artifactOnly,
   outcome .buildFailed, outcome .cancelled, outcome .dispatchFailed,
   outcome .groundedChange, outcome .groundedNoChange, outcome .guardrailRefusal,
   outcome .incomplete, outcome .noSelection, outcome .substrateUnavailable]

def advanceTwiceMass : OrganizationOutcome → ℝ
  | .abstained => 0.09555013225308848
  | .agentUnavailable => 0.07447381184188043
  | .artifactOnly => 0.1660549156527121
  | .buildFailed => 0
  | .cancelled => 0.10532904980883244
  | .dispatchFailed => 0
  | .groundedChange => 0.5585920904434866
  | .groundedNoChange => 0
  | .guardrailRefusal => 0
  | .incomplete => 0
  | .noSelection => 0
  | .substrateUnavailable => 0

def cascadeMass : OrganizationOutcome → ℝ
  | .abstained => 0
  | .agentUnavailable => 0
  | .artifactOnly => 0.2616050479058006
  | .buildFailed => 0.10532904980883244
  | .cancelled => 0.17980286165071285
  | .dispatchFailed => 0
  | .groundedChange => 0.45326304063465417
  | .groundedNoChange => 0
  | .guardrailRefusal => 0
  | .incomplete => 0
  | .noSelection => 0
  | .substrateUnavailable => 0

def mass (p : Policy) (o : Outcome Obs) : ℝ :=
  match o with
  | ⟨.organization, x⟩ =>
      match p with
      | .advanceTwice | .advanceTwiceRepeat => advanceTwiceMass x
      | .advanceThenCascade => cascadeMass x
  | ⟨.nouns, x⟩ => nomatch x
  | ⟨.verbs, x⟩ => nomatch x
  | ⟨.evidence, x⟩ => nomatch x

noncomputable def retainedKernel : PredictiveOutcomeKernel Policy Obs where
  support _ := outcomes
  mass := mass
  nonnegative := by
    intro p o
    cases p <;> cases o with
    | mk v x => cases v <;> try contradiction <;> cases x <;> norm_num [mass, advanceTwiceMass, cascadeMass]
  normalised := by
    intro p
    cases p <;> norm_num [outcomes, outcome, mass, advanceTwiceMass, cascadeMass]

theorem advanceTwiceCoordinates :
    ∀ o, retainedKernel.mass .advanceTwice (outcome o) = advanceTwiceMass o := by
  intro o; rfl

theorem advanceThenCascadeCoordinates :
    ∀ o, retainedKernel.mass .advanceThenCascade (outcome o) = cascadeMass o := by
  intro o; rfl

theorem repeatedPlanCoordinates :
    ∀ o, retainedKernel.mass .advanceTwiceRepeat (outcome o) =
      retainedKernel.mass .advanceTwice (outcome o) := by
  intro o; rfl

end DarkTower.WarMachine.MachinePredictiveOutcomeWitness
