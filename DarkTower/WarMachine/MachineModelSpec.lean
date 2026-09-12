import DarkTower.WarMachine.MachineBeliefState

namespace DarkTower.WarMachine.MachineModelSpec
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineBeliefState

structure Identity where
  id : String
  revision : String
  named : id ≠ ""
  versioned : revision ≠ ""

structure MeasurementPointer where
  path : String
  sha256 : String
  present : path ≠ ""
  pinned : sha256.length = 64

inductive Authority where
  | declaredPrior (name : String) (named : name ≠ "")
  | observedEstimate (name : String) (named : name ≠ "") (measurement : MeasurementPointer)

def Authority.isDeclared : Authority → Prop
  | .declaredPrior _ _ => True
  | .observedEstimate _ _ _ => False

inductive MissingProducer where | refuse
inductive ZeroMass where | retain
inductive ImpossibleOutcome where | typedRefusal
inductive EvidenceVocabulary where | owed
inductive ParameterRepresentation where | finiteRegisteredHypotheses

structure Policy (Action : Type) where
  identity : Identity
  entity : Entity
  cascade : Identity
  nodes : List String
  nodesNonempty : nodes ≠ []
  nodesUnique : nodes.Nodup
  actions : List Action
  actionsNonempty : actions ≠ []

/-- V1 is explicitly a single-entity model. Joint construction requires another type. -/
structure Contract (Obs : Vertex → Type) (Action Parameter : Type) where
  version : Nat
  versionOne : version = 1
  identity : Identity
  entity : Entity
  storedBelief : machineBeliefState
  belief : ProbabilityKernel Unit Status
  beliefSupport : belief.support () = Status.all
  beliefPresent : ∃ p, storedBelief entity = some p ∧ ∀ s, belief.mass () s = p s
  actions : List Action
  actionsNonempty : actions ≠ []
  actionsUnique : actions.Nodup
  policies : List (Policy Action)
  policiesNonempty : policies ≠ []
  policyIdsUnique : (policies.map (fun p => p.identity.id)).Nodup
  policyEntities : ∀ p ∈ policies, p.entity = entity
  policyActions : ∀ p ∈ policies, ∀ a ∈ p.actions, a ∈ actions
  model : GenerativeModel Obs Status Action (Policy Action)
  policySupport : model.policyPrior.support () = policies
  aAuthority : Authority
  bAuthority : Authority
  identityBDeclared : (∀ s a, model.transition.mass (s, a) s = 1) → bAuthority.isDeclared
  stateSupport : ∀ s a, model.transition.support (s, a) = Status.all
  initial : ProbabilityKernel Unit Status
  initialSupport : initial.support () = Status.all
  outcomes : List (Outcome Obs)
  outcomesNonempty : outcomes ≠ []
  outcomesUnique : outcomes.Nodup
  outcomeAuthority : MeasurementPointer
  observationSupport : ∀ s, model.observation.support s = outcomes
  evidence : EvidenceVocabulary
  organizationOnly : ∀ o ∈ outcomes, o.1 = .organization
  evidenceUnavailable : ∀ o ∈ outcomes, o.1 ≠ .evidence
  observationEncoding : Identity
  observationEncodingSupport : List (Outcome Obs)
  encodingMatches : observationEncodingSupport = outcomes
  parameterRepresentation : ParameterRepresentation
  parameters : List Parameter
  parametersNonempty : parameters ≠ []
  parametersUnique : parameters.Nodup
  parameterIdentity : Parameter → Identity
  parameterIdsUnique : (parameters.map (fun t => (parameterIdentity t).id)).Nodup
  registration : Parameter → MeasurementPointer
  likelihood : Parameter → ProbabilityKernel Status (Outcome Obs)
  likelihoodAuthority : Parameter → Authority
  likelihoodSupport : ∀ t s, (likelihood t).support s = outcomes
  parameterPrior : ProbabilityKernel Unit Parameter
  parameterSupport : parameterPrior.support () = parameters
  missingProducer : MissingProducer
  zeroMass : ZeroMass
  impossibleOutcome : ImpossibleOutcome

/-- A request requiring evidence vocabulary has no successful v1 constructor. -/
def evidenceConsumable (_ : EvidenceVocabulary) : Bool := false

theorem evidence_request_refused (v : EvidenceVocabulary) : evidenceConsumable v = false := rfl

theorem selected_entity_preserved {O : Vertex → Type} {A T : Type}
    (c : Contract O A T) (p : Policy A) (h : p ∈ c.policies) : p.entity = c.entity :=
  c.policyEntities p h

end DarkTower.WarMachine.MachineModelSpec
