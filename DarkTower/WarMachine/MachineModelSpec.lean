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

/-- Contract v1.1: the declared numerical admission for float-carried rows.
Production belief rows carry IEEE doubles whose exact sums land within one
ulp of 1 (row-7 witness); coordinates are read at their exact values and
summed exactly, so the sum is order-independent, and admission requires the
sum within `floatRowBound` of 1. Masses are never renormalised. -/
def floatRowBound : ℚ := 1 / 10 ^ 12

structure FloatCarriedRow (O : Type) where
  support : List O
  mass : O → ℚ
  nonnegative : ∀ o, 0 ≤ mass o
  support_nodup : support.Nodup
  mass_eq_zero_of_not_mem : ∀ o, o ∉ support → mass o = 0
  nearNormalised : |((support.map mass).sum) - 1| ≤ floatRowBound

/-- Exact rows satisfy the v1.1 criterion trivially: the two admissions agree
on exactly-normalised rows. -/
theorem exact_row_admissible {O : Type} (support : List O) (mass : O → ℚ)
    (h : (support.map mass).sum = 1) :
    |((support.map mass).sum) - 1| ≤ floatRowBound := by
  rw [h]
  norm_num [floatRowBound]

/-- The existing tolerance rules out empty support; no extra field is needed. -/
theorem FloatCarriedRow.support_ne_nil {O : Type} (r : FloatCarriedRow O) :
    r.support ≠ [] := by
  intro h
  have bound := r.nearNormalised
  rw [h] at bound
  norm_num [floatRowBound] at bound

/-- Preserve the rational coordinates. Exact normalization is an explicit premise,
not a consequence of approximate admission. No renormalization is performed. -/
noncomputable def FloatCarriedRow.toProbabilityKernel {O : Type}
    (r : FloatCarriedRow O) (h : (r.support.map r.mass).sum = 1) :
    ProbabilityKernel Unit O where
  support _ := r.support
  mass _ o := (r.mass o : ℝ)
  nonnegative _ o := by exact_mod_cast r.nonnegative o
  normalised _ := by
    have cast_sum : ∀ xs : List O,
        (xs.map (fun o => (r.mass o : ℝ))).sum = ((xs.map r.mass).sum : ℚ) := by
      intro xs
      induction xs with
      | nil => simp
      | cons o xs ih => simp [ih]
    rw [cast_sum, h]
    norm_num
  support_nodup _ := r.support_nodup
  mass_eq_zero_of_not_mem _ o ho := by simp [r.mass_eq_zero_of_not_mem o ho]

theorem FloatCarriedRow.toProbabilityKernel_coordinate {O : Type}
    (r : FloatCarriedRow O) (h : (r.support.map r.mass).sum = 1) (o : O) :
    (r.toProbabilityKernel h).mass () o = (r.mass o : ℝ) := rfl

theorem FloatCarriedRow.toProbabilityKernel_normalised {O : Type}
    (r : FloatCarriedRow O) (h : (r.support.map r.mass).sum = 1) :
    ((r.toProbabilityKernel h).support () |>.map
      ((r.toProbabilityKernel h).mass ())).sum = 1 :=
  (r.toProbabilityKernel h).normalised ()

end DarkTower.WarMachine.MachineModelSpec
