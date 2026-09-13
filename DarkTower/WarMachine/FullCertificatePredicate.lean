import DarkTower.WarMachine.CertificateStates

/-!
# Full-scope certificate rejection predicate

Additive row-24 precursor.  `CensusComplete` remains the honest typed census.
`FullQualifyingRun` is the separate all-positive predicate.  Its inputs must be
generated from externally checked bytes; this module proves structural
rejection and does not certify a production run.
-/

namespace DarkTower.WarMachine.FullCertificatePredicate
open CertificateStates

structure ExactBytePin where
  path : String
  expectedSha256 : String
  actualSha256 : String
  deriving DecidableEq, Repr

def ExactBytePin.valid (p : ExactBytePin) : Prop :=
  p.path ≠ "" ∧ p.expectedSha256.length = 64 ∧ p.actualSha256 = p.expectedSha256

instance (p : ExactBytePin) : Decidable p.valid := by
  unfold ExactBytePin.valid
  infer_instance

structure EquationRequirement where
  nodeId : NodeId
  equationId : String
  declaration : String
  deriving DecidableEq, Repr

inductive EquationBindingState
  | exact (requirement : EquationRequirement) (claimId runScope : String)
      (registryPin declarationPin witnessPin : ExactBytePin)
  | absent (requirement : EquationRequirement)
  | mismatched (expected actual : EquationRequirement)
  deriving DecidableEq, Repr

def EquationBindingState.requirement : EquationBindingState → EquationRequirement
  | .exact requirement _ _ _ _ _ => requirement
  | .absent requirement => requirement
  | .mismatched expected _ => expected

def EquationBindingState.positive : EquationBindingState → Prop
  | .exact requirement claimId runScope registryPin declarationPin witnessPin =>
      requirement.nodeId ≠ "" ∧ requirement.equationId ≠ "" ∧
      requirement.declaration ≠ "" ∧ claimId ≠ "" ∧ runScope ≠ "" ∧ registryPin.valid ∧
      declarationPin.valid ∧ witnessPin.valid
  | _ => False

instance (s : EquationBindingState) : Decidable s.positive := by
  cases s <;> simp [EquationBindingState.positive] <;> infer_instance

structure LegacyScalarRetirement where
  obligationId : String
  rulingRef : String
  rulingPin : ExactBytePin
  j2AuthorityPin : ExactBytePin
  deriving DecidableEq, Repr

def legacyObligationId := "retired-r8-legacy-free-energy-production-object"
def legacyDescription := "R8 retired legacy scalar producer; live F_pi remains required"
def delegatedRulingSha256 :=
  "30414e60c0b84d18f4322c4f45fba8f22242c633eef35c1d209025b00577faea"
def originalJ2Sha256 :=
  "2fed9f7c5d4a3c375807dab5e0e3f24c82852bbbd9cef949a2fac8d7c22479da"

def LegacyScalarRetirement.valid (r : LegacyScalarRetirement) : Prop :=
  r.obligationId = legacyObligationId ∧ r.rulingRef ≠ "" ∧
  r.rulingPin.expectedSha256 = delegatedRulingSha256 ∧ r.rulingPin.valid ∧
  r.j2AuthorityPin.expectedSha256 = originalJ2Sha256 ∧ r.j2AuthorityPin.valid

instance (r : LegacyScalarRetirement) : Decidable r.valid := by
  unfold LegacyScalarRetirement.valid
  infer_instance

structure FullScopeRequirements where
  requiredNodes : List NodeId
  requiredConnections : List ConnectionId
  requiredEquations : List EquationRequirement
  allowedDivergenceClasses : List String
  authorityPin : ExactBytePin
  deriving DecidableEq, Repr

structure FullScopeEvidence where
  equationBindings : List EquationBindingState
  divergenceAuthorityPin : ExactBytePin
  legacyRetirement : LegacyScalarRetirement
  deriving DecidableEq, Repr

def nodesPositive (req : FullScopeRequirements) (att : FullAttestation) : Prop :=
  req.authorityPin.valid ∧ req.requiredNodes.Nodup ∧
  att.declaredNodes = req.requiredNodes ∧
  ∀ entry ∈ att.nodeStates, positiveAtThisRun entry.state

def connectionPositive : ConnectionState → Prop
  | .firedClassified classification evidenceSource =>
      classification ≠ "" ∧ evidenceSource ≠ ""
  | _ => False

instance (s : ConnectionState) : Decidable (connectionPositive s) := by
  cases s <;> simp [connectionPositive] <;> infer_instance

def connectionsPositive (req : FullScopeRequirements) (att : FullAttestation) : Prop :=
  req.requiredConnections.Nodup ∧
  att.declaredConnections = req.requiredConnections ∧
  ∀ entry ∈ att.connectionStates, connectionPositive entry.state

def recordPositive : RecordFamilyPresence → Prop
  | .presentAndConsistent _ evidenceSource => evidenceSource ≠ ""
  | .typedGap _ _ => False

instance (r : RecordFamilyPresence) : Decidable (recordPositive r) := by
  cases r <;> simp [recordPositive] <;> infer_instance

def recordsPositive (att : FullAttestation) : Prop :=
  ∀ record ∈ att.recordFamilies, recordPositive record

def selectionPositive (req : FullScopeRequirements) (ev : FullScopeEvidence) :
    SelectionEnaction → Prop
  | .match selected enacted => selected = enacted ∧ selected ≠ ""
  | .typedDivergence selected enacted divergenceClass groundsRef evidenceSource =>
      selected ≠ "" ∧ enacted ≠ "" ∧ selected ≠ enacted ∧
      divergenceClass ∈ req.allowedDivergenceClasses ∧
      groundsRef ≠ "" ∧ evidenceSource ≠ "" ∧ ev.divergenceAuthorityPin.valid
  | .refusedShape _ => False

instance (req : FullScopeRequirements) (ev : FullScopeEvidence) (s : SelectionEnaction) :
    Decidable (selectionPositive req ev s) := by
  cases s <;> simp [selectionPositive] <;> infer_instance

def equationsPositive (req : FullScopeRequirements) (ev : FullScopeEvidence) : Prop :=
  req.requiredEquations.Nodup ∧
  ev.equationBindings.map EquationBindingState.requirement = req.requiredEquations ∧
  ∀ binding ∈ ev.equationBindings, binding.positive

def exactNegativeScope (att : FullAttestation) (ev : FullScopeEvidence) : Prop :=
  att.negativeScope = [⟨legacyObligationId, legacyDescription⟩] ∧
  ev.legacyRetirement.valid

/-- Full qualification.  This is deliberately stronger than census completeness.
External producers still owe byte hashing, scope applicability, and construction
of the requirement universe; Lean checks the resulting finite proposition. -/
def FullQualifyingRun (req : FullScopeRequirements) (ev : FullScopeEvidence)
    (att : FullAttestation) : Prop :=
  CensusComplete att ∧ nodesPositive req att ∧ connectionsPositive req att ∧
  recordsPositive att ∧ selectionPositive req ev att.selectionEnaction ∧
  equationsPositive req ev ∧ exactNegativeScope att ev

instance (req : FullScopeRequirements) (ev : FullScopeEvidence) (att : FullAttestation) :
    Decidable (FullQualifyingRun req ev att) := by
  unfold FullQualifyingRun nodesPositive connectionsPositive recordsPositive
    equationsPositive exactNegativeScope
  infer_instance

def badPin : ExactBytePin := ⟨"fixture", String.replicate 64 'a', String.replicate 64 'b'⟩
def absentEq : EquationRequirement := ⟨"R2", "observation", "machineObservation"⟩
def fixtureReq : FullScopeRequirements :=
  { requiredNodes := ["R2"]
    requiredConnections := ["R16->R2"]
    requiredEquations := [absentEq]
    allowedDivergenceClasses := ["reviewed-substitution"]
    authorityPin := badPin }
def fixtureRetirement : LegacyScalarRetirement :=
  ⟨legacyObligationId, "ruling", badPin, badPin⟩
def fixtureEvidence : FullScopeEvidence :=
  ⟨[.absent absentEq], badPin, fixtureRetirement⟩

def leadCounterexample : FullAttestation :=
  { declaredNodes := ["R2"]
    nodeStates := [⟨"R2", .supportedAtRun "unjoined-claim" "unverified-scope"⟩]
    declaredConnections := ["R16->R2"]
    connectionStates := [⟨"R16->R2", .mandatoryUnfired "this-run"⟩]
    selectionEnaction := .refusedShape "no selected/enacted pair"
    recordFamilies := allRecordFamilies.map (fun f => .typedGap f "missing")
    negativeScope := [⟨"unruled-gap", "no authorizing ruling"⟩] }

theorem rejects_existing_lead_counterexample :
    ¬ FullQualifyingRun fixtureReq fixtureEvidence leadCounterexample := by
  intro hfull
  rcases hfull with ⟨_, _, _, hrecords, _, _, _⟩
  have hp := hrecords (.typedGap .fullLoopCheckpoints "missing") (by
    simp [leadCounterexample, allRecordFamilies])
  simp [recordPositive] at hp

theorem rejects_missing_record_family (att : FullAttestation) (req : FullScopeRequirements)
    (ev : FullScopeEvidence) (family : RecordFamily) (gap : String)
    (h : .typedGap family gap ∈ att.recordFamilies) : ¬ FullQualifyingRun req ev att := by
  intro hfull
  rcases hfull with ⟨_, _, _, hrecords, _, _, _⟩
  have hp := hrecords _ h
  simp [recordPositive] at hp

theorem rejects_unclosed_node (att : FullAttestation) (req : FullScopeRequirements)
    (ev : FullScopeEvidence) (node claim scope : String)
    (h : ⟨node, .unvalidated claim scope⟩ ∈ att.nodeStates) :
    ¬ FullQualifyingRun req ev att := by
  intro hfull
  rcases hfull with ⟨_, hnodes, _, _, _, _, _⟩
  have hp := hnodes.2.2.2 _ h
  simp [positiveAtThisRun] at hp

theorem rejects_unfired_edge (att : FullAttestation) (req : FullScopeRequirements)
    (ev : FullScopeEvidence) (edge scope : String)
    (h : ⟨edge, .mandatoryUnfired scope⟩ ∈ att.connectionStates) :
    ¬ FullQualifyingRun req ev att := by
  intro hfull
  rcases hfull with ⟨_, _, hconnections, _, _, _, _⟩
  have hp := hconnections.2.2 _ h
  simp [connectionPositive] at hp

theorem rejects_selection_mismatch (att : FullAttestation) (req : FullScopeRequirements)
    (ev : FullScopeEvidence) (selected enacted : String)
    (hne : selected ≠ enacted) (hsel : att.selectionEnaction = .match selected enacted) :
    ¬ FullQualifyingRun req ev att := by
  intro hfull
  rcases hfull with ⟨_, _, _, _, hp, _, _⟩
  rw [hsel] at hp
  exact hne hp.1

theorem rejects_absent_equation (att : FullAttestation) (req : FullScopeRequirements)
    (ev : FullScopeEvidence) (equation : EquationRequirement)
    (h : .absent equation ∈ ev.equationBindings) : ¬ FullQualifyingRun req ev att := by
  intro hfull
  rcases hfull with ⟨_, _, _, _, _, hequations, _⟩
  have hp := hequations.2.2 _ h
  simp [EquationBindingState.positive] at hp

theorem rejects_mismatched_declaration (att : FullAttestation)
    (req : FullScopeRequirements) (ev : FullScopeEvidence)
    (expected actual : EquationRequirement)
    (h : .mismatched expected actual ∈ ev.equationBindings) :
    ¬ FullQualifyingRun req ev att := by
  intro hfull
  rcases hfull with ⟨_, _, _, _, _, hequations, _⟩
  have hp := hequations.2.2 _ h
  simp [EquationBindingState.positive] at hp

theorem rejects_unauthorized_negative_scope (att : FullAttestation)
    (req : FullScopeRequirements) (ev : FullScopeEvidence)
    (h : att.negativeScope ≠ [⟨legacyObligationId, legacyDescription⟩]) :
    ¬ FullQualifyingRun req ev att := by
  intro hfull
  rcases hfull with ⟨_, _, _, _, _, _, hnegative⟩
  exact h hnegative.1

#print axioms rejects_existing_lead_counterexample
#print axioms rejects_missing_record_family
#print axioms rejects_unclosed_node
#print axioms rejects_unfired_edge
#print axioms rejects_selection_mismatch
#print axioms rejects_absent_equation
#print axioms rejects_mismatched_declaration
#print axioms rejects_unauthorized_negative_scope

end DarkTower.WarMachine.FullCertificatePredicate
