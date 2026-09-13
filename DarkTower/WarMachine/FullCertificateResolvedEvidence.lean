import DarkTower.WarMachine.FullCertificateRecordConnectionBinding

/-! Exact resolved record and edge evidence; authentication remains external. -/
namespace DarkTower.WarMachine.FullCertificateResolvedEvidence
open CertificateStates FullCertificatePredicate FullCertificateRunBinding
  FullCertificateEventBinding FullCertificateRecordConnectionBinding

inductive ApplicableReference
  | checkpoint (checkpointId closeAttemptId : String)
  | trace (traceRunId tickId : String)
  | tickRun (tickId traceRunId : String)
  | closeCohort (closeAttemptId checkpointId : String)
  | dispatchJob (dispatchJobId tickId : String)
  | parkContinuation (continuationId dispatchJobId : String)
  | reviewAdmission (reviewClaimId witnessId : String)
  deriving DecidableEq, Repr

def ApplicableReference.family : ApplicableReference → RecordFamily
  | .checkpoint .. => .fullLoopCheckpoints
  | .trace .. => .wmTraceRecords
  | .tickRun .. => .tickRunRecords
  | .closeCohort .. => .closeCohortRecords
  | .dispatchJob .. => .dispatchJobRecords
  | .parkContinuation .. => .parkContinuationRecords
  | .reviewAdmission .. => .reviewAdmissionRecords

def ApplicableReference.nonempty : ApplicableReference → Prop
  | .checkpoint a b | .trace a b | .tickRun a b | .closeCohort a b
  | .dispatchJob a b | .parkContinuation a b | .reviewAdmission a b => a ≠ "" ∧ b ≠ ""

structure ResolvedRecord where
  family : RecordFamily
  run : RunIdentity
  recordId : String
  evidenceSource : String
  sourcePin : ExactBytePin
  reference : ApplicableReference
  deriving DecidableEq, Repr

structure CorrectedEdgeRequirement where
  connectionId : ConnectionId
  semanticEdgeId : String
  fromNode : NodeId
  toNode : NodeId
  classification : String
  deriving DecidableEq, Repr

structure ResolvedConnection where
  requirement : CorrectedEdgeRequirement
  run : RunIdentity
  evidenceSource : String
  sourcePin : ExactBytePin
  causalRecordId : String
  deriving DecidableEq, Repr

structure ResolvedEvidence where
  records : List ResolvedRecord
  connections : List ResolvedConnection
  deriving DecidableEq, Repr

def resolvedRecordValid (fixed : ExternallyFixedRun) (r : ResolvedRecord) : Prop :=
  r.run = fixed.identity ∧ r.recordId ≠ "" ∧ r.evidenceSource ≠ "" ∧
  r.sourcePin.valid ∧ r.reference.family = r.family ∧ r.reference.nonempty

def resolvedRecordsExact (fixed : ExternallyFixedRun)
    (expected actual : ResolvedEvidence) (att : FullAttestation) : Prop :=
  expected.records.map (·.family) = allRecordFamilies ∧
  actual.records = expected.records ∧
  ∀ r ∈ actual.records, resolvedRecordValid fixed r ∧
    .presentAndConsistent r.family r.evidenceSource ∈ att.recordFamilies

def resolvedConnectionsExact (fixed : ExternallyFixedRun) (req : FullScopeRequirements)
    (expected actual : ResolvedEvidence) (att : FullAttestation) : Prop :=
  expected.connections.map (·.requirement.connectionId) = req.requiredConnections ∧
  actual.connections = expected.connections ∧
  ∀ c ∈ actual.connections,
    c.run = fixed.identity ∧ c.requirement.semanticEdgeId ≠ "" ∧
    c.requirement.fromNode ≠ "" ∧ c.requirement.toNode ≠ "" ∧
    c.requirement.classification ≠ "" ∧ c.evidenceSource ≠ "" ∧ c.sourcePin.valid ∧
    (∃ r ∈ actual.records, r.recordId = c.causalRecordId) ∧
    ⟨c.requirement.connectionId,
      .firedClassified c.requirement.classification c.evidenceSource⟩ ∈ att.connectionStates

def ResolvedQualifyingRun (fixed : ExternallyFixedRun) (events : ExternallyFixedEventPair)
    (subjects : ExternallyFixedRecordConnectionSubjects) (expected actual : ResolvedEvidence)
    (req : FullScopeRequirements) (ev : FullScopeEvidence) (rb : RunBindingEvidence)
    (eb : EventBindingEvidence) (att : FullAttestation) : Prop :=
  RecordConnectionBoundQualifyingRun fixed events subjects req ev rb eb att ∧
  resolvedRecordsExact fixed expected actual att ∧
  resolvedConnectionsExact fixed req expected actual att

theorem resolved_implies_full {fixed events subjects expected actual req ev rb eb att} :
    ResolvedQualifyingRun fixed events subjects expected actual req ev rb eb att →
      FullQualifyingRun req ev att := fun h => recordConnectionBound_implies_full h.1

theorem rejects_wrong_nonempty_reference (fixed) (events) (subjects) (expected actual)
    (req) (ev) (rb) (eb) (att) (href : actual.records ≠ expected.records) :
    ¬ ResolvedQualifyingRun fixed events subjects expected actual req ev rb eb att := by
  intro h; exact href h.2.1.2.1

theorem rejects_same_source_changed_bytes (fixed) (events) (subjects) (expected actual)
    (req) (ev) (rb) (eb) (att) (href : actual.records ≠ expected.records) :
    ¬ ResolvedQualifyingRun fixed events subjects expected actual req ev rb eb att :=
  rejects_wrong_nonempty_reference fixed events subjects expected actual req ev rb eb att href

theorem rejects_cross_run_borrowed_record (fixed) (events) (subjects) (expected actual)
    (req) (ev) (rb) (eb) (att) (r : ResolvedRecord) (hr : r ∈ actual.records)
    (hcross : r.run ≠ fixed.identity) :
    ¬ ResolvedQualifyingRun fixed events subjects expected actual req ev rb eb att := by
  intro h; exact hcross (h.2.1.2.2 r hr).1.1

theorem rejects_unresolved_nonempty_causal_reference (fixed) (events) (subjects)
    (expected actual) (req) (ev) (rb) (eb) (att) (c : ResolvedConnection)
    (hc : c ∈ actual.connections)
    (hunresolved : ¬ ∃ r ∈ actual.records, r.recordId = c.causalRecordId) :
    ¬ ResolvedQualifyingRun fixed events subjects expected actual req ev rb eb att := by
  intro h; exact hunresolved (h.2.2.2.2 c hc).2.2.2.2.2.2.2.1

theorem rejects_wrong_corrected_edge_subject (fixed) (events) (subjects)
    (expected actual) (req) (ev) (rb) (eb) (att)
    (hwrong : actual.connections ≠ expected.connections) :
    ¬ ResolvedQualifyingRun fixed events subjects expected actual req ev rb eb att := by
  intro h; exact hwrong h.2.2.2.1

#print axioms resolved_implies_full
#print axioms rejects_wrong_nonempty_reference
#print axioms rejects_same_source_changed_bytes
#print axioms rejects_cross_run_borrowed_record
#print axioms rejects_unresolved_nonempty_causal_reference
#print axioms rejects_wrong_corrected_edge_subject

end DarkTower.WarMachine.FullCertificateResolvedEvidence
