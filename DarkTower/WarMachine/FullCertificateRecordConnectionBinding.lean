import DarkTower.WarMachine.FullCertificateEventBinding

/-!
# Exact record-family and connection subjects

Additive row-24 rejection layer. Expected subjects are external inputs; this
module compares them exactly and does not authenticate bytes or construct the
required universes.
-/

namespace DarkTower.WarMachine.FullCertificateRecordConnectionBinding
open CertificateStates FullCertificatePredicate FullCertificateRunBinding
  FullCertificateEventBinding

structure CausalReferences where
  tickId : String
  traceRunId : String
  closeAttemptId : String
  dispatchJobId : String
  reviewClaimId : String
  deriving DecidableEq, Repr

structure RecordFamilySubject where
  family : RecordFamily
  run : RunIdentity
  recordId : String
  evidenceSource : String
  sourcePin : ExactBytePin
  references : CausalReferences
  deriving DecidableEq, Repr

structure ConnectionSubject where
  connectionId : ConnectionId
  fromNode : NodeId
  toNode : NodeId
  classification : String
  run : RunIdentity
  evidenceSource : String
  sourcePin : ExactBytePin
  causalRecordId : String
  deriving DecidableEq, Repr

structure ExternallyFixedRecordConnectionSubjects where
  records : List RecordFamilySubject
  connections : List ConnectionSubject
  authorityRef : String
  authorityPin : ExactBytePin
  deriving DecidableEq, Repr

def recordSubjectValid (fixed : ExternallyFixedRun) (s : RecordFamilySubject) : Prop :=
  s.run = fixed.identity ∧ s.recordId ≠ "" ∧ s.evidenceSource ≠ "" ∧
  s.sourcePin.valid

def recordsExact (fixed : ExternallyFixedRun)
    (expected : ExternallyFixedRecordConnectionSubjects)
    (att : FullAttestation) : Prop :=
  expected.records.map (·.family) = allRecordFamilies ∧
  att.recordFamilies.map RecordFamilyPresence.family = allRecordFamilies ∧
  ∀ s ∈ expected.records,
    recordSubjectValid fixed s ∧
    .presentAndConsistent s.family s.evidenceSource ∈ att.recordFamilies

def connectionSubjectValid (fixed : ExternallyFixedRun) (s : ConnectionSubject) : Prop :=
  s.run = fixed.identity ∧ s.fromNode ≠ "" ∧ s.toNode ≠ "" ∧
  s.connectionId = s.fromNode ++ "->" ++ s.toNode ∧
  s.classification ≠ "" ∧ s.evidenceSource ≠ "" ∧ s.sourcePin.valid ∧
  s.causalRecordId ≠ ""

def connectionsExact (fixed : ExternallyFixedRun) (req : FullScopeRequirements)
    (expected : ExternallyFixedRecordConnectionSubjects)
    (att : FullAttestation) : Prop :=
  expected.connections.map (·.connectionId) = req.requiredConnections ∧
  att.connectionStates.map (·.connectionId) = req.requiredConnections ∧
  ∀ s ∈ expected.connections,
    connectionSubjectValid fixed s ∧
    ⟨s.connectionId, .firedClassified s.classification s.evidenceSource⟩ ∈
      att.connectionStates

def externalSubjectsValid (expected : ExternallyFixedRecordConnectionSubjects) : Prop :=
  expected.authorityRef ≠ "" ∧ expected.authorityPin.valid

def RecordConnectionBoundQualifyingRun (fixed : ExternallyFixedRun)
    (events : ExternallyFixedEventPair) (expected : ExternallyFixedRecordConnectionSubjects)
    (req : FullScopeRequirements) (ev : FullScopeEvidence) (rb : RunBindingEvidence)
    (eb : EventBindingEvidence) (att : FullAttestation) : Prop :=
  EventBoundQualifyingRun fixed events req ev rb eb att ∧
  externalSubjectsValid expected ∧ recordsExact fixed expected att ∧
  connectionsExact fixed req expected att

theorem recordConnectionBound_implies_eventBound {fixed events expected req ev rb eb att} :
    RecordConnectionBoundQualifyingRun fixed events expected req ev rb eb att →
      EventBoundQualifyingRun fixed events req ev rb eb att := fun h => h.1

theorem recordConnectionBound_implies_full {fixed events expected req ev rb eb att} :
    RecordConnectionBoundQualifyingRun fixed events expected req ev rb eb att →
      FullQualifyingRun req ev att := fun h => eventBound_implies_full h.1

theorem rejects_cross_run_family_reuse (fixed) (events) (expected) (req) (ev) (rb)
    (eb) (att) (s : RecordFamilySubject) (hs : s ∈ expected.records)
    (hrun : s.run ≠ fixed.identity) :
    ¬ RecordConnectionBoundQualifyingRun fixed events expected req ev rb eb att := by
  intro h
  exact hrun (h.2.2.1.2 s hs).1.1

theorem rejects_missing_family (fixed) (events) (expected) (req) (ev) (rb) (eb) (att)
    (family : RecordFamily) (hfamily : family ∉ expected.records.map (·.family)) :
    ¬ RecordConnectionBoundQualifyingRun fixed events expected req ev rb eb att := by
  intro h
  apply hfamily
  rw [h.2.2.1.1]
  cases family <;> simp [allRecordFamilies]

theorem rejects_mismatched_family_evidence_source (fixed) (events) (expected) (req)
    (ev) (rb) (eb) (att) (s : RecordFamilySubject) (hs : s ∈ expected.records)
    (hmissing : .presentAndConsistent s.family s.evidenceSource ∉ att.recordFamilies) :
    ¬ RecordConnectionBoundQualifyingRun fixed events expected req ev rb eb att := by
  intro h
  exact hmissing (h.2.2.1.2 s hs).2

theorem rejects_cross_run_edge_reuse (fixed) (events) (expected) (req) (ev) (rb)
    (eb) (att) (s : ConnectionSubject) (hs : s ∈ expected.connections)
    (hrun : s.run ≠ fixed.identity) :
    ¬ RecordConnectionBoundQualifyingRun fixed events expected req ev rb eb att := by
  intro h
  exact hrun (h.2.2.2.2 s hs).1.1

theorem rejects_wrong_connection_endpoint (fixed) (events) (expected) (req) (ev) (rb)
    (eb) (att) (s : ConnectionSubject) (hs : s ∈ expected.connections)
    (hendpoint : s.connectionId ≠ s.fromNode ++ "->" ++ s.toNode) :
    ¬ RecordConnectionBoundQualifyingRun fixed events expected req ev rb eb att := by
  intro h
  exact hendpoint (h.2.2.2.2 s hs).1.2.2.1

theorem rejects_wrong_connection_classification (fixed) (events) (expected) (req) (ev)
    (rb) (eb) (att) (s : ConnectionSubject) (hs : s ∈ expected.connections)
    (hmissing : ⟨s.connectionId, .firedClassified s.classification s.evidenceSource⟩ ∉
      att.connectionStates) :
    ¬ RecordConnectionBoundQualifyingRun fixed events expected req ev rb eb att := by
  intro h
  exact hmissing (h.2.2.2.2 s hs).2

theorem rejects_stale_causal_reference (fixed) (events) (expected) (req) (ev) (rb)
    (eb) (att) (s : ConnectionSubject) (hs : s ∈ expected.connections)
    (hstale : s.causalRecordId = "") :
    ¬ RecordConnectionBoundQualifyingRun fixed events expected req ev rb eb att := by
  intro h
  exact (h.2.2.2.2 s hs).1.2.2.2.2.2.2.2 hstale

#print axioms recordConnectionBound_implies_eventBound
#print axioms recordConnectionBound_implies_full
#print axioms rejects_cross_run_family_reuse
#print axioms rejects_missing_family
#print axioms rejects_mismatched_family_evidence_source
#print axioms rejects_cross_run_edge_reuse
#print axioms rejects_wrong_connection_endpoint
#print axioms rejects_wrong_connection_classification
#print axioms rejects_stale_causal_reference

end DarkTower.WarMachine.FullCertificateRecordConnectionBinding
