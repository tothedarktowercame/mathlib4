import DarkTower.WarMachine.FullCertificateResolvedEvidence

namespace DarkTower.WarMachine.FullCertificateCrossLayerBinding
open CertificateStates FullCertificatePredicate FullCertificateRunBinding
  FullCertificateEventBinding FullCertificateRecordConnectionBinding
  FullCertificateResolvedEvidence

structure RecordKey where
  family : RecordFamily
  run : RunIdentity
  recordId : String
  deriving DecidableEq, Repr

def ResolvedRecord.key (r : ResolvedRecord) : RecordKey := ⟨r.family, r.run, r.recordId⟩

def referenceProjects (old : CausalReferences) : ApplicableReference → Prop
  | .checkpoint checkpoint close => old.closeAttemptId = close ∧ old.tickId = checkpoint
  | .trace trace tick => old.traceRunId = trace ∧ old.tickId = tick
  | .tickRun tick trace => old.tickId = tick ∧ old.traceRunId = trace
  | .closeCohort close checkpoint => old.closeAttemptId = close ∧ old.tickId = checkpoint
  | .dispatchJob job tick => old.dispatchJobId = job ∧ old.tickId = tick
  | .parkContinuation _ job => old.dispatchJobId = job
  | .reviewAdmission claim _ => old.reviewClaimId = claim

def recordProjects (old : RecordFamilySubject) (r : ResolvedRecord) : Prop :=
  old.family = r.family ∧ old.run = r.run ∧ old.recordId = r.recordId ∧
  old.evidenceSource = r.evidenceSource ∧ old.sourcePin = r.sourcePin ∧
  referenceProjects old.references r.reference

def connectionProjects (old : ConnectionSubject) (c : ResolvedConnection) : Prop :=
  old.connectionId = c.requirement.connectionId ∧ old.fromNode = c.requirement.fromNode ∧
  old.toNode = c.requirement.toNode ∧ old.classification = c.requirement.classification ∧
  old.run = c.run ∧ old.evidenceSource = c.evidenceSource ∧
  old.sourcePin = c.sourcePin ∧ old.causalRecordId = c.causalRecordId

structure CrossFamilyAuthority where
  traceTickId : String
  traceRunId : String
  checkpointId : String
  closeAttemptId : String
  dispatchJobId : String
  continuationId : String
  reviewClaimId : String
  witnessId : String
  deriving DecidableEq, Repr

def crossFamilyExact (a : CrossFamilyAuthority) (rs : List ResolvedRecord) : Prop :=
  (∃ r ∈ rs, r.reference = .trace a.traceRunId a.traceTickId) ∧
  (∃ r ∈ rs, r.reference = .tickRun a.traceTickId a.traceRunId) ∧
  (∃ r ∈ rs, r.reference = .checkpoint a.checkpointId a.closeAttemptId) ∧
  (∃ r ∈ rs, r.reference = .closeCohort a.closeAttemptId a.checkpointId) ∧
  (∃ r ∈ rs, r.reference = .dispatchJob a.dispatchJobId a.traceTickId) ∧
  (∃ r ∈ rs, r.reference = .parkContinuation a.continuationId a.dispatchJobId) ∧
  (∃ r ∈ rs, r.reference = .reviewAdmission a.reviewClaimId a.witnessId)

structure EdgeCausalTarget where
  semanticEdgeId : String
  target : RecordKey
  deriving DecidableEq, Repr

structure SummaryExpansion where
  summary : RecordKey
  underlyingMembers : List ExactBytePin
  membershipAuthorityRef : String
  deriving DecidableEq, Repr

structure CrossLayerEvidence where
  causal : CrossFamilyAuthority
  edgeTargets : List EdgeCausalTarget
  expansions : List SummaryExpansion
  deriving DecidableEq, Repr

def projectionsExact (subjects : ExternallyFixedRecordConnectionSubjects)
    (actual : ResolvedEvidence) : Prop :=
  subjects.records.length = actual.records.length ∧
  (∀ old ∈ subjects.records, ∃ r ∈ actual.records, recordProjects old r) ∧
  subjects.connections.length = actual.connections.length ∧
  ∀ old ∈ subjects.connections, ∃ c ∈ actual.connections, connectionProjects old c

def targetsExact (actual : ResolvedEvidence) (x : CrossLayerEvidence) : Prop :=
  x.edgeTargets.map (·.semanticEdgeId) = actual.connections.map (·.requirement.semanticEdgeId) ∧
  ∀ t ∈ x.edgeTargets, ∃ c ∈ actual.connections,
    c.requirement.semanticEdgeId = t.semanticEdgeId ∧ c.causalRecordId = t.target.recordId ∧
    ∃ r ∈ actual.records, r.key = t.target

def CrossLayerQualifyingRun (fixed : ExternallyFixedRun) (events : ExternallyFixedEventPair)
    (subjects : ExternallyFixedRecordConnectionSubjects) (expected actual : ResolvedEvidence)
    (x : CrossLayerEvidence) (req : FullScopeRequirements) (ev : FullScopeEvidence)
    (rb : RunBindingEvidence) (eb : EventBindingEvidence) (att : FullAttestation) : Prop :=
  ResolvedQualifyingRun fixed events subjects expected actual req ev rb eb att ∧
  projectionsExact subjects actual ∧ (actual.records.map ResolvedRecord.key).Nodup ∧
  crossFamilyExact x.causal actual.records ∧ targetsExact actual x ∧
  ((∃ j ∈ rb.nodeJoins, j.claimId = x.causal.reviewClaimId) ∨
   (∃ j ∈ rb.equationJoins, j.claimId = x.causal.reviewClaimId)) ∧
  x.expansions.map (·.summary) = actual.records.map ResolvedRecord.key ∧
  ∀ e ∈ x.expansions, e.underlyingMembers ≠ [] ∧
    (∀ p ∈ e.underlyingMembers, p.valid) ∧ e.membershipAuthorityRef ≠ ""

theorem crossLayer_implies_full {fixed events subjects expected actual x req ev rb eb att} :
    CrossLayerQualifyingRun fixed events subjects expected actual x req ev rb eb att →
      FullQualifyingRun req ev att := fun h => resolved_implies_full h.1

theorem rejects_cross_layer_record_mismatch (fixed) (events) (subjects) (expected actual)
    (x) (req) (ev) (rb) (eb) (att) (old : RecordFamilySubject)
    (ho : old ∈ subjects.records)
    (hnone : ¬ ∃ r ∈ actual.records, recordProjects old r) :
    ¬ CrossLayerQualifyingRun fixed events subjects expected actual x req ev rb eb att := by
  intro h; exact hnone (h.2.1.2.1 old ho)

theorem rejects_wrong_nonempty_cross_family_reference (fixed) (events) (subjects)
    (expected actual) (x) (req) (ev) (rb) (eb) (att)
    (hbad : ¬ crossFamilyExact x.causal actual.records) :
    ¬ CrossLayerQualifyingRun fixed events subjects expected actual x req ev rb eb att := by
  intro h; exact hbad h.2.2.2.1

theorem rejects_ambiguous_composite_record_identity (fixed) (events) (subjects)
    (expected actual) (x) (req) (ev) (rb) (eb) (att)
    (hdup : ¬ (actual.records.map ResolvedRecord.key).Nodup) :
    ¬ CrossLayerQualifyingRun fixed events subjects expected actual x req ev rb eb att := by
  intro h; exact hdup h.2.2.1

theorem rejects_wrong_family_causal_target (fixed) (events) (subjects) (expected actual)
    (x) (req) (ev) (rb) (eb) (att) (hbad : ¬ targetsExact actual x) :
    ¬ CrossLayerQualifyingRun fixed events subjects expected actual x req ev rb eb att := by
  intro h; exact hbad h.2.2.2.2.1

theorem rejects_wrong_review_claim (fixed) (events) (subjects) (expected actual)
    (x) (req) (ev) (rb) (eb) (att)
    (hbad : ¬ ((∃ j ∈ rb.nodeJoins, j.claimId = x.causal.reviewClaimId) ∨
      (∃ j ∈ rb.equationJoins, j.claimId = x.causal.reviewClaimId))) :
    ¬ CrossLayerQualifyingRun fixed events subjects expected actual x req ev rb eb att := by
  intro h; exact hbad h.2.2.2.2.2.1

#print axioms crossLayer_implies_full
#print axioms rejects_cross_layer_record_mismatch
#print axioms rejects_wrong_nonempty_cross_family_reference
#print axioms rejects_ambiguous_composite_record_identity
#print axioms rejects_wrong_family_causal_target
#print axioms rejects_wrong_review_claim

end DarkTower.WarMachine.FullCertificateCrossLayerBinding
