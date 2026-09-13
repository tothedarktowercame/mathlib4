import DarkTower.WarMachine.FullCertificatePredicate

/-!
# Exact run and subject binding for the full certificate predicate

This additive refinement does not authenticate bytes or construct the required
node, connection, or equation universes.  Those are inputs from an independent
F11-owned producer.  It only rejects reuse of otherwise positive evidence at a
different run or subject.
-/

namespace DarkTower.WarMachine.FullCertificateRunBinding
open CertificateStates FullCertificatePredicate

structure RunIdentity where
  runId : String
  cohortId : String
  attemptId : String
  deriving DecidableEq, Repr

structure ExternallyFixedRun where
  identity : RunIdentity
  authorityRef : String
  authorityPin : ExactBytePin
  deriving DecidableEq, Repr

def ExternallyFixedRun.valid (r : ExternallyFixedRun) : Prop :=
  r.identity.runId ≠ "" ∧ r.identity.cohortId ≠ "" ∧
  r.identity.attemptId ≠ "" ∧ r.authorityRef ≠ "" ∧ r.authorityPin.valid

structure NodeClaimJoin where
  nodeId : NodeId
  claimId : ClaimId
  scope : Scope
  run : RunIdentity
  subjectNodeId : NodeId
  subjectRunId : String
  claimPin : ExactBytePin
  reviewPin : ExactBytePin
  deriving DecidableEq, Repr

structure EquationClaimJoin where
  requirement : EquationRequirement
  claimId : ClaimId
  scope : Scope
  run : RunIdentity
  subjectNodeId : NodeId
  subjectEquationId : String
  subjectDeclaration : String
  registryPin : ExactBytePin
  declarationPin : ExactBytePin
  witnessPin : ExactBytePin
  deriving DecidableEq, Repr

structure ActionOccurrence where
  run : RunIdentity
  occurrenceId : String
  actionId : ActionId
  deriving DecidableEq, Repr

structure DivergenceAuthorityRecord where
  run : RunIdentity
  selected : ActionOccurrence
  enacted : ActionOccurrence
  divergenceClass : String
  groundsRef : String
  evidenceSource : String
  authorityRef : String
  authorityPin : ExactBytePin
  deriving DecidableEq, Repr

structure RunBindingEvidence where
  nodeJoins : List NodeClaimJoin
  equationJoins : List EquationClaimJoin
  divergenceAuthority : Option DivergenceAuthorityRecord
  deriving DecidableEq, Repr

def nodeJoinsExact (fixed : ExternallyFixedRun) (req : FullScopeRequirements)
    (att : FullAttestation) (rb : RunBindingEvidence) : Prop :=
  rb.nodeJoins.map (·.nodeId) = req.requiredNodes ∧
  ∀ j ∈ rb.nodeJoins,
    j.run = fixed.identity ∧ j.subjectNodeId = j.nodeId ∧
    j.subjectRunId = fixed.identity.runId ∧ j.claimPin.valid ∧ j.reviewPin.valid ∧
    ∃ entry ∈ att.nodeStates,
      entry.nodeId = j.nodeId ∧ entry.state = .supportedAtRun j.claimId j.scope

def equationJoinsExact (fixed : ExternallyFixedRun) (req : FullScopeRequirements)
    (ev : FullScopeEvidence) (rb : RunBindingEvidence) : Prop :=
  rb.equationJoins.map (·.requirement) = req.requiredEquations ∧
  ∀ j ∈ rb.equationJoins,
    j.run = fixed.identity ∧ j.subjectNodeId = j.requirement.nodeId ∧
    j.subjectEquationId = j.requirement.equationId ∧
    j.subjectDeclaration = j.requirement.declaration ∧
    ∃ binding ∈ ev.equationBindings,
      binding = .exact j.requirement j.claimId j.scope
        j.registryPin j.declarationPin j.witnessPin

def divergenceMatches (fixed : ExternallyFixedRun) (req : FullScopeRequirements)
    (selected enacted cls grounds source : String)
    (r : DivergenceAuthorityRecord) : Prop :=
  r.run = fixed.identity ∧ r.selected.run = fixed.identity ∧
  r.enacted.run = fixed.identity ∧ r.selected.actionId = selected ∧
  r.enacted.actionId = enacted ∧ r.selected.occurrenceId ≠ "" ∧
  r.enacted.occurrenceId ≠ "" ∧ r.divergenceClass = cls ∧
  cls ∈ req.allowedDivergenceClasses ∧ r.groundsRef = grounds ∧
  r.evidenceSource = source ∧ r.authorityRef ≠ "" ∧ r.authorityPin.valid

def selectionRunBound (fixed : ExternallyFixedRun) (req : FullScopeRequirements)
    (rb : RunBindingEvidence) : SelectionEnaction → Prop
  | .match selected enacted => selected = enacted ∧ rb.divergenceAuthority = none
  | .typedDivergence selected enacted cls grounds source =>
      ∃ r, rb.divergenceAuthority = some r ∧
        divergenceMatches fixed req selected enacted cls grounds source r
  | .refusedShape _ => False

/-- Refinement of `FullQualifyingRun`; it is not a successful certificate or
an authority producer. -/
def RunBoundQualifyingRun (fixed : ExternallyFixedRun)
    (req : FullScopeRequirements) (ev : FullScopeEvidence)
    (rb : RunBindingEvidence) (att : FullAttestation) : Prop :=
  FullQualifyingRun req ev att ∧ fixed.valid ∧
  nodeJoinsExact fixed req att rb ∧ equationJoinsExact fixed req ev rb ∧
  selectionRunBound fixed req rb att.selectionEnaction

theorem runBound_implies_full {fixed req ev rb att} :
    RunBoundQualifyingRun fixed req ev rb att → FullQualifyingRun req ev att :=
  fun h => h.1

theorem rejects_cross_run_node_reuse (fixed) (req) (ev) (rb) (att)
    (j : NodeClaimJoin) (hj : j ∈ rb.nodeJoins) (hrun : j.run ≠ fixed.identity) :
    ¬ RunBoundQualifyingRun fixed req ev rb att := by
  intro h
  exact hrun (h.2.2.1.2 j hj).1

theorem rejects_cross_run_equation_reuse (fixed) (req) (ev) (rb) (att)
    (j : EquationClaimJoin) (hj : j ∈ rb.equationJoins)
    (hrun : j.run ≠ fixed.identity) :
    ¬ RunBoundQualifyingRun fixed req ev rb att := by
  intro h
  exact hrun (h.2.2.2.1.2 j hj).1

theorem rejects_mismatched_claim_declaration_subject (fixed) (req) (ev) (rb) (att)
    (j : EquationClaimJoin) (hj : j ∈ rb.equationJoins)
    (hm : j.subjectDeclaration ≠ j.requirement.declaration) :
    ¬ RunBoundQualifyingRun fixed req ev rb att := by
  intro h
  exact hm (h.2.2.2.1.2 j hj).2.2.2.1

theorem rejects_borrowed_divergence_authority (fixed) (req) (ev) (rb) (att)
    (selected enacted cls grounds source : String) (r : DivergenceAuthorityRecord)
    (hsel : att.selectionEnaction = .typedDivergence selected enacted cls grounds source)
    (href : rb.divergenceAuthority = some r) (hrun : r.run ≠ fixed.identity) :
    ¬ RunBoundQualifyingRun fixed req ev rb att := by
  intro h
  have hs := h.2.2.2.2
  rw [hsel] at hs
  rcases hs with ⟨r', hr', hm⟩
  rw [href] at hr'
  injection hr' with heq
  subst r'
  exact hrun hm.1

theorem rejects_unauthorized_divergence_class (fixed) (req) (ev) (rb) (att)
    (selected enacted cls grounds source : String) (r : DivergenceAuthorityRecord)
    (hsel : att.selectionEnaction = .typedDivergence selected enacted cls grounds source)
    (href : rb.divergenceAuthority = some r)
    (hclass : cls ∉ req.allowedDivergenceClasses) :
    ¬ RunBoundQualifyingRun fixed req ev rb att := by
  intro h
  have hs := h.2.2.2.2
  rw [hsel] at hs
  rcases hs with ⟨r', hr', hm⟩
  rw [href] at hr'
  injection hr' with heq
  subst r'
  exact hclass hm.2.2.2.2.2.2.2.2.1

#print axioms runBound_implies_full
#print axioms rejects_cross_run_node_reuse
#print axioms rejects_cross_run_equation_reuse
#print axioms rejects_mismatched_claim_declaration_subject
#print axioms rejects_borrowed_divergence_authority
#print axioms rejects_unauthorized_divergence_class

end DarkTower.WarMachine.FullCertificateRunBinding
