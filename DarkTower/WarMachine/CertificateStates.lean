import Mathlib

/-!
# Full-run certificate state algebra

This module defines the finite census vocabulary required by row 24.  “Full”
means that every declared node, connection, and record family has a typed
entry; it does not mean that every entry is positive.

`qualifyingRun` requires an explicit `QualifyingRuling` value, including its
bytes pin.  This module offers all three candidate readings and does not create
a ruling value or choose among them.  In the absence of such a value, no term
can be submitted to `qualifyingRun`, so nothing is certifiable here.
-/

namespace DarkTower.WarMachine.CertificateStates

abbrev ClaimId := String
abbrev Scope := String
abbrev Pin := String
abbrev NodeId := String
abbrev ConnectionId := String
abbrev ActionId := String

/-- Closed state of one node claim.  Claim identity and scope remain data even
for negative and incomplete states. -/
inductive NodeValidationState
  | supportedAtRun (claimId : ClaimId) (scope : Scope)
  | supportedAtOtherPin (claimId : ClaimId) (scope : Scope) (pin : Pin)
  | refutedAtPin (claimId : ClaimId) (scope : Scope) (pin : Pin)
  | typedAbsence (claimId : ClaimId) (scope : Scope) (absenceClass : String)
  | mechanismOnly (claimId : ClaimId) (scope : Scope)
  | unvalidated (claimId : ClaimId) (scope : Scope)
  deriving DecidableEq, Repr

/-- Closed state of one declared connection. -/
inductive ConnectionState
  | firedClassified (classification : String) (evidenceSource : String)
  | mandatoryUnfired (scope : Scope)
  | conditionalWithPremise (premise : String) (held : Bool)
      (evidenceSource : String)
  | aspirationalRuled (rulingRef : String) (rulingBytesPin : Pin)
  | retiredSource (sourceRef : String)
  deriving DecidableEq, Repr

/-- Selection/enaction is a sum: equality, fully grounded divergence, or a
typed refusal to construct either shape. -/
inductive SelectionEnaction
  | «match» (selected enacted : ActionId)
  | typedDivergence (selected enacted : ActionId) (divergenceClass : String)
      (groundsRef : String) (evidenceSource : String)
  | refusedShape (reason : String)
  deriving DecidableEq, Repr

/-- The seven record families required by the row-24 record manifest. -/
inductive RecordFamily
  | fullLoopCheckpoints
  | wmTraceRecords
  | tickRunRecords
  | closeCohortRecords
  | dispatchJobRecords
  | parkContinuationRecords
  | reviewAdmissionRecords
  deriving DecidableEq, Repr

def allRecordFamilies : List RecordFamily :=
  [.fullLoopCheckpoints, .wmTraceRecords, .tickRunRecords,
   .closeCohortRecords, .dispatchJobRecords, .parkContinuationRecords,
   .reviewAdmissionRecords]

/-- Presence is never a bare boolean: success retains its consistency evidence,
while a gap retains its type and family. -/
inductive RecordFamilyPresence
  | presentAndConsistent (family : RecordFamily) (evidenceSource : String)
  | typedGap (family : RecordFamily) (gapClass : String)
  deriving DecidableEq, Repr

def RecordFamilyPresence.family : RecordFamilyPresence → RecordFamily
  | .presentAndConsistent family _ => family
  | .typedGap family _ => family

structure NodeEntry where
  nodeId : NodeId
  state : NodeValidationState
  deriving DecidableEq, Repr

structure ConnectionEntry where
  connectionId : ConnectionId
  state : ConnectionState
  deriving DecidableEq, Repr

structure NegativeScopeItem where
  itemId : String
  description : String
  deriving DecidableEq, Repr

/-- Raw full attestation.  The two universes are independently declared so the
census predicate can reject missing, duplicate, extra, or reordered entries. -/
structure FullAttestation where
  declaredNodes : List NodeId
  nodeStates : List NodeEntry
  declaredConnections : List ConnectionId
  connectionStates : List ConnectionEntry
  selectionEnaction : SelectionEnaction
  recordFamilies : List RecordFamilyPresence
  negativeScope : List NegativeScopeItem
  deriving DecidableEq, Repr

/-- Finite census completeness, with no positivity condition. -/
def CensusComplete (att : FullAttestation) : Prop :=
  att.declaredNodes.Nodup ∧
  att.nodeStates.map (·.nodeId) = att.declaredNodes ∧
  att.declaredConnections.Nodup ∧
  att.connectionStates.map (·.connectionId) = att.declaredConnections ∧
  att.recordFamilies.map RecordFamilyPresence.family = allRecordFamilies

instance censusCompleteDecidable (att : FullAttestation) : Decidable (CensusComplete att) :=
  by
    unfold CensusComplete
    infer_instance

theorem censusCompleteness_is_decidable (att : FullAttestation) :
    CensusComplete att ∨ ¬ CensusComplete att := by
  exact decidable_em (CensusComplete att)

def positiveAtThisRun : NodeValidationState → Prop
  | .supportedAtRun _ _ => True
  | _ => False

instance positiveAtThisRunDecidable (state : NodeValidationState) :
    Decidable (positiveAtThisRun state) := by
  cases state <;> simp [positiveAtThisRun] <;> infer_instance

/-- Reading one: a complete, honestly typed census qualifies as-is. -/
def readingOne (att : FullAttestation) : Prop := CensusComplete att

/-- Reading two: census completeness plus positive at-this-run support for
every node. -/
def readingTwo (att : FullAttestation) : Prop :=
  CensusComplete att ∧ ∀ entry ∈ att.nodeStates, positiveAtThisRun entry.state

/-- Reading three: reading two except for an exact externally ruled item set.
Membership is by stable node id; this definition does not decide that the set
is legitimate. -/
def readingThree (ruledOut : List NodeId) (att : FullAttestation) : Prop :=
  CensusComplete att ∧
  ∀ entry ∈ att.nodeStates,
    positiveAtThisRun entry.state ∨ entry.nodeId ∈ ruledOut

inductive QualifyingReading | one | two | three
  deriving DecidableEq, Repr

/-- Joe's still-pending authority input.  `bytesPin` binds the selected reading
and ruled-out set to the future written ruling. -/
structure QualifyingRuling where
  chosenReading : QualifyingReading
  ruledOutItems : List NodeId
  bytesPin : Pin
  deriving DecidableEq, Repr

/-- No unpinned ruling can certify.  Otherwise the ruling selects one of the
three definitions above rather than this module silently choosing one. -/
def qualifyingRun (ruling : QualifyingRuling) (att : FullAttestation) : Prop :=
  ruling.bytesPin ≠ "" ∧
  match ruling.chosenReading with
  | .one => readingOne att
  | .two => readingTwo att
  | .three => readingThree ruling.ruledOutItems att

theorem readingTwo_implies_readingThree_empty (att : FullAttestation) :
    readingTwo att → readingThree [] att := by
  rintro ⟨hcensus, hall⟩
  exact ⟨hcensus, fun entry hentry => Or.inl (hall entry hentry)⟩

theorem readingThree_empty_iff_readingTwo (att : FullAttestation) :
    readingThree [] att ↔ readingTwo att := by
  constructor
  · rintro ⟨hcensus, hall⟩
    refine ⟨hcensus, ?_⟩
    intro entry hentry
    rcases hall entry hentry with hpositive | himpossible
    · exact hpositive
    · simp at himpossible
  · exact readingTwo_implies_readingThree_empty att

/-- A retained refutation cannot satisfy the all-positive reading. -/
theorem refutedNode_cannot_satisfy_readingTwo
    (att : FullAttestation) (nodeId : NodeId)
    (claimId : ClaimId) (scope : Scope) (pin : Pin)
    (hmember : ⟨nodeId, .refutedAtPin claimId scope pin⟩ ∈ att.nodeStates) :
    ¬ readingTwo att := by
  intro hreading
  have hpositive := hreading.2 _ hmember
  simp [positiveAtThisRun] at hpositive

#print axioms censusCompleteness_is_decidable
#print axioms readingTwo_implies_readingThree_empty
#print axioms readingThree_empty_iff_readingTwo
#print axioms refutedNode_cannot_satisfy_readingTwo

end DarkTower.WarMachine.CertificateStates
