import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

/-!
# R12 two-layer calibration admission

This module states the record-level role checked by
`futon2/src/futon2/aif/calibration_admission.clj/admit!`, labelled by
`futon2/src/futon2/aif/calibration_cycle.clj`, and projected by
`independent-layer-2?` / `r12-certificate` in
`futon2/src/futon2/aif/wm/apparatus_certificates.clj`, read at Futon2 commit
`0f9587532031beb50a21091cc41cd10f4a16ff63`.

`Admitted` states that a returned artifact is tied to one R12 commission and
approved by a check for that exact return. `ValueEvidence` additionally
requires an admitted, independent Layer-2 record. Layer-1 content is retained
but cannot satisfy that additional condition.

This is a predicate over retained records. It does not prove that a commission,
return, check, outcome, or independence witness was produced in reality. It
does not model runtime schemas, `:check/id`, scan-map structure, posterior
numericity, class-count consistency, evidence provenance, source hashes, or
the apparatus receipt's outer status/node projection. In particular, the Lean
claim corresponds to the runtime certificate only when the supplied Layer-2
flags faithfully represent `:layer :R12/layer-2`, `:status :admitted`, and
`:independent? true` in the returned artifact.
-/

namespace DarkTower.WarMachine.R12TwoLayerCalibration

inductive Node where
  | r12
  | other
  deriving DecidableEq, Repr

inductive Verdict where
  | approve
  | refuse
  deriving DecidableEq, Repr

/-- Layer-1 diagnostic content. `perfect` stands for any perfect
prediction-versus-model-realisation result; `diagnostic` stands for the
retained Layer-1 scan/diagnostic payload. Neither is value evidence. -/
structure Layer1Record where
  perfect : Bool
  diagnostic : Nat
  deriving DecidableEq, Repr

/-- The returned `:layer-2/independent-evidence` record. `isLayer2` stands for
`:layer :R12/layer-2`; `admitted` for `:status :admitted`; and `independent`
for `:independent? true`. -/
structure Layer2Record where
  isLayer2 : Bool
  admitted : Bool
  independent : Bool
  deriving DecidableEq, Repr

/-- The returned `:artifact`. `layer1` stands for `:layer-1/label` and its
diagnostic content; `layer2` stands for `:layer-2/independent-evidence`. -/
structure Artifact where
  layer1 : Layer1Record
  layer2 : Option Layer2Record
  deriving DecidableEq, Repr

/-- The commission record. `node` stands for `:node`; `commissionId` for the
possibly absent `:commission/id`. -/
structure Commission where
  node : Node
  commissionId : Option Nat
  deriving DecidableEq, Repr

/-- The returned record. `node`, `commissionId`, `returnId`, and `artifact`
stand for runtime `:node`, `:commission/id`, `:return/id`, and `:artifact`. -/
structure ReturnRecord where
  node : Node
  commissionId : Option Nat
  returnId : Option Nat
  artifact : Artifact
  deriving DecidableEq, Repr

/-- The structural check. `node`, `commissionId`, `returnId`, and `verdict`
stand for runtime `:node`, `:commission/id`, `:return/id`, and `:verdict`. -/
structure CheckRecord where
  node : Node
  commissionId : Option Nat
  returnId : Option Nat
  verdict : Verdict
  deriving DecidableEq, Repr

/-- One R12 admission question over a commission, return, and check. -/
structure CalibrationRecord where
  /-- Runtime COMMISSION argument to `admit!`. -/
  commission : Commission
  /-- Runtime RETURN argument to `admit!`. -/
  returned : ReturnRecord
  /-- Runtime CHECK argument to `admit!`. -/
  checked : CheckRecord
  deriving DecidableEq, Repr

/-- The clauses accepted by `calibration-admission/admit!`, stated without the
checker. The two existential equalities also require the IDs to be present. -/
def Admitted (record : CalibrationRecord) : Prop :=
  record.commission.node = Node.r12 ∧
  record.returned.node = Node.r12 ∧
  ∃ commissionId returnId,
    record.commission.commissionId = some commissionId ∧
    record.returned.commissionId = some commissionId ∧
    record.returned.returnId = some returnId ∧
    record.checked.node = Node.r12 ∧
    record.checked.returnId = some returnId ∧
    record.checked.commissionId = some commissionId ∧
    record.checked.verdict = Verdict.approve

/-- Executable transcription of the admission clauses. -/
def checkAdmitted (record : CalibrationRecord) : Bool :=
  decide (record.commission.node = Node.r12) &&
  decide (record.returned.node = Node.r12) &&
  match record.commission.commissionId, record.returned.returnId with
  | some commissionId, some returnId =>
      decide (record.returned.commissionId = some commissionId) &&
      decide (record.checked.node = Node.r12) &&
      decide (record.checked.returnId = some returnId) &&
      decide (record.checked.commissionId = some commissionId) &&
      decide (record.checked.verdict = Verdict.approve)
  | _, _ => false

theorem checkAdmitted_eq_true_iff (record : CalibrationRecord) :
    checkAdmitted record = true ↔ Admitted record := by
  simp [checkAdmitted, Admitted]
  aesop

/-- R12 value evidence: admission alone is insufficient; the returned artifact
must retain an actual Layer-2 record that is admitted and independent. -/
def ValueEvidence (record : CalibrationRecord) : Prop :=
  Admitted record ∧
  ∃ layer2,
    record.returned.artifact.layer2 = some layer2 ∧
    layer2.isLayer2 = true ∧
    layer2.admitted = true ∧
    layer2.independent = true

/-- Executable transcription of the value-evidence clauses. -/
def checkValueEvidence (record : CalibrationRecord) : Bool :=
  checkAdmitted record &&
  match record.returned.artifact.layer2 with
  | some layer2 => layer2.isLayer2 && layer2.admitted && layer2.independent
  | none => false

theorem checkValueEvidence_eq_true_iff (record : CalibrationRecord) :
    checkValueEvidence record = true ↔ ValueEvidence record := by
  simp [checkValueEvidence, ValueEvidence, checkAdmitted_eq_true_iff]
  aesop

/-- The node's separation rule, universally over the record and therefore over
all possible Layer-1 content: without an admitted independent Layer-2 record,
the artifact is not value evidence. -/
theorem no_independent_admitted_layer2_not_valueEvidence
    (record : CalibrationRecord)
    (absent : ∀ layer2, record.returned.artifact.layer2 = some layer2 →
      ¬ (layer2.isLayer2 = true ∧ layer2.admitted = true ∧
        layer2.independent = true)) :
    ¬ ValueEvidence record := by
  rintro ⟨_, layer2, retained, layer, admitted, independent⟩
  exact absent layer2 retained ⟨layer, admitted, independent⟩

theorem valueEvidence_implies_admitted (record : CalibrationRecord) :
    ValueEvidence record → Admitted record := fun evidence => evidence.1

def perfectLayer1 : Layer1Record := { perfect := true, diagnostic := 100 }
def ordinaryArtifact : Artifact := { layer1 := perfectLayer1, layer2 := none }

def baseCommission : Commission := { node := .r12, commissionId := some 7 }
def baseReturn : ReturnRecord :=
  { node := .r12, commissionId := some 7, returnId := some 11, artifact := ordinaryArtifact }
def approvingCheck : CheckRecord :=
  { node := .r12, commissionId := some 7, returnId := some 11, verdict := .approve }

/-- Positive admission witness; it deliberately carries only Layer 1. -/
def admittedLayer1Only : CalibrationRecord :=
  { commission := baseCommission, returned := baseReturn, checked := approvingCheck }

theorem admittedLayer1Only_is_admitted : Admitted admittedLayer1Only := by
  rw [← checkAdmitted_eq_true_iff]
  decide

theorem admittedLayer1Only_is_not_valueEvidence : ¬ ValueEvidence admittedLayer1Only := by
  apply no_independent_admitted_layer2_not_valueEvidence
  simp [admittedLayer1Only, baseReturn, ordinaryArtifact]

def independentLayer2 : Layer2Record :=
  { isLayer2 := true, admitted := true, independent := true }

/-- Positive value-evidence witness. -/
def valueRecord : CalibrationRecord :=
  { admittedLayer1Only with
    returned := { baseReturn with artifact := { ordinaryArtifact with layer2 := some independentLayer2 } } }

theorem valueRecord_is_valueEvidence : ValueEvidence valueRecord := by
  rw [← checkValueEvidence_eq_true_iff]
  decide

/-- Control B: Layer 2 is present and admitted, but not independent. -/
def dependentLayer2Record : CalibrationRecord :=
  { valueRecord with
    returned := { baseReturn with artifact :=
      { ordinaryArtifact with layer2 := some { independentLayer2 with independent := false } } } }

theorem dependentLayer2Record_is_admitted : Admitted dependentLayer2Record := by
  rw [← checkAdmitted_eq_true_iff]
  decide

theorem dependentLayer2Record_is_not_valueEvidence : ¬ ValueEvidence dependentLayer2Record := by
  apply no_independent_admitted_layer2_not_valueEvidence
  simp [dependentLayer2Record, valueRecord, baseReturn, ordinaryArtifact, independentLayer2]

/-- Control C: a return tied to a different commission, corresponding to
`:r12/untied-return`. -/
def untiedReturnRecord : CalibrationRecord :=
  { admittedLayer1Only with returned := { baseReturn with commissionId := some 8 } }

theorem untiedReturnRecord_is_rejected : ¬ Admitted untiedReturnRecord := by
  intro admitted
  obtain ⟨_, _, commissionId, _, commissionPresent, returnTied, _⟩ := admitted
  simp [untiedReturnRecord, admittedLayer1Only, baseCommission] at commissionPresent
  subst commissionId
  simp [untiedReturnRecord, baseReturn] at returnTied

/-- Control D: the exact check refuses, corresponding to
`:r12/unchecked-return`. -/
def refusedCheckRecord : CalibrationRecord :=
  { admittedLayer1Only with checked := { approvingCheck with verdict := .refuse } }

theorem refusedCheckRecord_is_rejected : ¬ Admitted refusedCheckRecord := by
  intro admitted
  obtain ⟨_, _, _, _, _, _, _, _, _, _, approved⟩ := admitted
  cases approved

end DarkTower.WarMachine.R12TwoLayerCalibration
