import DarkTower.WarMachine.PrecisionFromObservation
import DarkTower.WarMachine.EvidenceFromTheProcess
import DarkTower.WarMachine.R15HabitPrior
import DarkTower.WarMachine.CTauClassPreference
import DarkTower.WarMachine.R15StrategicTarget
import DarkTower.WarMachine.R10ScheduledEntrypoint
import DarkTower.WarMachine.R11JointAction
import Mathlib.Tactic

/-!
# R20: the per-click active-inference certificate

At the end of a click the machine says, node by node, what happened in the
terms of the theory and whether its retained record agrees.  The click is
certified as active inference only when every row agrees.  Absence is a hole,
never a pass.

This is the final assembly described by `PROOF-2a-THEOREM-draft-2026-09-24.md`
lines 28--32 and 47--56: each row identifies consumed values, checks the Lean
proposition on them, and has an independently constructed bad extract that
fails that same proposition.  Da Costa et al. (2020),
`refs/dacosta2020.txt:222-227`, call the paired perception/action account
“self-evidencing”.  Joe's 2026-10-05 ruling identifies R20 as the final
Proof-2A/Proof-2B certificate and requires the qualitative result (for
example, whether F discriminated between policies) to be printed.

| row | module | proposition | control |
| --- | --- | --- | --- |
| precision | `PrecisionFromObservation` | `Conforms` | unchanged despite discriminating F |
| evidence | `EvidenceFromTheProcess` | Bayes posterior correspondence | forged unchanged posterior |
| habit | `R15TemporalHierarchy` | `TwoTickFeedback` | unwitnessed outcome |
| class preference | `CTauClassPreference` | reported `classRisk` | altered risk |
| strategic focus | `R15StrategicTarget` | `StrategicTickConforms` | wrong class |
| liveness | `R10ScheduledEntrypoint` | honest live label | green no-op |
| independence | R9 adapter | author/reviewer verdict | same author and reviewer |
| joint action | `R11JointAction.SharedState` | `OneWriter` | two writers |

The evidence module supplies the posterior but no before/after receipt, so
`EvidenceRow` is the minimal carrier for those existing quantities.  R9's
`Holes` declarations concern generic claims and witnesses rather than an
author/reviewer receipt; `IndependenceRow` is therefore the equally small
boundary required by this certificate.  Neither adapter adds theory.
-/

namespace DarkTower.WarMachine.R20Certificate

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

inductive Node
  | precision | evidence | habit | classPreference
  | strategicFocus | liveness | independence | jointAction
  deriving DecidableEq, Repr, Fintype

inductive PrecisionCase | unchanged | moreDecisive | lessDecisive deriving DecidableEq, Repr
inductive EvidenceCase | beliefUnchanged | beliefMoved deriving DecidableEq, Repr
inductive HabitCase | reinforced | unchanged deriving DecidableEq, Repr
inductive ClassPreferenceCase
  | beforeHorizon | atHorizonSupported | atHorizonUnsupported
  deriving DecidableEq, Repr
inductive StrategicFocusCase | focusKept | focusChanged deriving DecidableEq, Repr
inductive LivenessCase | live | notLive deriving DecidableEq, Repr
inductive IndependenceCase | authorIsNotReviewer | sameAgent deriving DecidableEq, Repr
inductive JointActionCase | eachTookItsPart | takenTwice | dropped deriving DecidableEq, Repr

inductive Case
  | precision (v : PrecisionCase) | evidence (v : EvidenceCase)
  | habit (v : HabitCase) | classPreference (v : ClassPreferenceCase)
  | strategicFocus (v : StrategicFocusCase) | liveness (v : LivenessCase)
  | independence (v : IndependenceCase) | jointAction (v : JointActionCase)
  deriving DecidableEq, Repr

abbrev Policy := PrecisionFromObservation.TwoPolicy
abbrev Hidden := Fin 2
abbrev Observation := Bool

/-- The existing finite Bayes quantities, retained before and after. -/
structure EvidenceRow where
  prior : EvidenceFromTheProcess.Belief Hidden
  likelihood : EvidenceFromTheProcess.Likelihood Hidden Observation
  observation : Observation
  posterior : EvidenceFromTheProcess.Belief Hidden

def EvidenceConforms (r : EvidenceRow) : Prop :=
  r.posterior = EvidenceFromTheProcess.posterior r.prior r.likelihood r.observation

structure ClassPreferenceRow where
  horizon : Nat
  tau : Nat
  predicted : CTauClassPreference.Distribution
  reportedRisk : EReal

def ClassPreferenceConforms (r : ClassPreferenceRow) : Prop :=
  r.reportedRisk = CTauClassPreference.classRisk r.predicted
    (CTauClassPreference.classPreference r.horizon r.tau)

structure StrategicFocusRow where
  previousFocus : Nat
  tick : R15StrategicTarget.StrategicTickRecord

def StrategicFocusConforms (r : StrategicFocusRow) : Prop :=
  R15StrategicTarget.StrategicTickConforms r.tick

abbrev LiveRow := R10ScheduledEntrypoint.TickOutcome Nat
def LivenessConforms (r : LiveRow) : Prop :=
  r.reportedLive = decide (R10ScheduledEntrypoint.LiveTick r)

inductive IndependenceVerdict | independent | sameAgent deriving DecidableEq, Repr
structure IndependenceRow where
  author : Fin 2
  reviewer : Fin 2
  verdict : IndependenceVerdict

def IndependenceConforms (r : IndependenceRow) : Prop :=
  r.verdict = if r.author = r.reviewer then .sameAgent else .independent

abbrev JointRow := Fin 2 → R11JointAction.Ownership Unit (Fin 2)

def NodeRecord : Node → Type
  | .precision => PrecisionFromObservation.TickRecord Policy
  | .evidence => EvidenceRow
  | .habit => R15TemporalHierarchy.TwoTickRecord
  | .classPreference => ClassPreferenceRow
  | .strategicFocus => StrategicFocusRow
  | .liveness => LiveRow
  | .independence => IndependenceRow
  | .jointAction => JointRow

def conforms : (n : Node) → NodeRecord n → Prop
  | .precision, r => PrecisionFromObservation.Conforms r
  | .evidence, r => EvidenceConforms r
  | .habit, r => R15TemporalHierarchy.TwoTickFeedback r
  | .classPreference, r => ClassPreferenceConforms r
  | .strategicFocus, r => StrategicFocusConforms r
  | .liveness, r => LivenessConforms r
  | .independence, r => IndependenceConforms r
  | .jointAction, r => R11JointAction.OneWriter r

def caseOf : (n : Node) → NodeRecord n → Case
  | .precision, r => .precision <| if r.betaPosterior = r.betaPrior then .unchanged
      else if r.betaPosterior < r.betaPrior then .moreDecisive else .lessDecisive
  | .evidence, r => .evidence <| if r.posterior = r.prior then .beliefUnchanged else .beliefMoved
  | .habit, r => .habit <| if r.outcome.witnessed && r.outcome.succeeded then .reinforced else .unchanged
  | .classPreference, r => .classPreference <| if r.tau < r.horizon then .beforeHorizon
      else if r.reportedRisk = ⊤ then .atHorizonUnsupported else .atHorizonSupported
  | .strategicFocus, r => .strategicFocus <|
      if r.previousFocus = r.tick.focus then .focusKept else .focusChanged
  | .liveness, r => .liveness <| if R10ScheduledEntrypoint.LiveTick r then .live else .notLive
  | .independence, r => .independence <|
      if r.author = r.reviewer then .sameAgent else .authorIsNotReviewer
  | .jointAction, r => .jointAction <| match (R11JointAction.writers r ()).card with
      | 0 => .dropped | 1 => .eachTookItsPart | _ => .takenTwice

/-- The precision row prints the fixed-point's qualitative direction. -/
theorem precision_constant_F_is_unchanged
    (r : PrecisionFromObservation.TickRecord Policy) (h : PrecisionFromObservation.Conforms r)
    (c : ℝ) (hc : r.F = fun _ => c) : caseOf .precision r = .precision .unchanged := by
  have fixed := h.2.2.1
  have eq := (PrecisionFromObservation.constant_F_posterior_temperature_iff
    h.2.1 r.E r.G c).mp (by simpa [hc] using fixed)
  simp [caseOf, eq]

theorem evidence_state_independent_is_unchanged (r : EvidenceRow)
    (h : EvidenceConforms r) (normal : ∑ s, r.prior s = 1)
    (c : ℝ) (hc : 0 < c) (constant : ∀ s, r.likelihood s r.observation = c) :
    r.posterior = r.prior := by
  have unchanged := EvidenceFromTheProcess.no_evidence_no_change
    r.prior r.likelihood r.observation normal c hc constant
  exact h.trans unchanged

theorem failed_habit_is_unchanged (r : R15TemporalHierarchy.TwoTickRecord)
    (failed : r.outcome.succeeded = false) : caseOf .habit r = .habit .unchanged := by
  simp [caseOf, failed]

theorem liveness_case_is_live_iff (r : LiveRow) :
    caseOf .liveness r = .liveness .live ↔ R10ScheduledEntrypoint.LiveTick r := by
  simp [caseOf]

inductive RowVerdict | notRecorded | agrees (case : Case) | disagrees (case : Case)
  deriving DecidableEq, Repr

abbrev Records := (n : Node) → Option (NodeRecord n)
abbrev Certificate := Node → RowVerdict

noncomputable def certify (records : Records) : Certificate := fun n =>
  match records n with
  | none => .notRecorded
  | some r => if conforms n r then .agrees (caseOf n r) else .disagrees (caseOf n r)

def Certified (certificate : Certificate) : Prop :=
  ∀ node, ∃ c, certificate node = .agrees c

theorem certified_iff (records : Records) :
    Certified (certify records) ↔
      ∀ node, ∃ r, records node = some r ∧ conforms node r := by
  classical
  constructor
  · intro certified node
    generalize present : records node = option
    cases option with
    | none =>
        rcases certified node with ⟨c, hc⟩
        simp [certify, present] at hc
    | some r =>
        refine ⟨r, rfl, ?_⟩
        by_contra bad
        rcases certified node with ⟨c, hc⟩
        simp [certify, present, bad] at hc
  · intro complete node
    have row := complete node
    cases node <;> simp only [certify] at row ⊢ <;>
      rcases row with ⟨r, hr, good⟩ <;> simp [hr, good]

theorem missing_not_certified (records : Records) (node : Node)
    (missing : records node = none) : ¬ Certified (certify records) := by
  intro certified
  rcases certified node with ⟨c, hc⟩
  simp [certify, missing] at hc

theorem refused_row_disagrees (records : Records) (node : Node) (r : NodeRecord node)
    (present : records node = some r) (bad : ¬ conforms node r) :
    certify records node = .disagrees (caseOf node r) := by
  simp [certify, present, bad]

def badEvidence : EvidenceRow where
  prior := fun _ => 1 / 2
  likelihood := fun _ _ => 1
  observation := false
  posterior := fun _ => 0

theorem badEvidence_refused : ¬ EvidenceConforms badEvidence := by
  intro h
  have at0 := congrFun h (0 : Hidden)
  norm_num [badEvidence, EvidenceFromTheProcess.posterior,
    EvidenceFromTheProcess.evidence] at at0

def badClass : ClassPreferenceRow where
  horizon := 2; tau := 1
  predicted := CTauClassPreference.waitingPreference
  reportedRisk := 1

theorem badClass_refused : ¬ ClassPreferenceConforms badClass := by
  change (1 : EReal) ≠ CTauClassPreference.classRisk
    CTauClassPreference.waitingPreference CTauClassPreference.waitingPreference
  rw [CTauClassPreference.waiting_point_mass_risk_zero]
  norm_num

def badLive : LiveRow := ⟨0, 0, true⟩
theorem badLive_refused : ¬ LivenessConforms badLive := by
  simp [LivenessConforms, badLive, R10ScheduledEntrypoint.LiveTick,
    R10ScheduledEntrypoint.ChangedState]

def badIndependence : IndependenceRow := ⟨0, 0, .independent⟩
theorem badIndependence_refused : ¬ IndependenceConforms badIndependence := by
  simp [IndependenceConforms, badIndependence]

theorem precision_control_disagrees (records : Records)
    (r : PrecisionFromObservation.TickRecord Policy)
    (present : records .precision = some r) (bad : ¬ PrecisionFromObservation.Conforms r) :
    certify records .precision = .disagrees (caseOf .precision r) :=
  refused_row_disagrees records .precision r present bad

theorem evidence_control_disagrees (records : Records)
    (present : records .evidence = some badEvidence) :
    certify records .evidence = .disagrees (caseOf .evidence badEvidence) :=
  refused_row_disagrees records .evidence badEvidence present badEvidence_refused

theorem habit_control_disagrees (records : Records)
    (present : records .habit = some R15TemporalHierarchy.unwitnessedRecord) :
    certify records .habit = .disagrees (caseOf .habit R15TemporalHierarchy.unwitnessedRecord) :=
  refused_row_disagrees records .habit _ present R15TemporalHierarchy.unwitnessedRecord_is_rejected

theorem class_control_disagrees (records : Records)
    (present : records .classPreference = some badClass) :
    certify records .classPreference = .disagrees (caseOf .classPreference badClass) :=
  refused_row_disagrees records .classPreference badClass present badClass_refused

def badStrategic : StrategicFocusRow := ⟨7, R15StrategicTarget.wrongClassTick⟩
theorem strategic_control_disagrees (records : Records)
    (present : records .strategicFocus = some badStrategic) :
    certify records .strategicFocus = .disagrees (caseOf .strategicFocus badStrategic) :=
  refused_row_disagrees records .strategicFocus badStrategic present
    (by exact R15StrategicTarget.wrongClassTick_rejected)

theorem liveness_control_disagrees (records : Records)
    (present : records .liveness = some badLive) :
    certify records .liveness = .disagrees (caseOf .liveness badLive) :=
  refused_row_disagrees records .liveness badLive present badLive_refused

theorem independence_control_disagrees (records : Records)
    (present : records .independence = some badIndependence) :
    certify records .independence = .disagrees (caseOf .independence badIndependence) :=
  refused_row_disagrees records .independence badIndependence present badIndependence_refused

theorem joint_control_disagrees (records : Records)
    (present : records .jointAction = some R11JointAction.bothClaim) :
    certify records .jointAction =
      .disagrees (caseOf .jointAction R11JointAction.bothClaim) :=
  refused_row_disagrees records .jointAction _ present R11JointAction.both_claim_refused

/-- Fixed print order for the run's succinct certificate. -/
def nodeOrder : List Node :=
  [.precision, .evidence, .habit, .classPreference, .strategicFocus,
   .liveness, .independence, .jointAction]

def summary (certificate : Certificate) : List (Node × RowVerdict) :=
  nodeOrder.map fun node => (node, certificate node)

end
end DarkTower.WarMachine.R20Certificate
