import Mathlib.Tactic

/-!
# Admission inputs and measurement domains (defect lines R7, R8)

Source: `~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` R7, R8
(claude-9, 2026-10-26).

R7.  The selected occurrence's prediction inputs are part of the sealed
admission record; sealing without them is not an admission.  Observed on
machinery-149 attempt-001 (run 90ca, `~/notes/wm-next/minimum-construction-learning/admission-stop.md`):
the first stop is `:wm/token-outcome-prediction-v1 :status :refused :reason
:prediction-input-unavailable :target "M-war-machine-wiring"`, then
`:wm/token-outcome-comparison-v1 :status :refused :reason :prediction-unavailable
:measurement-source nil`, before any trial row.  Repair futon2 `cb9da1e31`
exists; this clause pins it.

R8.  The measurement domain of a prediction equals the domain of the observation
it is scored against; mission accounting and pattern learning are distinct
domains.  Observed on machinery-150 attempt-002 (run 25e24,
`~/notes/wm-next/diagnostic-clicks/remaining-two/token-outcome-2.edn`): two
pattern-done token predictions (gauntlet occurrence 0, world-is-hypergraph
occurrence 19) against six mission-hole measurements; all 27 trials held
`:observation-missing`.

This module does not import `PatternObservationAdmission`: that module is a
conditional admission over a supplied witness and does not state R8.
-/

namespace DarkTower.WarMachine.AdmissionInputs

abbrev Id := Nat

/-- The prediction input at admission: present with its digest, or unavailable
for a typed reason.  No absent inhabitant. -/
inductive PredictionInput where
  | present (digest : Id)
  | unavailable (reason : Id)
  deriving DecidableEq, Repr

structure AdmissionRecord where
  occurrence : Id
  target : Id
  prediction : PredictionInput
  sealed : Bool
  deriving DecidableEq, Repr

def AdmissionRecord.isAdmission (r : AdmissionRecord) : Bool :=
  match r.prediction with
  | .present _ => r.sealed
  | .unavailable _ => false

/-- R7.  An admission is a sealed record whose prediction input is present. -/
def AdmissionRecord.IsAdmission (r : AdmissionRecord) : Prop := r.isAdmission = true

instance (r : AdmissionRecord) : Decidable r.IsAdmission := by
  unfold AdmissionRecord.IsAdmission
  infer_instance

theorem sealed_without_prediction_not_admission (r : AdmissionRecord) (reason : Id)
    (h : r.prediction = .unavailable reason) : ¬ r.IsAdmission := by
  simp [AdmissionRecord.IsAdmission, AdmissionRecord.isAdmission, h]

theorem admission_has_prediction (r : AdmissionRecord) (h : r.IsAdmission) :
    ∃ d, r.prediction = .present d := by
  unfold AdmissionRecord.IsAdmission AdmissionRecord.isAdmission at h
  cases hp : r.prediction with
  | present d => exact ⟨d, rfl⟩
  | unavailable _ => simp [hp] at h

/-! ### Control: run 90ca

Target 98 is M-war-machine-wiring (its position in the m150 census, kept for
cross-reference); reason 1 is `:prediction-input-unavailable`. -/

def run90caRecord (sealed : Bool) : AdmissionRecord :=
  ⟨1, 98, .unavailable 1, sealed⟩

theorem run90ca_not_admission (sealed : Bool) : ¬ (run90caRecord sealed).IsAdmission :=
  sealed_without_prediction_not_admission _ 1 rfl

/-! ## R8: measurement domains -/

inductive Domain where
  | missionAccounting
  | patternLearning
  deriving DecidableEq, Repr

theorem domains_distinct : Domain.missionAccounting ≠ Domain.patternLearning := by decide

structure Prediction where
  token : Id
  domain : Domain
  deriving DecidableEq, Repr

structure Observation where
  token : Id
  domain : Domain
  deriving DecidableEq, Repr

/-- A prediction is scorable against an observation of the same token in the
same domain. -/
def Scorable (p : Prediction) (o : Observation) : Prop :=
  p.domain = o.domain ∧ p.token = o.token

instance (p : Prediction) (o : Observation) : Decidable (Scorable p o) := by
  unfold Scorable
  infer_instance

theorem cross_domain_not_scorable (p : Prediction) (o : Observation)
    (h : p.domain ≠ o.domain) : ¬ Scorable p o :=
  fun hs => h hs.1

/-- R8.  A scoring step over a set of predictions and the observations it was
given has, for every prediction, an observation in its own domain. -/
def Measurable (ps : List Prediction) (os : List Observation) : Prop :=
  ∀ p ∈ ps, ∃ o ∈ os, Scorable p o

instance (ps : List Prediction) (os : List Observation) : Decidable (Measurable ps os) := by
  unfold Measurable
  infer_instance

theorem foreign_domain_observations_not_measurable (ps : List Prediction)
    (os : List Observation) (p : Prediction) (hp : p ∈ ps)
    (hos : ∀ o ∈ os, o.domain ≠ p.domain) : ¬ Measurable ps os := by
  intro h
  obtain ⟨o, ho, hs⟩ := h p hp
  exact hos o ho hs.1.symm

/-! ### Control: run 25e24

Tokens 1, 2 are the pattern-done tokens (gauntlet occurrence 0,
world-is-hypergraph occurrence 19); tokens 11..16 are the six mission-hole
tokens measured at revision `547b191`. -/

def run25e24Predictions : List Prediction :=
  [⟨1, .patternLearning⟩, ⟨2, .patternLearning⟩]

def run25e24Measurements : List Observation :=
  [⟨11, .missionAccounting⟩, ⟨12, .missionAccounting⟩, ⟨13, .missionAccounting⟩,
   ⟨14, .missionAccounting⟩, ⟨15, .missionAccounting⟩, ⟨16, .missionAccounting⟩]

theorem run25e24_not_measurable : ¬ Measurable run25e24Predictions run25e24Measurements := by
  decide

/-- Holding the trials `:observation-missing` is the only valid reading of that
step: no pairing of those predictions and measurements is scorable. -/
theorem run25e24_no_scorable_pair :
    ∀ p ∈ run25e24Predictions, ∀ o ∈ run25e24Measurements, ¬ Scorable p o := by
  decide

/-- Pattern-domain measurements of the same tokens would be measurable. -/
theorem run25e24_pattern_measurements_measurable :
    Measurable run25e24Predictions [⟨1, .patternLearning⟩, ⟨2, .patternLearning⟩] := by
  decide

end DarkTower.WarMachine.AdmissionInputs
