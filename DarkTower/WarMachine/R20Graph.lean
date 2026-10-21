import DarkTower.WarMachine.PolicyFreeEnergy
import DarkTower.WarMachine.CTauClassPreference

/-!
# R20 wiring from the publications

Selection emits the E and G used in the policy prior and its observation
model's predicted class probabilities. Post-observation inference emits F
defined from its frozen-policy tick inputs by H1, not a free score.
See S2-authority-ledger.md, "Settlement from the publications" (2026-10-21).

Habit row → selection's E is NOT declared: no cited publication supplies a map
from class-grain habit counts to policy-indexed E. Class-preference risk →
selection's G is deferred to H3 (G = risk + ambiguity).

Preference is at the class grain because the existing risk row consumes CTau's
class distribution. R15StrategicTarget.tacticalPreference pulls this C back
along the focus-dependent classification; it is not a predicted distribution.
Wiring checks artifact identity, not normalization, exact inference, positive
likelihoods or support: those are separate mathematical properties of a run.
-/

namespace DarkTower.WarMachine.R20Graph
noncomputable section

/-- The nine rows are unchanged. -/
inductive Node
  | precision | evidence | habit | classPreference
  | strategicFocus | liveness | independence | jointAction | cost
  deriving DecidableEq, Repr, Fintype

inductive Producer
  | node (node : Node)
  | selection
  | postObservationInference
  deriving DecidableEq, Repr

abbrev RunId := Nat

structure HabitPrior (Policy : Type) where
  value : Policy → ℝ
  producer : Producer
  runId : RunId

structure PredictedClassDistribution where
  value : CTauClassPreference.Distribution
  producer : Producer
  runId : RunId

/-- C over classes, distinct from predicted probabilities over those classes. -/
structure Preference where
  value : CTauClassPreference.Distribution
  producer : Producer
  runId : RunId

structure PolicyExpectedFreeEnergy (Policy : Type) where
  value : Policy → ℝ
  producer : Producer
  runId : RunId

/-- Finite state/tick inputs; no independently editable F value. -/
structure PolicyFreeEnergy (Policy : Type) where
  stateCount : Nat
  ticks : Nat
  q : Policy → Fin ticks → Fin stateCount → ℝ
  prior : Policy → Fin ticks → Fin stateCount → ℝ
  likelihood : Policy → Fin ticks → Fin stateCount → ℝ
  producer : Producer
  runId : RunId

def PolicyFreeEnergy.value {Policy : Type} (f : PolicyFreeEnergy Policy) : Policy → ℝ :=
  DarkTower.WarMachine.PolicyFreeEnergy.policyFreeEnergy f.q f.prior f.likelihood

structure PolicyTemperature where
  value : ℝ
  producer : Producer
  runId : RunId

inductive QuantityKind
  | habitPrior | preference | predictedClassDistribution | policyExpectedFreeEnergy
  | policyFreeEnergy
  deriving DecidableEq, Repr

inductive Endpoint
  | row (node : Node)
  | selection
  | postObservationInference
  deriving DecidableEq, Repr

inductive Edge
  /-- Parr B.7 :12636-12646; Friston eq.2.7 :660-685: the same E
  enters the selection prior and posterior inference. -/
  | selectionToPrecisionHabit
  /-- Friston eq.2.7 :660-685 and eq.2.6 :600-620: the same evaluated
  G enters both policy beliefs. -/
  | selectionToPrecisionG
  /-- Friston :1604-1609, :780; Parr B.4 :12560, :12631-12634:
  state inference after observations produces per-policy F. -/
  | inferenceToPrecisionF
  /-- Parr :10430-10433, :5282-5284: higher levels set C; Friston
  eq.2.6 :600-620 uses U = ln P(o), not predicted probabilities. -/
  | strategicFocusToClassPreference
  /-- Friston eq.2.6 :600-620: predicted outcomes are A times the
  policy-conditioned states, from selection's observation model. -/
  | selectionToClassPreference
  deriving DecidableEq, Repr, Fintype

def Edge.source : Edge → Endpoint
  | .selectionToPrecisionHabit | .selectionToPrecisionG | .selectionToClassPreference =>
    .selection
  | .inferenceToPrecisionF => .postObservationInference
  | .strategicFocusToClassPreference => .row .strategicFocus

def Edge.target : Edge → Node
  | .selectionToPrecisionHabit | .selectionToPrecisionG | .inferenceToPrecisionF => .precision
  | .strategicFocusToClassPreference | .selectionToClassPreference => .classPreference

def Edge.quantity : Edge → QuantityKind
  | .selectionToPrecisionHabit => .habitPrior
  | .selectionToPrecisionG => .policyExpectedFreeEnergy
  | .inferenceToPrecisionF => .policyFreeEnergy
  | .strategicFocusToClassPreference => .preference
  | .selectionToClassPreference => .predictedClassDistribution

structure Ports (Policy : Type) where
  runId : RunId
  selectionHabit : HabitPrior Policy
  precisionHabit : HabitPrior Policy
  selectionG : PolicyExpectedFreeEnergy Policy
  precisionG : PolicyExpectedFreeEnergy Policy
  inferenceF : PolicyFreeEnergy Policy
  precisionF : PolicyFreeEnergy Policy
  strategicPreference : Preference
  classPreference : Preference
  selectionPredicted : PredictedClassDistribution
  classPredicted : PredictedClassDistribution
  precisionBeta : PolicyTemperature

/-- Each consumer receives the producer's entire artifact from this run. -/
structure Wired {Policy : Type} {Row : Node → Type}
    (records : (n : Node) → Option (Row n)) (ports : Ports Policy) : Prop where
  present : ∀ n, n = .strategicFocus ∨ n = .classPreference ∨ n = .precision → records n ≠ none
  habitProducer : ports.selectionHabit.producer = .selection
  habitRun : ports.selectionHabit.runId = ports.runId
  habitRead : ports.precisionHabit = ports.selectionHabit
  gProducer : ports.selectionG.producer = .selection
  gRun : ports.selectionG.runId = ports.runId
  gRead : ports.precisionG = ports.selectionG
  fProducer : ports.inferenceF.producer = .postObservationInference
  fRun : ports.inferenceF.runId = ports.runId
  fRead : ports.precisionF = ports.inferenceF
  preferenceProducer : ports.strategicPreference.producer = .node .strategicFocus
  preferenceRun : ports.strategicPreference.runId = ports.runId
  preferenceRead : ports.classPreference = ports.strategicPreference
  predictedProducer : ports.selectionPredicted.producer = .selection
  predictedRun : ports.selectionPredicted.runId = ports.runId
  predictedRead : ports.classPredicted = ports.selectionPredicted
  betaProducer : ports.precisionBeta.producer = .node .precision
  betaRun : ports.precisionBeta.runId = ports.runId

/-- K1: class risk is not the producer of the policy G used by precision. -/
theorem k1_class_G_not_wired {Policy : Type} {Row : Node → Type}
    (records : (n : Node) → Option (Row n)) (ports : Ports Policy)
    (wrong : ports.precisionG.producer = .node .classPreference) : ¬ Wired records ports := by
  intro h
  rw [h.gRead, h.gProducer] at wrong
  contradiction

/-- K2: selection's G cannot be substituted from another run/menu. -/
theorem k2_other_run_G_not_wired {Policy : Type} {Row : Node → Type}
    (records : (n : Node) → Option (Row n)) (ports : Ports Policy)
    (_producer : ports.precisionG.producer = .selection)
    (wrong : ports.precisionG.runId ≠ ports.runId) : ¬ Wired records ports := by
  intro h
  exact wrong ((congrArg PolicyExpectedFreeEnergy.runId h.gRead).trans h.gRun)

/-- K3: a selection-time F is not post-observation inference's F. -/
theorem k3_selection_F_not_wired {Policy : Type} {Row : Node → Type}
    (records : (n : Node) → Option (Row n)) (ports : Ports Policy)
    (wrong : ports.precisionF.producer = .selection) : ¬ Wired records ports := by
  intro h
  rw [h.fRead, h.fProducer] at wrong
  contradiction

abbrev TestPolicy := PrecisionFromObservation.TwoPolicy

/-- One tick, one state, normalized exact posterior and likelihood one. -/
def exampleF (run : RunId) : PolicyFreeEnergy TestPolicy :=
  ⟨1, 1, fun _ _ _ => 1, fun _ _ _ => 1, fun _ _ _ => 1, .postObservationInference, run⟩

def examplePrediction (run : RunId) : PredictedClassDistribution :=
  ⟨CTauClassPreference.waitingPreference, .selection, run⟩

def goodPorts (run : RunId) : Ports TestPolicy :=
  { runId := run
    selectionHabit := ⟨fun _ => 1 / 2, .selection, run⟩
    precisionHabit := ⟨fun _ => 1 / 2, .selection, run⟩
    selectionG := ⟨fun _ => 0, .selection, run⟩
    precisionG := ⟨fun _ => 0, .selection, run⟩
    inferenceF := exampleF run, precisionF := exampleF run
    strategicPreference := ⟨CTauClassPreference.waitingPreference, .node .strategicFocus, run⟩
    classPreference := ⟨CTauClassPreference.waitingPreference, .node .strategicFocus, run⟩
    selectionPredicted := examplePrediction run, classPredicted := examplePrediction run
    precisionBeta := ⟨1, .node .precision, run⟩ }

abbrev TestRow : Node → Type := fun _ => Unit
def goodRecords : (n : Node) → Option (TestRow n) := fun _ => some ()

/-- K4: all five edges can be wired simultaneously, with actual tick inputs. -/
theorem k4_goodPorts_wired (run : RunId) : Wired goodRecords (goodPorts run) := by
  constructor
  · intro n _; simp [goodRecords]
  all_goals rfl

/- K6 negative type control (checked separately):
example : Preference := examplePrediction 0
Lean: Type mismatch
  examplePrediction 0
has type
  PredictedClassDistribution
but is expected to have type
  Preference
-/

#print axioms k1_class_G_not_wired
#print axioms k2_other_run_G_not_wired
#print axioms k3_selection_F_not_wired
#print axioms k4_goodPorts_wired

end
end DarkTower.WarMachine.R20Graph
