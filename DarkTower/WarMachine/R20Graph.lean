import DarkTower.WarMachine.PolicyFreeEnergy
import DarkTower.WarMachine.PolicyExpectedFreeEnergy
import DarkTower.WarMachine.CTauClassPreference

/-!
# R20 wiring from the publications

Selection emits the E and G used in the policy prior and its observation
model's predicted class probabilities. Post-observation inference emits F
defined from its frozen-policy tick inputs by H1, not a free score.
See S2-authority-ledger.md, "Settlement from the publications" (2026-10-21).

The habit row supplies selection's E (`habitToSelectionHabit`): its counts are
per policy (`R15TemporalHierarchy`), and E is their normalisation, which
`R20Certificate.RowsReadPorts` checks and `R20HabitPrior` uses. Class preference supplies
the tick schedule C to selection; selection computes H3's risk plus ambiguity.

Preference is at the class grain because the existing risk row consumes CTau's
class distribution. R15StrategicTarget.tacticalPreference pulls this C back
along the focus-dependent classification; it is not a predicted distribution.
G artifacts carry stochasticity proofs for A, s and C. Wiring checks their
identity and provenance, not exact inference, positive likelihoods or support.
Unsupported preferences remain infinite G; the real precision consumer must
agree after embedding its value in EReal, never by dropping infinity.
-/

namespace DarkTower.WarMachine.R20Graph
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The certificate's ten rows. -/
inductive Node
  | precision | evidence | habit | classPreference
  | strategicFocus | liveness | independence | jointAction | cost | interoception
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

/-- Each policy's risk on the interoceptive modality. -/
structure InteroceptiveRisk (Policy : Type) where
  value : Policy → EReal
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

/-- Per-tick preferences, distinct from a single preference and predictions. -/
structure PreferenceSchedule (ticks : Nat) where
  value : Fin ticks → CTauClassPreference.Distribution
  producer : Producer
  runId : RunId

structure PolicyExpectedFreeEnergy (Policy : Type) where
  stateCount : Nat
  ticks : Nat
  A : CTauClassPreference.EndingClass → Fin stateCount → ℝ
  s : Policy → Fin ticks → Fin stateCount → ℝ
  schedule : PreferenceSchedule ticks
  aNonneg : ∀ o x, 0 ≤ A o x
  aNormalized : ∀ x, ∑ o, A o x = 1
  sNonneg : ∀ π t x, 0 ≤ s π t x
  sNormalized : ∀ π t, ∑ x, s π t x = 1
  cProbability : ∀ t, CTauClassPreference.ProbabilityDistribution (schedule.value t)
  producer : Producer
  runId : RunId

def PolicyExpectedFreeEnergy.value {Policy : Type} (g : PolicyExpectedFreeEnergy Policy) :
    Policy → EReal :=
  DarkTower.WarMachine.PolicyExpectedFreeEnergy.policyExpectedFreeEnergy g.A g.s
    (fun t o => (g.schedule.value t o : ℝ))

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
  | habitPrior | preference | preferenceSchedule | predictedClassDistribution | policyExpectedFreeEnergy
  | policyFreeEnergy | interoceptiveRisk
  deriving DecidableEq, Repr

inductive Endpoint
  | row (node : Node)
  | selection
  | postObservationInference
  deriving DecidableEq, Repr

inductive Edge
  /-- Friston et al. 2016, friston2016.txt:436-442, :675-678: E is the mean of
  Dir(e), counts of each policy; Parr, Pezzulo and Friston 2022,
  parr2022.txt:10724-10727: cached results of which policies were successful
  "can be incorporated as a prior value of policies". -/
  | habitToSelectionHabit
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
  /-- Friston eq.2.6, friston2017.txt:600-620, U_τ = ln P(o_τ);
  S2 settlement row 3: class preference supplies C, selection computes G. -/
  | classPreferenceToSelectionG
  /-- Parr, Pezzulo and Friston 2022, parr2022.txt:6537-6540: separate outcome
  modalities have separate A tensors, and C (:13769-13770) is given per
  modality; pp. 215-216: viable ranges are priors over interoceptive
  observations. With independent modalities the risk of the joint outcome is
  the sum of each modality's risk, so selection adds this row's risk to the
  class risk (`selectionScore`). -/
  | interoceptionToSelectionG
  deriving DecidableEq, Repr, Fintype

def Edge.source : Edge → Endpoint
  | .habitToSelectionHabit => .row .habit
  | .selectionToPrecisionHabit | .selectionToPrecisionG | .selectionToClassPreference =>
    .selection
  | .inferenceToPrecisionF => .postObservationInference
  | .strategicFocusToClassPreference => .row .strategicFocus
  | .classPreferenceToSelectionG => .row .classPreference
  | .interoceptionToSelectionG => .row .interoception

def Edge.target : Edge → Endpoint
  | .habitToSelectionHabit => .selection
  | .selectionToPrecisionHabit | .selectionToPrecisionG | .inferenceToPrecisionF => .row .precision
  | .strategicFocusToClassPreference | .selectionToClassPreference => .row .classPreference
  | .classPreferenceToSelectionG | .interoceptionToSelectionG => .selection

def Edge.quantity : Edge → QuantityKind
  | .habitToSelectionHabit => .habitPrior
  | .selectionToPrecisionHabit => .habitPrior
  | .selectionToPrecisionG => .policyExpectedFreeEnergy
  | .inferenceToPrecisionF => .policyFreeEnergy
  | .strategicFocusToClassPreference => .preference
  | .selectionToClassPreference => .predictedClassDistribution
  | .classPreferenceToSelectionG => .preferenceSchedule
  | .interoceptionToSelectionG => .interoceptiveRisk

structure Ports (Policy : Type) where
  runId : RunId
  habitRowE : HabitPrior Policy
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
  interoceptionRisk : InteroceptiveRisk Policy
  selectionInteroceptionRisk : InteroceptiveRisk Policy

/-- Each consumer receives the producer's entire artifact from this run. -/
structure Wired {Policy : Type} {Row : Node → Type}
    (records : (n : Node) → Option (Row n)) (ports : Ports Policy) : Prop where
  present : ∀ n, n = .strategicFocus ∨ n = .classPreference ∨ n = .precision ∨ n = .habit ∨
    n = .interoception → records n ≠ none
  habitRowProducer : ports.habitRowE.producer = .node .habit
  habitRowRun : ports.habitRowE.runId = ports.runId
  habitIntoSelection : ports.selectionHabit.value = ports.habitRowE.value
  habitProducer : ports.selectionHabit.producer = .selection
  habitRun : ports.selectionHabit.runId = ports.runId
  habitRead : ports.precisionHabit = ports.selectionHabit
  gProducer : ports.selectionG.producer = .selection
  gRun : ports.selectionG.runId = ports.runId
  gRead : ports.precisionG = ports.selectionG
  scheduleProducer : ports.selectionG.schedule.producer = .node .classPreference
  scheduleRun : ports.selectionG.schedule.runId = ports.runId
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
  interoceptionProducer : ports.interoceptionRisk.producer = .node .interoception
  interoceptionRun : ports.interoceptionRisk.runId = ports.runId
  interoceptionRead : ports.selectionInteroceptionRisk = ports.interoceptionRisk

/-- Each policy's expected free energy over both outcome modalities: the class
modality's G (risk plus ambiguity, Friston eq. 2.6) plus the interoceptive
modality's risk. Expected free energy of independent modalities is the sum of
each modality's term. The interoceptive term is risk only, which is its whole
G when readings are observed without noise (a deterministic interoceptive A,
so zero ambiguity); likelihood precision for that modality is not modelled
(`R20Interoception`). Selection scores policies by this, and the precision row
reads this same G (`R20Certificate.RowsReadPorts`). -/
def selectionScore {Policy : Type} (ports : Ports Policy) (π : Policy) : EReal :=
  ports.selectionG.value π + ports.selectionInteroceptionRisk.value π

/-- K15: an interoceptive risk produced by selection itself is not wired. -/
theorem k15_interoception_from_selection_not_wired {Policy : Type} {Row : Node → Type}
    (records : (n : Node) → Option (Row n)) (ports : Ports Policy)
    (wrong : ports.selectionInteroceptionRisk.producer = .selection) : ¬ Wired records ports := by
  intro h
  rw [h.interoceptionRead, h.interoceptionProducer] at wrong
  contradiction

/-- K16: selection scoring with another run's interoceptive risk is not wired. -/
theorem k16_interoception_other_run_not_wired {Policy : Type} {Row : Node → Type}
    (records : (n : Node) → Option (Row n)) (ports : Ports Policy)
    (wrong : ports.selectionInteroceptionRisk.runId ≠ ports.runId) : ¬ Wired records ports :=
  fun h => wrong ((congrArg InteroceptiveRisk.runId h.interoceptionRead).trans h.interoceptionRun)

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

/-- K13: an E in selection that is not the habit row's E is not wired. -/
theorem k13_selection_E_not_habit_not_wired {Policy : Type} {Row : Node → Type}
    (records : (n : Node) → Option (Row n)) (ports : Ports Policy)
    (wrong : ports.selectionHabit.value ≠ ports.habitRowE.value) : ¬ Wired records ports :=
  fun h => wrong h.habitIntoSelection

/-- K14: a habit E produced anywhere but the habit row is not wired. -/
theorem k14_habit_E_from_selection_not_wired {Policy : Type} {Row : Node → Type}
    (records : (n : Node) → Option (Row n)) (ports : Ports Policy)
    (wrong : ports.habitRowE.producer = .selection) : ¬ Wired records ports := by
  intro h
  rw [h.habitRowProducer] at wrong
  contradiction

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

/-- A normalized deterministic column emitting focused, with one state/tick. -/
def focusedG (run : RunId) (C : CTauClassPreference.Distribution)
    (hc : CTauClassPreference.ProbabilityDistribution C) : PolicyExpectedFreeEnergy TestPolicy where
  stateCount := 1
  ticks := 1
  A := fun o _ => if o = .focused then 1 else 0
  s := fun _ _ _ => 1
  schedule := ⟨fun _ => C, .node .classPreference, run⟩
  aNonneg := by intros; split_ifs <;> norm_num
  aNormalized := by intro x; simp
  sNonneg := by intros; norm_num
  sNormalized := by intros; simp
  cProbability := fun _ => hc
  producer := .selection
  runId := run

def waitingG (run : RunId) : PolicyExpectedFreeEnergy TestPolicy :=
  focusedG run (CTauClassPreference.classPreference 2 1)
    (CTauClassPreference.classPreference_probability 2 1 (by omega) (by omega) (by omega))

def goodPorts (run : RunId) : Ports TestPolicy :=
  { runId := run
    habitRowE := ⟨fun _ => 1 / 2, .node .habit, run⟩
    selectionHabit := ⟨fun _ => 1 / 2, .selection, run⟩
    precisionHabit := ⟨fun _ => 1 / 2, .selection, run⟩
    selectionG := waitingG run
    precisionG := waitingG run
    inferenceF := exampleF run, precisionF := exampleF run
    strategicPreference := ⟨CTauClassPreference.waitingPreference, .node .strategicFocus, run⟩
    classPreference := ⟨CTauClassPreference.waitingPreference, .node .strategicFocus, run⟩
    selectionPredicted := examplePrediction run, classPredicted := examplePrediction run
    precisionBeta := ⟨1, .node .precision, run⟩
    interoceptionRisk := ⟨fun _ => 0, .node .interoception, run⟩
    selectionInteroceptionRisk := ⟨fun _ => 0, .node .interoception, run⟩ }

abbrev TestRow : Node → Type := fun _ => Unit
def goodRecords : (n : Node) → Option (TestRow n) := fun _ => some ()

/-- K4: all eight edges can be wired simultaneously, with actual tick inputs.
This is wiring, not certification of a finite-G precision row. -/
theorem k4_goodPorts_wired (run : RunId) : Wired goodRecords (goodPorts run) := by
  constructor
  · intro n _; simp [goodRecords]
  all_goals rfl

/-- K7: predictions produced by selection cannot supply the C schedule. -/
theorem k7_selection_schedule_not_wired {Policy : Type} {Row : Node → Type}
    (records : (n : Node) → Option (Row n)) (ports : Ports Policy)
    (wrong : ports.selectionG.schedule.producer = .selection) : ¬ Wired records ports := by
  intro h
  rw [h.scheduleProducer] at wrong
  contradiction

/-- K8: valid inputs still yield top for an off-waiting deterministic outcome. -/
theorem k8_waiting_G_top (run : RunId) (π : TestPolicy) :
    (waitingG run).value π = ⊤ := by
  simp only [PolicyExpectedFreeEnergy.value,
    DarkTower.WarMachine.PolicyExpectedFreeEnergy.policyExpectedFreeEnergy,
    waitingG, focusedG, CTauClassPreference.classPreference]
  simp only [show (1 : Nat) ≠ 2 by decide, if_false,
    Finset.univ_unique, Finset.sum_singleton]
  apply DarkTower.WarMachine.PolicyExpectedFreeEnergy.before_horizon_top
  refine ⟨.focused, by decide, ?_⟩
  norm_num [DarkTower.WarMachine.PolicyExpectedFreeEnergy.predictedOutcome]

def terminalG (run : RunId) : PolicyExpectedFreeEnergy TestPolicy :=
  focusedG run (CTauClassPreference.classPreference 1 1)
    (CTauClassPreference.classPreference_probability 1 1 (by omega) (by omega) (by omega))

def focusedC : CTauClassPreference.Distribution := fun o => if o = .focused then 1 else 0

theorem focusedC_probability : CTauClassPreference.ProbabilityDistribution focusedC := by
  constructor
  · intro o; simp only [focusedC]; split_ifs <;> norm_num
  · simp [CTauClassPreference.totalMass, focusedC]

def alternativeG (run : RunId) : PolicyExpectedFreeEnergy TestPolicy :=
  focusedG run focusedC focusedC_probability

private theorem focusedG_value (run : RunId) (C : CTauClassPreference.Distribution)
    (hc : CTauClassPreference.ProbabilityDistribution C) (positive : 0 < C .focused)
    (π : TestPolicy) : (focusedG run C hc).value π = (-Real.log (C .focused : ℝ) : ℝ) := by
  have nonzero : C .focused ≠ 0 := ne_of_gt positive
  have indicator (x : CTauClassPreference.EndingClass) :
      (0 < if x = .focused then (1 : ℝ) else 0) ↔ x = .focused := by
    split_ifs <;> simp_all
  have enum : (Finset.univ : Finset CTauClassPreference.EndingClass) =
      {.focused, .related, .unrelated, .stopTheLine, .notYetEvaluated} := by decide
  simp [PolicyExpectedFreeEnergy.value, focusedG,
    DarkTower.WarMachine.PolicyExpectedFreeEnergy.policyExpectedFreeEnergy,
    DarkTower.WarMachine.PolicyExpectedFreeEnergy.tickG,
    DarkTower.WarMachine.PolicyExpectedFreeEnergy.predictedOutcome,
    DarkTower.WarMachine.PolicyExpectedFreeEnergy.ambiguity,
    DarkTower.WarMachine.PolicyExpectedFreeEnergy.columnEntropy,
    DarkTower.WarMachine.PolicyExpectedFreeEnergy.risk,
    DarkTower.WarMachine.PolicyExpectedFreeEnergy.Unsupported,
    DarkTower.WarMachine.PolicyExpectedFreeEnergy.finiteRisk, indicator, nonzero, enum]

/-- K9: terminal C yields a finite G; a different normalized C changes it. -/
theorem k9_terminal_G_finite_and_sensitive (run : RunId) (π : TestPolicy) :
    (terminalG run).value π = (-Real.log (55 / 100 : ℝ) : ℝ) ∧
    (terminalG run).value π ≠ ⊤ ∧ (terminalG run).value π ≠ ⊥ ∧
    (alternativeG run).value π = 0 ∧
    (terminalG run).value π ≠ (alternativeG run).value π := by
  have terminal : (terminalG run).value π = (-Real.log (55 / 100 : ℝ) : ℝ) := by
    unfold terminalG
    rw [focusedG_value run _ _ (by norm_num [CTauClassPreference.classPreference,
      CTauClassPreference.terminalPreference]) π]
    norm_num [CTauClassPreference.classPreference, CTauClassPreference.terminalPreference]
  have alternative : (alternativeG run).value π = 0 := by
    unfold alternativeG
    rw [focusedG_value run _ _ (by norm_num [focusedC]) π]
    simp [focusedC]
  have positive : 0 < -Real.log (55 / 100 : ℝ) := by
    have := Real.log_neg (by norm_num : (0 : ℝ) < 55 / 100)
      (by norm_num : (55 / 100 : ℝ) < 1)
    linarith
  refine ⟨terminal, ?_, ?_, alternative, ?_⟩
  · rw [terminal]; exact EReal.coe_ne_top _
  · rw [terminal]; exact EReal.coe_ne_bot _
  · rw [terminal, alternative]
    exact ne_of_gt (by exact_mod_cast positive)

/-- K10: no normalization field can be supplied for a missing/zero column. -/
theorem k10_zero_column_not_admissible :
    ¬ ∀ _x : Fin 1, (∑ _o : CTauClassPreference.EndingClass, (0 : ℝ)) = 1 := by
  intro h
  have := h 0
  norm_num at this

/-- K10, port form: every admissible G port has no all-zero column of A, so the
H3 zero-column case (G = 0, the best score) cannot reach selection. -/
theorem k10_port_has_no_zero_column {Policy : Type} (g : PolicyExpectedFreeEnergy Policy)
    (x : Fin g.stateCount) : ¬ ∀ o, g.A o x = 0 := by
  intro h
  have := g.aNormalized x
  simp [h] at this

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
#print axioms k7_selection_schedule_not_wired
#print axioms k8_waiting_G_top
#print axioms k9_terminal_G_finite_and_sensitive
#print axioms k10_zero_column_not_admissible
#print axioms k10_port_has_no_zero_column

end
end DarkTower.WarMachine.R20Graph
