import DarkTower.WarMachine.PrecisionFromObservation
import DarkTower.WarMachine.CTauClassPreference

/-!
# R20 certificate wiring

The R20 rows are checked separately.  This module names the small graph that
connects the quantities shared by those rows and retains their run and producer
identity.  The wiring is a sidecar to the dependent row family: it does not
change any `NodeRecord` constructor.
-/

namespace DarkTower.WarMachine.R20Graph

noncomputable section

/-- The nine rows of the R20 certificate. -/
inductive Node
  | precision | evidence | habit | classPreference
  | strategicFocus | liveness | independence | jointAction | cost
  deriving DecidableEq, Repr, Fintype

/-- A producer is either one of the nine rows or the scorer outside R20. -/
inductive Producer
  | node (node : Node)
  | policyFreeEnergyScorer
  deriving DecidableEq, Repr

abbrev RunId := Nat

/-- The policy habit prior E, with its producing row and run. -/
structure HabitPrior (Policy : Type) where
  value : Policy → ℝ
  producer : Producer
  runId : RunId

/-- A predicted class distribution, distinct from preferences and scalar risk. -/
structure PredictedClassDistribution where
  value : CTauClassPreference.Distribution
  producer : Producer
  runId : RunId

/-- Policy expected free energy G.  It is deliberately not definitionally F. -/
structure PolicyExpectedFreeEnergy (Policy : Type) where
  value : Policy → ℝ
  producer : Producer
  runId : RunId

/-- Policy free energy F.  It is deliberately not definitionally G. -/
structure PolicyFreeEnergy (Policy : Type) where
  value : Policy → ℝ
  producer : Producer
  runId : RunId

/-- Policy temperature/precision beta emitted by the precision row. -/
structure PolicyTemperature where
  value : ℝ
  producer : Producer
  runId : RunId

/-- The semantic kind carried by a declared edge. -/
inductive QuantityKind
  | habitPrior | predictedClassDistribution | policyExpectedFreeEnergy
  | policyFreeEnergy
  deriving DecidableEq, Repr

/-- The endpoint of an edge, including the external F scorer. -/
inductive Endpoint
  | row (node : Node)
  | policyFreeEnergyScorer
  deriving DecidableEq, Repr

/--
The conservative graph declared by PL1.  Every constructor corresponds to one
read/write join in `PL1-lean-graph.edn`; no module-dependency-only edge is added.
-/
inductive Edge
  /-- Inferred from the prose role of `(TAG classHabitPrior)` in
  `R15HabitPrior.lean` and the E field of `(TAG TickRecord)` in
  `PrecisionFromObservation.lean`. -/
  | habitPriorToPrecision
  /-- Inferred from `(TAG inducedClassDistribution)` in
  `R15StrategicTarget.lean`. -/
  | strategicFocusToClassPreference
  /-- Inferred from `(TAG classPreference)`, `(TAG classRisk)` in
  `CTauClassPreference.lean`, and `(TAG ClassPreferenceConforms)` in
  `R20Certificate.lean`. -/
  | classPreferenceToPrecision
  /-- PL1 marks the producer missing outside R20; the consumer field is exposed
  by `(TAG TickRecord)` in `PrecisionFromObservation.lean`. -/
  | policyFreeEnergyScorerToPrecision
  deriving DecidableEq, Repr, Fintype

def Edge.source : Edge → Endpoint
  | .habitPriorToPrecision => .row .habit
  | .strategicFocusToClassPreference => .row .strategicFocus
  | .classPreferenceToPrecision => .row .classPreference
  | .policyFreeEnergyScorerToPrecision => .policyFreeEnergyScorer

def Edge.target : Edge → Node
  | .habitPriorToPrecision => .precision
  | .strategicFocusToClassPreference => .classPreference
  | .classPreferenceToPrecision => .precision
  | .policyFreeEnergyScorerToPrecision => .precision

def Edge.quantity : Edge → QuantityKind
  | .habitPriorToPrecision => .habitPrior
  | .strategicFocusToClassPreference => .predictedClassDistribution
  | .classPreferenceToPrecision => .policyExpectedFreeEnergy
  | .policyFreeEnergyScorerToPrecision => .policyFreeEnergy

/-- Sidecar ports for the quantities the current row records do not brand. -/
structure Ports (Policy : Type) where
  runId : RunId
  habitEmitted : HabitPrior Policy
  precisionHabit : HabitPrior Policy
  strategicPredicted : PredictedClassDistribution
  classPredicted : PredictedClassDistribution
  classG : PolicyExpectedFreeEnergy Policy
  precisionG : PolicyExpectedFreeEnergy Policy
  scorerF : PolicyFreeEnergy Policy
  precisionF : PolicyFreeEnergy Policy
  precisionBeta : PolicyTemperature

/-- Every declared row endpoint is present, and every consumer port is the
producer's exact artifact from this run.  `Row` keeps this module independent
of the concrete `NodeRecord` family and avoids an import cycle. -/
def Wired {Policy : Type} {Row : Node → Type}
    (records : (n : Node) → Option (Row n)) (ports : Ports Policy) : Prop :=
  (∀ n, n = .habit ∨ n = .strategicFocus ∨ n = .classPreference ∨ n = .precision →
    records n ≠ none) ∧
  ports.habitEmitted.producer = .node .habit ∧
  ports.habitEmitted.runId = ports.runId ∧
  ports.precisionHabit = ports.habitEmitted ∧
  ports.strategicPredicted.producer = .node .strategicFocus ∧
  ports.strategicPredicted.runId = ports.runId ∧
  ports.classPredicted = ports.strategicPredicted ∧
  ports.classG.producer = .node .classPreference ∧
  ports.classG.runId = ports.runId ∧
  ports.precisionG = ports.classG ∧
  ports.scorerF.producer = .policyFreeEnergyScorer ∧
  ports.scorerF.runId = ports.runId ∧
  ports.precisionF = ports.scorerF ∧
  ports.precisionBeta.producer = .node .precision ∧
  ports.precisionBeta.runId = ports.runId

abbrev TestPolicy := PrecisionFromObservation.TwoPolicy

def zeroE (run : RunId) : HabitPrior TestPolicy :=
  ⟨fun _ => 0, .node .habit, run⟩

def zeroPrediction (run : RunId) : PredictedClassDistribution :=
  ⟨fun _ => 0, .node .strategicFocus, run⟩

def zeroG (run : RunId) : PolicyExpectedFreeEnergy TestPolicy :=
  ⟨fun _ => 0, .node .classPreference, run⟩

def zeroF (run : RunId) : PolicyFreeEnergy TestPolicy :=
  ⟨fun _ => 0, .policyFreeEnergyScorer, run⟩

def goodPorts (run : RunId) : Ports TestPolicy :=
  { runId := run
    habitEmitted := zeroE run, precisionHabit := zeroE run
    strategicPredicted := zeroPrediction run, classPredicted := zeroPrediction run
    classG := zeroG run, precisionG := zeroG run
    scorerF := zeroF run, precisionF := zeroF run
    precisionBeta := ⟨1, .node .precision, run⟩ }

abbrev TestRow : Node → Type := fun _ => Unit

def goodRecords : (n : Node) → Option (TestRow n) := fun _ => some ()

/-- C4: the wiring predicate has a concrete positive inhabitant. -/
theorem c4_goodPorts_wired (run : RunId) : Wired goodRecords (goodPorts run) := by
  classical
  constructor
  · intro n hn
    simp [goodRecords]
  · simp [goodPorts, zeroE, zeroPrediction, zeroG, zeroF]

def wrongProducerPorts : Ports TestPolicy :=
  { goodPorts 7 with
    precisionF := ⟨fun _ => 0, .node .evidence, 7⟩ }

/-- C1: an F of the right semantic type but from another producer is rejected. -/
theorem c1_wrong_producer_not_wired : ¬ Wired goodRecords wrongProducerPorts := by
  classical
  simp [Wired, wrongProducerPorts, goodPorts, zeroF]

def wrongRunPorts : Ports TestPolicy :=
  { goodPorts 7 with
    precisionF := zeroF 8 }

/-- C2: an F from the scorer but from another run is rejected. -/
theorem c2_wrong_run_not_wired : ¬ Wired goodRecords wrongRunPorts := by
  classical
  simp [Wired, wrongRunPorts, goodPorts, zeroF]

/-- C5 (wiring form): an unrelated row-wise proposition supplies no wiring;
the explicit wrong-producer sidecar remains rejected. -/
theorem c5_rows_property_does_not_supply_wiring (RowsCertified : Prop)
    (_ : RowsCertified) : ¬ Wired goodRecords wrongProducerPorts :=
  c1_wrong_producer_not_wired

/- C3: this does not typecheck; `PolicyExpectedFreeEnergy` cannot fill an F port.

example : PolicyFreeEnergy TestPolicy := zeroG 0

Lean reports:
  application type mismatch
    zeroG 0
  argument has type
    PolicyExpectedFreeEnergy TestPolicy : Type
  but is expected to have type
    PolicyFreeEnergy TestPolicy : Type
-/

end
end DarkTower.WarMachine.R20Graph
