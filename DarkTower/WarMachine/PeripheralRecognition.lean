import Mathlib.Data.Finset.Basic

/-!
# Peripheral recognition depends on operational evidence

This is the first concrete-state sensitivity witness for PROOF-2b.  A
peripheral role is derived from an operational witness, never from the name of
the product.  The deliberately coarse token carrier retains only connection,
send, and receive facts.  It consequently aliases an inhabitable REPL with an
untyped pipe and cannot support a correct classifier for both.

The source exemplar is
`futon2/resources/wm/peripheral-recognition-sensitivity-sample-v1.edn`.
Numerical expected-free-energy rankings are intentionally deferred: this file
first establishes recognition, collision, and operational separation.
-/

namespace DarkTower.WarMachine.PeripheralRecognition

/-- Evidence about how an interface behaves.  The first three fields are the
facts retained by the coarse token interpretation; the remaining fields are
the distinctions supplied by the operational interpretation. -/
structure OperationalWitness where
  connected : Bool
  canSend : Bool
  canReceive : Bool
  boundedActionVocabulary : Bool
  entryCondition : Bool
  exitCondition : Bool
  transportContract : Bool
  typedEvents : Bool
  embodiment : Bool
  auditableTrace : Bool
  inhabitationFeedback : Bool
  deriving DecidableEq, Repr

structure NamedInstance where
  name : String
  witness : OperationalWitness
  deriving DecidableEq, Repr

/-- A full execution peripheral supplies an envelope, lifecycle, transport,
and embodiment. -/
def IsExecutionPeripheral (w : OperationalWitness) : Prop :=
  w.boundedActionVocabulary = true ∧
  w.entryCondition = true ∧
  w.exitCondition = true ∧
  w.transportContract = true ∧
  w.embodiment = true

instance (w : OperationalWitness) : Decidable (IsExecutionPeripheral w) := by
  unfold IsExecutionPeripheral
  infer_instance

/-- A transport peripheral supplies a bounded vocabulary and typed transport;
it can be composed with a separate embodiment. -/
def IsTransportPeripheral (w : OperationalWitness) : Prop :=
  w.boundedActionVocabulary = true ∧
  w.transportContract = true ∧
  w.typedEvents = true

instance (w : OperationalWitness) : Decidable (IsTransportPeripheral w) := by
  unfold IsTransportPeripheral
  infer_instance

inductive PeripheralRole
  | execution
  | transport
  deriving DecidableEq, Repr

def recognise (w : OperationalWitness) : Option PeripheralRole :=
  if decide (IsExecutionPeripheral w) then some .execution
  else if decide (IsTransportPeripheral w) then some .transport
  else none

def recogniseNamed (x : NamedInstance) : Option PeripheralRole :=
  recognise x.witness

/-- Names are annotations, not recognition evidence. -/
theorem recognition_name_invariant (x : NamedInstance) (newName : String) :
    recogniseNamed { x with name := newName } = recogniseNamed x := by
  rfl

def codexReplWitness : OperationalWitness where
  connected := true
  canSend := true
  canReceive := true
  boundedActionVocabulary := true
  entryCondition := true
  exitCondition := true
  transportContract := true
  typedEvents := true
  embodiment := true
  auditableTrace := true
  inhabitationFeedback := true

def claudeReplWitness : OperationalWitness := codexReplWitness

def ircAdapterWitness : OperationalWitness where
  connected := true
  canSend := true
  canReceive := true
  boundedActionVocabulary := true
  entryCondition := false
  exitCondition := false
  transportContract := true
  typedEvents := true
  embodiment := false
  auditableTrace := true
  inhabitationFeedback := false

def untypedPipeWitness : OperationalWitness where
  connected := true
  canSend := true
  canReceive := true
  boundedActionVocabulary := false
  entryCondition := false
  exitCondition := false
  transportContract := false
  typedEvents := false
  embodiment := false
  auditableTrace := false
  inhabitationFeedback := false

theorem codex_repl_is_execution_peripheral :
    IsExecutionPeripheral codexReplWitness := by
  decide

theorem claude_repl_is_execution_peripheral :
    IsExecutionPeripheral claudeReplWitness := by
  decide

theorem irc_adapter_is_transport_peripheral :
    IsTransportPeripheral ircAdapterWitness := by
  decide

theorem examples_are_recognised :
    recognise codexReplWitness = some .execution ∧
    recognise claudeReplWitness = some .execution ∧
    recognise ircAdapterWitness = some .transport := by
  decide

theorem untyped_pipe_is_not_execution_peripheral :
    ¬ IsExecutionPeripheral untypedPipeWitness := by
  decide

inductive FactToken
  | connected
  | canSend
  | canReceive
  deriving DecidableEq, Repr

abbrev CoarseState := Finset FactToken

/-- The intentionally inadequate carrier sees connectivity but not lifecycle,
typing, embodiment, audit, or feedback. -/
def coarseEncode (w : OperationalWitness) : CoarseState :=
  (if w.connected then { .connected } else ∅) ∪
  (if w.canSend then { .canSend } else ∅) ∪
  (if w.canReceive then { .canReceive } else ∅)

/-- The advertised coarse collision. -/
theorem coarse_repl_pipe_collision :
    coarseEncode codexReplWitness = coarseEncode untypedPipeWitness := by
  decide

/-- The operational carrier retains evidence that the coarse carrier erased. -/
theorem operational_repl_pipe_separation :
    codexReplWitness ≠ untypedPipeWitness := by
  decide

/-- No Boolean classifier which sees only the coarse state can accept this
REPL and reject this pipe.  This is stronger than merely displaying equal
encodings: it states the application-level consequence of the collision. -/
theorem no_correct_coarse_classifier (classify : CoarseState → Bool) :
    ¬ (classify (coarseEncode codexReplWitness) = true ∧
       classify (coarseEncode untypedPipeWitness) = false) := by
  rw [coarse_repl_pipe_collision]
  simp

#print axioms recognition_name_invariant
#print axioms examples_are_recognised
#print axioms coarse_repl_pipe_collision
#print axioms operational_repl_pipe_separation
#print axioms no_correct_coarse_classifier

end DarkTower.WarMachine.PeripheralRecognition
