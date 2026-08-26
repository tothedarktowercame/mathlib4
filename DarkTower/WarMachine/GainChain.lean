/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# War Machine realised-outcome gain chain

This file is an outline behavioural model of the R8 realised-outcome fold
through the R14 selection gain.  It names the requirements which rule out the
composition-and-liveness defect introduced on 2026-07-08; it is not a semantics
of the War Machine.

`DarkTower/WMPipelineExample.lean` describes the same gamma consumer, but a
different feed and incident.  Its hungry port was the expected-dG feed severed
by classical-fold retirement on 2026-07-05 and repaired by the escrow feed that
day.  This module concerns gamma's realised leg: the 2026-07-08 substitution of
the broad realised-outcome producer by a grounded producer whose data
precondition was not discharged.

The model rules out that composition-and-liveness class of defect.  It does
not decide whether `bound - inhabited` is the right measurement, inspect the
current substrate for deposits, or catch the wrong-corpus error of 2026-08-26.
It is an outline: there is no emitter, Clojure contract, or mutation suite.
Nothing here repairs the running system; excursion slices 4 and 5 remain the
operator's decision and are outside this file.

`ProducerSelection` includes a tick in addition to the suggested fields.  The
extra field is necessary to state family 1: selection, outcome and fold must
literally share one threaded tick.
-/

namespace DarkTower.WarMachine.GainChain

structure Tick where
  id : Nat
  deriving DecidableEq, Repr

structure Mission where
  id : String
  deriving DecidableEq, Repr

inductive Producer where
  | coverageDelta
  | groundedDial
  deriving DecidableEq, Repr

/-- Typed absence keeps an unsupported mission distinct from missing data. -/
inductive Measurement where
  | measured (r : Int)
  | domainMismatch
  | noData
  deriving DecidableEq, Repr

inductive CorpusLoadPolicy where
  | strict
  | degrading
  deriving DecidableEq, Repr

structure RealizedOutcome where
  tick : Tick
  mission : Mission
  producer : Producer
  expectedLeg : Int
  realizedLeg : Measurement
  durable : Bool
  deriving DecidableEq, Repr

structure FoldOccurrence where
  tick : Tick
  consumed : Option RealizedOutcome
  gainMoved : Bool
  deriving DecidableEq, Repr

structure ProducerSelection where
  tick : Tick
  mission : Mission
  producer : Producer
  inDomain : Mission → Bool
  preconditionDischarged : Bool

/-!
The four requirement-family predicates instantiated by this module are kept
generic enough to move later to `DarkTower/WarMachine/Requirements.lean`.

Reserved but not instantiated here:

* family 3: `selfContainedRecord`;
* family 6: `separatedPowers`;
* family 7: `pinnedExit`.
-/

/-- Family 1: selection, enactment outcome and fold retain one identity. -/
def threadedIdentity (occurrence : FoldOccurrence)
    (selection : ProducerSelection) : Prop :=
  ∃ outcome, occurrence.consumed = some outcome ∧
    selection.tick = outcome.tick ∧ occurrence.tick = outcome.tick ∧
    selection.mission = outcome.mission ∧ selection.producer = outcome.producer

/-- Family 2: an occurrence records a value or a typed absence. -/
def inhabitedHandle (occurrence : FoldOccurrence) : Prop :=
  ∃ outcome, occurrence.consumed = some outcome

/-- Family 4: folding may consume only an outcome already durably written. -/
def durableBeforeFold (occurrence : FoldOccurrence) : Prop :=
  ∀ outcome, occurrence.consumed = some outcome → outcome.durable = true

/-- Family 5: the selected mission belongs to the producer's declared domain. -/
def declaredDomain (selection : ProducerSelection) : Prop :=
  selection.inDomain selection.mission = true

/-- A selected live producer must have its data precondition discharged. -/
def dischargedPrecondition (selection : ProducerSelection) : Prop :=
  selection.preconditionDischarged = true

/-- A producer substitution may preserve or enlarge, but never shrink, domain. -/
def domainNotNarrowed (old new : ProducerSelection) : Prop :=
  ∀ mission, old.inDomain mission = true → new.inDomain mission = true

/-- The R8-to-R14 chain property. -/
def gainChainSound (occurrence : FoldOccurrence)
    (selection : ProducerSelection) : Prop :=
  threadedIdentity occurrence selection ∧
  inhabitedHandle occurrence ∧
  durableBeforeFold occurrence ∧
  declaredDomain selection ∧
  dischargedPrecondition selection

def bayesianMission : Mission := ⟨"M-bayesian-structure-learning"⟩
def groundedMission : Mission := ⟨"M-grounded-dial-example"⟩

def coverageSelection : ProducerSelection where
  tick := ⟨8⟩
  mission := bayesianMission
  producer := .coverageDelta
  inDomain := fun _ => true
  preconditionDischarged := true

def groundedSelection : ProducerSelection where
  tick := ⟨8⟩
  mission := bayesianMission
  producer := .groundedDial
  inDomain := fun mission => decide (mission = groundedMission)
  preconditionDischarged := true

/-- The 2026-07-08 substitution loses an enacted mission from the domain. -/
theorem substitution_2026_07_08_narrows_domain_is_refused :
    ¬ domainNotNarrowed coverageSelection groundedSelection := by
  intro h
  have := h bayesianMission (by rfl)
  simp [groundedSelection, bayesianMission, groundedMission] at this

/-- "INERT UNTIL DATA" is not a discharged live-producer precondition. -/
theorem inert_until_data_is_not_a_discharged_precondition
    (occurrence : FoldOccurrence) (selection : ProducerSelection)
    (h : selection.preconditionDischarged = false) :
    ¬ gainChainSound occurrence selection := by
  intro hs
  have ht := hs.2.2.2.2
  simp [dischargedPrecondition, h] at ht

def swallowedStrictOccurrence : FoldOccurrence where
  tick := ⟨9⟩
  consumed := none
  gainMoved := false

/-- A strict-load rejection swallowed by enactment is a silent success only
operationally; the model refuses it because the fold has no handle. -/
theorem strict_load_swallowed_gives_a_silent_success :
    CorpusLoadPolicy.strict = .strict ∧
      ¬ inhabitedHandle swallowedStrictOccurrence := by
  constructor
  · rfl
  · simp [inhabitedHandle, swallowedStrictOccurrence]

def clockSplitOutcome : RealizedOutcome where
  tick := ⟨100⟩
  mission := bayesianMission
  producer := .coverageDelta
  expectedLeg := -2
  realizedLeg := .measured (-5)
  durable := true

def clockSplitOccurrence : FoldOccurrence where
  tick := ⟨101⟩
  consumed := some clockSplitOutcome
  gainMoved := true

def clockSplitSelection : ProducerSelection where
  tick := ⟨100⟩
  mission := bayesianMission
  producer := .coverageDelta
  inDomain := fun _ => true
  preconditionDischarged := true

/-- Reading the outcome and scheduled-run clocks separately breaks identity. -/
theorem two_clocks_break_threaded_identity :
    ¬ gainChainSound clockSplitOccurrence clockSplitSelection := by
  intro h
  rcases h.1 with ⟨outcome, hout, _, htick, _, _⟩
  simp [clockSplitOccurrence] at hout
  subst outcome
  simp [clockSplitOccurrence, clockSplitOutcome] at htick

def domainMismatchOutcome : RealizedOutcome where
  tick := ⟨12⟩
  mission := bayesianMission
  producer := .groundedDial
  expectedLeg := -2
  realizedLeg := .domainMismatch
  durable := true

def domainMismatchOccurrence : FoldOccurrence where
  tick := ⟨12⟩
  consumed := some domainMismatchOutcome
  gainMoved := false

/-- A typed out-of-domain report is evidence; `none` would be silence. -/
theorem domain_mismatch_is_a_record_not_a_silence :
    inhabitedHandle domainMismatchOccurrence := by
  exact ⟨domainMismatchOutcome, rfl⟩

def soundOutcome : RealizedOutcome where
  tick := ⟨5⟩
  mission := bayesianMission
  producer := .coverageDelta
  expectedLeg := -2
  realizedLeg := .measured (-5)
  durable := true

def soundOccurrence : FoldOccurrence where
  tick := ⟨5⟩
  consumed := some soundOutcome
  gainMoved := true

def soundSelection : ProducerSelection where
  tick := ⟨5⟩
  mission := bayesianMission
  producer := .coverageDelta
  inDomain := fun _ => true
  preconditionDischarged := true

/-- The contract is inhabited, modelled on the 88 pre-substitution outcomes. -/
theorem gain_chain_sound_nonvacuous :
    gainChainSound soundOccurrence soundSelection := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨soundOutcome, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨soundOutcome, rfl⟩
  · intro outcome h
    simp [soundOccurrence] at h
    subst outcome
    rfl
  · rfl
  · rfl

#print axioms substitution_2026_07_08_narrows_domain_is_refused
#print axioms inert_until_data_is_not_a_discharged_precondition
#print axioms strict_load_swallowed_gives_a_silent_success
#print axioms two_clocks_break_threaded_identity
#print axioms domain_mismatch_is_a_record_not_a_silence
#print axioms gain_chain_sound_nonvacuous

end DarkTower.WarMachine.GainChain
