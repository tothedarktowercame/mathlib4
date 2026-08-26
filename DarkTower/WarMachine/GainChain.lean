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

Reviewed 2026-08-26 (claude-13) with three requirements added, each of which
the first draft named but did not constrain:

* `typedAbsence` — the realised leg must tell an out-of-domain mission apart
  from an unmeasured one.  The three-way `Measurement` split was exhibited but
  never required, so `noData` and `domainMismatch` were still interchangeable,
  which is the `fold_realized.clj:163` defect the split exists to rule out.
* `gainAdvances` — R14's end of the chain.  Without it the property held of a
  fold that read a durable outcome and left the gain pinned at 1.0, i.e. of the
  observed failure.
* `loadYieldsOutcome` / `foldOf` — the corpus-load policy now decides whether
  the fold has a handle, so `strict` and `degrading` are distinguishable.  It
  was previously a declared type used only in a conjunct proved by `rfl`.

`foldCompliant` is separated from `gainChainSound` for the same reason: an
out-of-domain mission cannot move the gain, and must still leave a record.
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

-- translated from APMCycleMachine.lean:108 validDispatch
/-- Family 1: selection, enactment outcome and fold retain one identity. -/
def threadedIdentity (occurrence : FoldOccurrence)
    (selection : ProducerSelection) : Prop :=
  ∃ outcome, occurrence.consumed = some outcome ∧
    selection.tick = outcome.tick ∧ occurrence.tick = outcome.tick ∧
    selection.mission = outcome.mission ∧ selection.producer = outcome.producer

-- translated from APMCycleMachine.lean:234 validStudentTerminalCandidate
--   (the non-empty-digest clause)
/-- Family 2: an occurrence records a value or a typed absence. -/
def inhabitedHandle (occurrence : FoldOccurrence) : Prop :=
  ∃ outcome, occurrence.consumed = some outcome

-- translated from APMCycleMachine.lean:239 persistedBeforeReceipt
/-- Family 4: folding may consume only an outcome already durably written. -/
def durableBeforeFold (occurrence : FoldOccurrence) : Prop :=
  ∀ outcome, occurrence.consumed = some outcome → outcome.durable = true

-- translated from APMCycleMachine.lean:326 validControllerMemoryUse
/-- Family 5: the selected mission belongs to the producer's declared domain. -/
def declaredDomain (selection : ProducerSelection) : Prop :=
  selection.inDomain selection.mission = true

/-- A selected live producer must have its data precondition discharged. -/
def dischargedPrecondition (selection : ProducerSelection) : Prop :=
  selection.preconditionDischarged = true

/-- A producer substitution may preserve or enlarge, but never shrink, domain. -/
def domainNotNarrowed (old new : ProducerSelection) : Prop :=
  ∀ mission, old.inDomain mission = true → new.inDomain mission = true

/-- Family 5, measurement side: the realised leg tells an out-of-domain
mission apart from an in-domain one with nothing measured yet.  A mismatch is
not missing data, and `noData` is not a licence to report a mismatch.  This is
the requirement behind `fold_realized.clj:163`, which returns one bare `nil`
for both conditions. -/
def typedAbsence (occurrence : FoldOccurrence)
    (selection : ProducerSelection) : Prop :=
  ∀ outcome, occurrence.consumed = some outcome →
    (outcome.realizedLeg = Measurement.domainMismatch ↔
      selection.inDomain outcome.mission = false)

/-- R14's end of the chain.  Without this clause the model would accept a fold
that reads a durable outcome and still leaves `:selection-gain` pinned at 1.0,
which is the state observed in all 65 occurrences since 2026-07-08. -/
def gainAdvances (occurrence : FoldOccurrence) : Prop :=
  occurrence.gainMoved = true

/-- The R8-to-R14 chain property: the gain moved, and moved lawfully. -/
def gainChainSound (occurrence : FoldOccurrence)
    (selection : ProducerSelection) : Prop :=
  threadedIdentity occurrence selection ∧
  inhabitedHandle occurrence ∧
  durableBeforeFold occurrence ∧
  typedAbsence occurrence selection ∧
  declaredDomain selection ∧
  dischargedPrecondition selection ∧
  gainAdvances occurrence

/-- What a fold owes even when the gain cannot move: a durable, threaded,
typed record.  An out-of-domain mission cannot satisfy `gainChainSound` — there
is no measurement to fold — but it must still satisfy this.  Reporting an
absence is compliant; skipping the step is not. -/
def foldCompliant (occurrence : FoldOccurrence)
    (selection : ProducerSelection) : Prop :=
  threadedIdentity occurrence selection ∧
  inhabitedHandle occurrence ∧
  durableBeforeFold occurrence ∧
  typedAbsence occurrence selection ∧
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
  obtain ⟨-, -, -, -, -, hd, -⟩ := hs
  simp [dischargedPrecondition, h] at hd

/-- Whether a corpus load hands the fold anything.  `strict` refuses the whole
corpus when any single deposit is rejected (`actuator_a3.clj:149`); `degrading`
serves the deposits that validated (`fold_escrow/load-deposits`). -/
def loadYieldsOutcome : CorpusLoadPolicy → Nat → Bool
  | .strict, rejected => rejected == 0
  | .degrading, _ => true

/-- The fold occurrence a corpus load produces.  When the load yields nothing
the exception is swallowed at `enact.clj:255`, so the occurrence is not an
error: it is a tick with no handle and a gain that did not move. -/
def foldOf (policy : CorpusLoadPolicy) (rejected : Nat)
    (outcome : RealizedOutcome) : FoldOccurrence :=
  if loadYieldsOutcome policy rejected then
    { tick := outcome.tick, consumed := some outcome, gainMoved := true }
  else
    { tick := outcome.tick, consumed := none, gainMoved := false }

def pendingOutcome : RealizedOutcome where
  tick := ⟨9⟩
  mission := bayesianMission
  producer := .coverageDelta
  expectedLeg := -2
  realizedLeg := .measured (-5)
  durable := true

/-- One rejected deposit anywhere in the corpus, under `strict`, leaves the
fold with no handle — while the same corpus under `degrading` still yields one.
The policy, not the data, decides whether the loop can see its own outcome.
This is excursion slice 4, and the two policies are distinguishable here. -/
theorem strict_load_swallowed_gives_a_silent_success :
    ¬ inhabitedHandle (foldOf .strict 1 pendingOutcome) ∧
      inhabitedHandle (foldOf .degrading 1 pendingOutcome) := by
  constructor
  · simp [inhabitedHandle, foldOf, loadYieldsOutcome]
  · exact ⟨pendingOutcome, by simp [foldOf, loadYieldsOutcome]⟩

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

def domainMismatchSelection : ProducerSelection where
  tick := ⟨12⟩
  mission := bayesianMission
  producer := .groundedDial
  inDomain := fun mission => decide (mission = groundedMission)
  preconditionDischarged := true

/-- A typed out-of-domain report is evidence; `none` would be silence.  The
fold is compliant and the gain correctly does not move — the two verdicts the
2026-07-08 chain collapsed into one silence. -/
theorem domain_mismatch_is_a_record_not_a_silence :
    foldCompliant domainMismatchOccurrence domainMismatchSelection ∧
      ¬ gainChainSound domainMismatchOccurrence domainMismatchSelection := by
  constructor
  · refine ⟨⟨domainMismatchOutcome, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨domainMismatchOutcome, rfl⟩, ?_, ?_, rfl⟩
    · intro outcome h
      simp [domainMismatchOccurrence] at h
      subst outcome
      rfl
    · intro outcome h
      simp [domainMismatchOccurrence] at h
      subst outcome
      simp [domainMismatchOutcome, domainMismatchSelection, bayesianMission,
        groundedMission]
  · intro hs
    obtain ⟨-, -, -, -, hdom, -, -⟩ := hs
    simp [declaredDomain, domainMismatchSelection, bayesianMission,
      groundedMission] at hdom

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨soundOutcome, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨soundOutcome, rfl⟩
  · intro outcome h
    simp [soundOccurrence] at h
    subst outcome
    rfl
  · intro outcome h
    simp [soundOccurrence] at h
    subst outcome
    simp [soundOutcome, soundSelection]
  · rfl
  · rfl
  · rfl

#print axioms substitution_2026_07_08_narrows_domain_is_refused
#print axioms inert_until_data_is_not_a_discharged_precondition
#print axioms strict_load_swallowed_gives_a_silent_success
#print axioms two_clocks_break_threaded_identity
#print axioms domain_mismatch_is_a_record_not_a_silence
#print axioms gain_chain_sound_nonvacuous

end DarkTower.WarMachine.GainChain
