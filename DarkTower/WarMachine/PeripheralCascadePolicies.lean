import DarkTower.WarMachine.PeripheralSensitivityG

/-!
# Peripheral pattern cascades interpreted as repair policies

This file supplies the graph-to-generative-model bridge for the peripheral
sensitivity witness.  Policies are occurrence graphs with separate support,
meet, and generative-precedence relations.  Their operational outcomes are
compiled from graph facts rather than attached as caller-provided labels.

Two warranted policies are compared for one reload-safe repair:

* direct Drawbridge/REPL repair;
* IRC-mediated ground-control repair, which adds a typed transport hop.

Both complete the repair while preserving state and typed auditability.  The
second has higher time and token cost in this pinned fixture.  A
restart-through-untyped-pipe graph remains a negative control: it is
structurally well formed but fails the warranted peripheral-policy predicate.
-/

namespace DarkTower.WarMachine.PeripheralCascadePolicies

open PinnedRepairWant PeripheralSensitivityG

/-- The pattern labels used by the fixture.  Every constructor names a real
file in `futon3/library/peripherals`. -/
inductive Pattern
  | readExistingSeam
  | constrainedEnvelope
  | canonicalTypedEvent
  | pilotGroundControl
  | progressHeartbeat
  | hotReload
  | splitTransportEmbodiment
  deriving DecidableEq, Fintype, Repr

structure Occurrence where
  id : Nat
  pattern : Pattern
  deriving DecidableEq, Repr

abbrev Edge := Occurrence × Occurrence

/-- The meet occurrence is the recognisable unit shared by the left and right
co-requirements. -/
structure Meet where
  left : Occurrence
  right : Occurrence
  shared : Occurrence
  deriving DecidableEq, Repr

structure Cascade where
  units : Finset Occurrence
  support : Finset Edge
  meets : Finset Meet
  precedes : Finset Edge

def Cascade.WellFormed (c : Cascade) : Prop :=
  c.units.Nonempty ∧
  (∀ e ∈ c.support, e.1 ∈ c.units ∧ e.2 ∈ c.units) ∧
  (∀ m ∈ c.meets, m.left ∈ c.units ∧ m.right ∈ c.units ∧ m.shared ∈ c.units) ∧
  (∀ e ∈ c.precedes, e.1 ∈ c.units ∧ e.2 ∈ c.units ∧ e.1.id < e.2.id)

instance (c : Cascade) : Decidable c.WellFormed := by
  unfold Cascade.WellFormed
  infer_instance

def Cascade.Contains (c : Cascade) (p : Pattern) : Prop :=
  ∃ u ∈ c.units, u.pattern = p

instance (c : Cascade) (p : Pattern) : Decidable (c.Contains p) := by
  unfold Cascade.Contains
  infer_instance

def Cascade.Orders (c : Cascade) (before after : Pattern) : Prop :=
  ∃ a ∈ c.units, ∃ b ∈ c.units,
    (a, b) ∈ c.precedes ∧ a.pattern = before ∧ b.pattern = after

instance (c : Cascade) (a b : Pattern) : Decidable (c.Orders a b) := by
  unfold Cascade.Orders
  infer_instance

/-- Minimum construction evidence for this repair problem.  It is deliberately
separate from structural well-formedness: a tidy graph is not thereby an
admissible policy. -/
def Cascade.WarrantedRepair (c : Cascade) : Prop :=
  c.Contains .readExistingSeam ∧
  c.Contains .canonicalTypedEvent ∧
  c.Contains .hotReload ∧
  c.Orders .readExistingSeam .hotReload ∧
  c.Orders .canonicalTypedEvent .hotReload

instance (c : Cascade) : Decidable c.WarrantedRepair := by
  unfold Cascade.WarrantedRepair
  infer_instance

def Cascade.AdmissibleRepair (c : Cascade) : Prop :=
  c.WellFormed ∧ c.WarrantedRepair

instance (c : Cascade) : Decidable c.AdmissibleRepair := by
  unfold Cascade.AdmissibleRepair
  infer_instance

def seam : Occurrence := ⟨0, .readExistingSeam⟩
def envelope : Occurrence := ⟨1, .constrainedEnvelope⟩
def event : Occurrence := ⟨2, .canonicalTypedEvent⟩
def ground : Occurrence := ⟨3, .pilotGroundControl⟩
def heartbeat : Occurrence := ⟨4, .progressHeartbeat⟩
def reload : Occurrence := ⟨5, .hotReload⟩

/-- The six-unit cascade from the v2 exemplar. -/
def directReplCascade : Cascade where
  units := {seam, envelope, event, ground, heartbeat, reload}
  support := {(seam, envelope), (seam, reload), (event, ground),
    (event, heartbeat), (ground, envelope), (heartbeat, ground), (reload, ground)}
  meets := {⟨ground, heartbeat, event⟩, ⟨envelope, reload, seam⟩}
  precedes := {(seam, envelope), (seam, event), (envelope, ground),
    (event, ground), (event, heartbeat), (ground, reload), (heartbeat, reload),
    (seam, reload), (event, reload)}

theorem direct_repl_admissible : directReplCascade.AdmissibleRepair := by
  native_decide

def ircSeam : Occurrence := ⟨0, .readExistingSeam⟩
def ircEnvelope : Occurrence := ⟨1, .constrainedEnvelope⟩
def ircSplit : Occurrence := ⟨2, .splitTransportEmbodiment⟩
def ircEvent : Occurrence := ⟨3, .canonicalTypedEvent⟩
def ircGround : Occurrence := ⟨4, .pilotGroundControl⟩
def ircHeartbeat : Occurrence := ⟨5, .progressHeartbeat⟩
def ircReload : Occurrence := ⟨6, .hotReload⟩

/-- The IRC adapter is a transport peripheral composed with the ground-control
embodiment; Drawbridge remains the state-preserving repair seam. -/
def ircMediatedCascade : Cascade where
  units := {ircSeam, ircEnvelope, ircSplit, ircEvent, ircGround, ircHeartbeat, ircReload}
  support := {(ircSeam, ircEnvelope), (ircSeam, ircReload),
    (ircSplit, ircEvent), (ircEvent, ircGround), (ircEvent, ircHeartbeat),
    (ircGround, ircEnvelope), (ircHeartbeat, ircGround), (ircReload, ircGround)}
  meets := {⟨ircGround, ircHeartbeat, ircEvent⟩,
    ⟨ircEnvelope, ircReload, ircSeam⟩}
  precedes := {(ircSeam, ircEnvelope), (ircSeam, ircSplit),
    (ircSplit, ircEvent), (ircEnvelope, ircGround), (ircEvent, ircGround),
    (ircEvent, ircHeartbeat), (ircGround, ircReload), (ircHeartbeat, ircReload),
    (ircSeam, ircReload), (ircEvent, ircReload)}

theorem irc_mediated_admissible : ircMediatedCascade.AdmissibleRepair := by
  native_decide

/-- Operational interpretation.  Completion, preservation, auditability, and
resource bands are computed from graph structure. -/
def interpretSuccess (c : Cascade) : OperationalOutcome where
  completed := decide (c.Contains .hotReload)
  statePreserved := decide (c.Orders .readExistingSeam .hotReload)
  typedAndAuditable := decide (c.Orders .canonicalTypedEvent .hotReload)
  elapsed := if decide (c.Contains .splitTransportEmbodiment) then .high else .low
  modelTokens := if decide (c.Contains .splitTransportEmbodiment) then .high else .low

def interpretFallback (c : Cascade) : OperationalOutcome :=
  { interpretSuccess c with completed := false }

theorem direct_success_interpretation :
    interpretSuccess directReplCascade = replRepair := by
  native_decide

theorem direct_fallback_interpretation :
    interpretFallback directReplCascade = replFallback := by
  native_decide

def ircSuccess : OperationalOutcome where
  completed := true
  statePreserved := true
  typedAndAuditable := true
  elapsed := .high
  modelTokens := .high

def ircFallback : OperationalOutcome where
  completed := false
  statePreserved := true
  typedAndAuditable := true
  elapsed := .high
  modelTokens := .high

theorem irc_success_interpretation :
    interpretSuccess ircMediatedCascade = ircSuccess := by
  native_decide

theorem irc_fallback_interpretation :
    interpretFallback ircMediatedCascade = ircFallback := by
  native_decide

theorem ircSuccess_utility : utility pinnedWant ircSuccess = 9 := by
  norm_num [utility, pinnedWant, ircSuccess, boolReward, lowCostReward]

theorem ircFallback_utility : utility pinnedWant ircFallback = 5 := by
  norm_num [utility, pinnedWant, ircFallback, boolReward, lowCostReward]

theorem direct_success_preferred :
    preference pinnedWant ircSuccess < preference pinnedWant replRepair := by
  unfold preference
  apply (div_lt_div_iff_of_pos_right (normalizer_pos pinnedWant)).2
  apply Real.exp_lt_exp.mpr
  rw [ircSuccess_utility, replRepair_utility]
  norm_num

theorem direct_fallback_preferred :
    preference pinnedWant ircFallback < preference pinnedWant replFallback := by
  unfold preference
  apply (div_lt_div_iff_of_pos_right (normalizer_pos pinnedWant)).2
  apply Real.exp_lt_exp.mpr
  rw [ircFallback_utility, replFallback_utility]
  norm_num

theorem cascade_deterministic_operational_ranking :
    deterministicG (interpretSuccess directReplCascade) <
      deterministicG (interpretSuccess ircMediatedCascade) := by
  rw [direct_success_interpretation, irc_success_interpretation]
  exact surprisal_lt_of_preference_gt direct_success_preferred

theorem cascade_deterministic_coarse_tie :
    coarseDeterministicG (interpretSuccess directReplCascade) =
      coarseDeterministicG (interpretSuccess ircMediatedCascade) := by
  rw [direct_success_interpretation, irc_success_interpretation]
  rfl

theorem cascade_stochastic_operational_ranking (sharedAmbiguity : ℝ) :
    stochasticG (interpretSuccess directReplCascade)
        (interpretFallback directReplCascade) sharedAmbiguity <
      stochasticG (interpretSuccess ircMediatedCascade)
        (interpretFallback ircMediatedCascade) sharedAmbiguity := by
  rw [direct_success_interpretation, direct_fallback_interpretation,
    irc_success_interpretation, irc_fallback_interpretation]
  have hs := surprisal_lt_of_preference_gt direct_success_preferred
  have hf := surprisal_lt_of_preference_gt direct_fallback_preferred
  unfold stochasticG
  nlinarith

theorem cascade_stochastic_coarse_tie (sharedAmbiguity : ℝ) :
    coarseStochasticG (interpretSuccess directReplCascade)
        (interpretFallback directReplCascade) sharedAmbiguity =
      coarseStochasticG (interpretSuccess ircMediatedCascade)
        (interpretFallback ircMediatedCascade) sharedAmbiguity := by
  rw [direct_success_interpretation, direct_fallback_interpretation,
    irc_success_interpretation, irc_fallback_interpretation]
  rfl

/-- A bare restart may be a graph-shaped action plan, but for this reload-safe
problem it lacks the seam and typed-event construction evidence required of a
peripheral cascade. -/
def restartUntypedControl : Cascade where
  units := {reload}
  support := ∅
  meets := ∅
  precedes := ∅

theorem restart_control_well_formed : restartUntypedControl.WellFormed := by
  native_decide

theorem restart_control_not_admissible :
    ¬ restartUntypedControl.AdmissibleRepair := by
  native_decide

#print axioms direct_repl_admissible
#print axioms irc_mediated_admissible
#print axioms cascade_deterministic_operational_ranking
#print axioms cascade_deterministic_coarse_tie
#print axioms cascade_stochastic_operational_ranking
#print axioms cascade_stochastic_coarse_tie
#print axioms restart_control_not_admissible

end DarkTower.WarMachine.PeripheralCascadePolicies
