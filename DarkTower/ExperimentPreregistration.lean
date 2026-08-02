/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

/-!
# Preregistration: what an experiment commits to before it runs

This file holds the *declaration* half of the pre-go-live gate. It says what an
experiment is claiming, what it will vary, and what settings it will apply --- and
derives, from that declaration alone, the list of obligations the experiment must
discharge before it may start.

`ExperimentalDesign` consumes this. It supplies evidence, decides whether each
obligation is discharged, and owns the launch gate. The split matters because the two
halves change for different reasons: obligations accrue as we learn new ways an
experiment can be vacuous, while the machinery that discharges them stays fixed.

The obligations here are not a taxonomy invented for symmetry. Each corresponds to a
way a real run turned out to be incapable of supporting its claim:

* a search along an axis whose score was flat across every adjacent pair;
* a "rarer than chance" claim with no no-selection arm to be rarer *than*;
* a setting whose implementation silently did nothing, so the run answered a
  different question than the one asked;
* a cost estimate that omitted a sampling multiplier;
* a teardown that depended on the run succeeding.
-/

namespace ExperimentPreregistration

universe u

/-! ## Settings must declare what they do -/

/--
An observable consequence, stated over whatever the run emits.

`Trace` is abstract on purpose: it is the run's own output, and the point is that a
consequence must be checkable *from that output* rather than from the exit status of
the process that produced it. Every silent failure worth guarding against reported
success and emitted a trace that disagreed.
-/
structure Observable (Trace : Type u) where
  /-- What is claimed, for reporting. -/
  name : String
  /-- The claim as a predicate on the trace. -/
  holds : Trace → Prop
  /-- The claim must be checkable, not merely stateable. -/
  check : Trace → Bool
  /-- The check must be *sound*: it never passes a trace that violates the claim.

  This is the field that rules out the check which cannot distinguish "the thing is
  absent" from "I was unable to ask" --- such a test passes traces it should reject,
  so it cannot inhabit this field. -/
  check_sound : ∀ t, check t = true → holds t

/--
A setting, together with the consequence that setting it must have.

There is no constructor omitting the observable. Declaring a flag without declaring
what it does is therefore a type error rather than an oversight, which is the
structural form of the failure where a flag reached a billing run without ever taking
effect.
-/
structure Flag (Trace : Type u) where
  name : String
  observable : Observable Trace

/-- A flag is honoured by a trace when its observable holds there. -/
def Flag.honoured {Trace : Type u} (f : Flag Trace) (t : Trace) : Prop :=
  f.observable.holds t

/-- Soundness lifts the runtime check to the claim. -/
theorem Flag.honoured_of_check {Trace : Type u} (f : Flag Trace) (t : Trace)
    (h : f.observable.check t = true) : f.honoured t :=
  f.observable.check_sound t h

/-! ## Axes -/

/--
A parameter axis: the levels a search can actually occupy, and the score at each.

`levels` is the *reachable* set under the declared operators, not what the
representation could express. A value present in the type and absent from the mutation
operator is in the representation and not in the experiment.
-/
structure Axis where
  name : String
  levels : List ℝ
  score : ℝ → ℝ

/-- Adjacent level pairs across which the score changes.

Noncomputable because it decides equality of reals: this is the specification, and the
runtime gate evaluates the corresponding test on measured values. -/
noncomputable def Axis.gradientSteps (a : Axis) : Nat :=
  ((a.levels.zip a.levels.tail).filter (fun p => a.score p.1 ≠ a.score p.2)).length

/--
An axis is navigable when some *adjacent* pair carries gradient.

Counting adjacent transitions rather than distinct values is the entire content. A
profile that is zero at every level but one has two distinct values and a single
transition; a local search cannot cross a lone cliff. A check phrased as "the axis is
not constant" passes such a design, and did.
-/
def Axis.Navigable (a : Axis) : Prop := 0 < a.gradientSteps

/-- A constant axis is not navigable: there is nothing to climb. -/
theorem not_navigable_of_constant {a : Axis} (h : ∀ x y, a.score x = a.score y) :
    ¬ a.Navigable := by
  unfold Axis.Navigable Axis.gradientSteps
  simp only [not_lt, Nat.le_zero, List.length_eq_zero_iff]
  apply List.filter_eq_nil_iff.mpr
  intro p _
  simp [h p.1 p.2]

/-- An axis with a single reachable level is not navigable: there are no adjacent
pairs at all. This is the operator-reachability failure --- a dial the search cannot
turn is not a treatment. -/
theorem not_navigable_of_singleton {a : Axis} {x : ℝ} (h : a.levels = [x]) :
    ¬ a.Navigable := by
  unfold Axis.Navigable Axis.gradientSteps
  simp [h]

/-! ## Claims and arms -/

/-- The shape of the claim the run is meant to support. -/
inductive ClaimForm
  /-- "Rarer/commoner than chance", which obliges a no-selection control. -/
  | rarerThanChance
  /-- "These treatments differ", which obliges the arms to be separable. -/
  | comparative
  /-- Description only. -/
  | descriptive
  deriving DecidableEq, Repr

/-- The inferential role of an experimental arm.  Only a positive control
reverses the polarity of its axis obligation: its predicted null must itself be
proved, rather than silently exempting the axis from scrutiny. -/
inductive ArmRole
  | treatment
  | baselineNeutral
  | positiveControl
  deriving DecidableEq, Repr

/-- An arm of the experiment. -/
structure Arm where
  name : String
  /-- Selection disabled, making this arm an empirical null. -/
  neutral : Bool
  /-- The axes this arm's search moves along. -/
  axes : List Axis
  /-- What inferential job this arm performs.  The dependent default preserves
  old declarations while classifying their neutral baselines honestly. -/
  role : ArmRole := if neutral then .baselineNeutral else .treatment

/-! ## The registration, and the obligations it generates -/

/--
What is committed to before running.

Registering does not make an experiment ready. It makes explicit what readiness would
consist of, by generating the obligation list below.
-/
structure Registration (Trace : Type u) where
  name : String
  claim : ClaimForm
  arms : List Arm
  flags : List (Flag Trace)
  /-- Cost from a *measured* rate, including sampling multipliers. An arm with four
  times the seeds and sites costs four times per generation, and an estimate that
  counts only the extra generations is wrong by that factor. -/
  estimatedCost : ℝ
  /-- The ceiling the run may not exceed. -/
  budgetCap : ℝ
  /-- Teardown scheduled independently of the run succeeding. -/
  teardownDeadline : Option ℝ

/-! ## Prospective commitments

The first version of this module was exercised retrospectively.  That exposed three
commitments which cannot be reconstructed honestly after seeing the data: replication
seeds, stop rules, and the interpretation function.  They live in a separate wrapper
so that old post-registrations remain readable while new experiments cannot omit them.
-/

/-- Whether this registration is the first apparatus pilot or a confirmation
of an identified predecessor. -/
inductive RegistrationStage
  | pilot
  | confirmation
  deriving DecidableEq, Repr

/-- A nonempty endpoint name.  Both reproducibility checks and identity-floor
measurements are operational endpoints, not prose caveats. -/
structure NamedEndpoint where
  name : String
  nameNonempty : name ≠ ""

/-- The proof burden generated by the source of run-to-run variation.

Controlled variation owes a reproducibility endpoint: rerunning one unit must
produce the same trace.  Measured variation owes an identity-floor endpoint:
control-vs-control agreement is the yardstick for the treatment effect.  There
is no constructor which merely suppresses either burden. -/
inductive VariationPlan
  | controlled (reproducibilityEndpoint : NamedEndpoint)
  | measured (floorEndpoint : NamedEndpoint)

/-- A replication plan indexed by the experiment's genuine replicate unit.

The constructors route stage obligations structurally.  A pilot cannot carry a
predecessor or a meaningless disjointness proof.  A confirmation cannot omit
its predecessor, predecessor units, current units, or their disjointness proof.
Seeded simulations instantiate `ι := Nat`; non-seedable experiments may use a
problem identifier or another checkable unit type. -/
inductive ReplicationPlan (ι : Type*)
  | pilot
      (pilotUnits : List ι)
      (pilotNonempty : pilotUnits ≠ [])
      (variation : VariationPlan)
  | confirmation
      (predecessor : NamedEndpoint)
      (pilotUnits : List ι)
      (confirmationUnits : List ι)
      (pilotNonempty : pilotUnits ≠ [])
      (confirmationNonempty : confirmationUnits ≠ [])
      (disjoint : pilotUnits.Disjoint confirmationUnits)
      (variation : VariationPlan)

namespace ReplicationPlan

def stage {ι : Type*} : ReplicationPlan ι → RegistrationStage
  | .pilot .. => .pilot
  | .confirmation .. => .confirmation

def predecessor {ι : Type*} : ReplicationPlan ι → Option String
  | .pilot .. => none
  | .confirmation predecessor .. => some predecessor.name

def pilotUnits {ι : Type*} : ReplicationPlan ι → List ι
  | .pilot units .. => units
  | .confirmation _ units .. => units

def confirmationUnits {ι : Type*} : ReplicationPlan ι → List ι
  | .pilot .. => []
  | .confirmation _ _ units .. => units

def variation {ι : Type*} : ReplicationPlan ι → VariationPlan
  | .pilot _ _ variation => variation
  | .confirmation _ _ _ _ _ _ variation => variation

/-- Compatibility constructor for genuinely seeded confirmation studies.  It
still names the predecessor and carries the same nonemptiness/disjointness
proofs; the fixed endpoint records deterministic seeded replay. -/
def seededConfirmation (predecessorName : String) (predecessorNonempty : predecessorName ≠ "")
    (pilotUnits confirmationUnits : List Nat)
    (pilotNonempty : pilotUnits ≠ []) (confirmationNonempty : confirmationUnits ≠ [])
    (disjoint : pilotUnits.Disjoint confirmationUnits) : ReplicationPlan Nat :=
  .confirmation ⟨predecessorName, predecessorNonempty⟩ pilotUnits confirmationUnits
    pilotNonempty confirmationNonempty disjoint
    (.controlled ⟨"seeded-trace-replay", by decide⟩)

end ReplicationPlan

/--
A stopping condition together with an exact executable test.  Requiring an `iff`, rather
than only soundness, prevents a checker which always returns `false` from satisfying the
registration while never stopping a failed run.
-/
structure StopRule (Trace : Type u) where
  name : String
  fires : Trace → Prop
  check : Trace → Bool
  check_iff : ∀ t, check t = true ↔ fires t

/-- A pre-committed total interpretation of every trace the experiment may emit. -/
structure DecisionRule (Trace : Type u) (Outcome : Type*) where
  name : String
  classify : Trace → Outcome

/--
The prospective envelope around a base registration.  Its fields have no defaults:
replication, at least one stop rule, and an interpretation must exist before this value
can be constructed.
-/
structure ProspectiveRegistration (ι : Type*) (Trace : Type u) (Outcome : Type*) where
  base : Registration Trace
  replication : ReplicationPlan ι
  stopRules : List (StopRule Trace)
  stopRulesNonempty : stopRules ≠ []
  decision : DecisionRule Trace Outcome

/-- Every confirmation names at least one current replicate unit. -/
theorem ReplicationPlan.exists_confirmationUnit {ι : Type*}
    (predecessor : NamedEndpoint) (pilotUnits confirmationUnits : List ι)
    (pilotNonempty : pilotUnits ≠ [])
    (confirmationNonempty : confirmationUnits ≠ [])
    (disjoint : pilotUnits.Disjoint confirmationUnits) (variation : VariationPlan) :
    ∃ unit, unit ∈ (ReplicationPlan.confirmation predecessor pilotUnits
      confirmationUnits pilotNonempty confirmationNonempty disjoint variation).confirmationUnits := by
  change ∃ unit, unit ∈ confirmationUnits
  cases h : confirmationUnits with
  | nil => exact (confirmationNonempty h).elim
  | cons unit units => exact ⟨unit, by simp⟩

/-- No predecessor unit can be silently recycled as a confirmation unit. -/
theorem ReplicationPlan.confirmation_not_pilot {ι : Type*}
    (predecessor : NamedEndpoint) (pilotUnits confirmationUnits : List ι)
    (pilotNonempty : pilotUnits ≠ [])
    (confirmationNonempty : confirmationUnits ≠ [])
    (disjoint : pilotUnits.Disjoint confirmationUnits) (variation : VariationPlan)
    {unit : ι}
    (h : unit ∈ (ReplicationPlan.confirmation predecessor pilotUnits
      confirmationUnits pilotNonempty confirmationNonempty disjoint variation).confirmationUnits) :
    unit ∉ (ReplicationPlan.confirmation predecessor pilotUnits
      confirmationUnits pilotNonempty confirmationNonempty disjoint variation).pilotUnits := by
  change unit ∈ confirmationUnits at h
  change unit ∉ pilotUnits
  intro hp
  exact List.disjoint_left.mp disjoint hp h

/--
A single thing that must be true before launch.

Keeping obligations as data rather than as fields of a conjunction is what makes the
gate modular: a new way for experiments to be vacuous is a new constructor here, and
every consumer must then say how it is discharged.
-/
inductive Obligation (Trace : Type u)
  /-- This axis must carry gradient somewhere. -/
  | axisNavigable (a : Axis)
  /-- This positive-control axis must be proved unable to move the treatment.
  This is the opposite proposition, not an exemption from an obligation. -/
  | axisPredictedNonNavigable (a : Axis)
  /-- Some arm must have selection disabled. -/
  | controlPresent
  /-- Some pair of arms must be able to differ; identical arms are an inert
  treatment, not a robustness result. -/
  | armsSeparable
  /-- This flag must be observed to act on the smoke trace. -/
  | flagHonoured (f : Flag Trace)
  /-- Estimated cost must be within the cap. -/
  | withinBudget
  /-- Teardown must be scheduled. -/
  | teardownScheduled

/--
The obligations a registration generates.

Note that the control obligation is *derived from the claim*, not declared separately.
An experiment cannot register a "rarer than chance" claim and quietly omit its
control, because the obligation appears without being asked for.
-/
def Registration.obligations {Trace : Type u} (r : Registration Trace) :
    List (Obligation Trace) :=
  (r.arms.flatMap (fun a =>
    match a.role with
    | ArmRole.positiveControl => a.axes.map Obligation.axisPredictedNonNavigable
    | _ => a.axes.map Obligation.axisNavigable)) ++
  (match r.claim with
   | ClaimForm.rarerThanChance => [Obligation.controlPresent]
   | ClaimForm.comparative => [Obligation.armsSeparable]
   | ClaimForm.descriptive => []) ++
  (r.flags.map Obligation.flagHonoured) ++
  [Obligation.withinBudget, Obligation.teardownScheduled]

/-- Every axis of a non-positive-control arm generates a navigability obligation.
The role premise is necessary: without it the statement is false for positive
controls, whose obligation deliberately has the opposite polarity. -/
theorem mem_obligations_axisNavigable {Trace : Type u} {r : Registration Trace}
    {a : Arm} (ha : a ∈ r.arms) (hrole : a.role ≠ ArmRole.positiveControl)
    {ax : Axis} (hax : ax ∈ a.axes) :
    Obligation.axisNavigable ax ∈ r.obligations := by
  unfold Registration.obligations
  simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  refine Or.inl (Or.inl (Or.inl ⟨a, ha, ?_⟩))
  split <;> simp_all

/-- Every axis of a positive-control arm generates the predicted-null
obligation instead of the treatment navigability obligation. -/
theorem mem_obligations_axisPredictedNonNavigable
    {Trace : Type u} {r : Registration Trace} {a : Arm} (ha : a ∈ r.arms)
    (hrole : a.role = ArmRole.positiveControl) {ax : Axis} (hax : ax ∈ a.axes) :
    Obligation.axisPredictedNonNavigable ax ∈ r.obligations := by
  unfold Registration.obligations
  simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inl (Or.inl ⟨a, ha, by simp [hrole, hax]⟩))

/-- A "rarer than chance" claim always generates the control obligation. -/
theorem mem_obligations_controlPresent {Trace : Type u} {r : Registration Trace}
    (h : r.claim = ClaimForm.rarerThanChance) :
    Obligation.controlPresent ∈ r.obligations := by
  unfold Registration.obligations
  simp [h]

/-- Every declared flag generates an efficacy obligation. -/
theorem mem_obligations_flagHonoured {Trace : Type u} {r : Registration Trace}
    {f : Flag Trace} (hf : f ∈ r.flags) :
    Obligation.flagHonoured f ∈ r.obligations := by
  unfold Registration.obligations
  simp only [List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨f, hf, rfl⟩)

/-- Budget and teardown obligations are unconditional. -/
theorem mem_obligations_budget {Trace : Type u} (r : Registration Trace) :
    Obligation.withinBudget ∈ r.obligations := by
  unfold Registration.obligations; simp

theorem mem_obligations_teardown {Trace : Type u} (r : Registration Trace) :
    Obligation.teardownScheduled ∈ r.obligations := by
  unfold Registration.obligations; simp

end ExperimentPreregistration
