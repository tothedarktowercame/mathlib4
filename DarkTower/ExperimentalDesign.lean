/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.ExperimentPreregistration

/-!
# The pre-go-live gate

`ExperimentPreregistration` declares what an experiment claims and derives the
obligations that follow. This file consumes that: it says what evidence discharges an
obligation, bundles the discharged obligations into a witness, and makes the witness a
*required argument* of launching.

`BaldwinDesign` specifies what a result must exhibit before it may be claimed; this is
the same move one level out, for what a run must exhibit before it may start.

The two structural properties are worth stating plainly, because they are what
distinguishes an envelope from a checklist:

* a `Flag` cannot be constructed without its observable (in the preregistration), so a
  setting that silently does nothing is not declarable;
* `Launch` takes a `ReadyToRun`, so there is no code path that starts a run without
  the gate --- a checklist can be skipped under time pressure, a missing argument
  cannot.

Lean cannot determine whether a binary is on the `PATH`. `Evidence` is what a runtime
checker asserts, and this file fixes what a complete assertion consists of and proves
what follows from one. The division matches `BaldwinDesign` specifying and the
Clojure checker deciding.
-/

namespace ExperimentalDesign

open ExperimentPreregistration

universe u

/-! ## Evidence the runtime supplies -/

/--
What a runtime checker asserts, having actually looked.

Each field is a failure that occurred, not a category invented for completeness.
The `Bool`s are deliberately opaque here: their content is that some checker was
willing to assert them, and this file's job is to make that assertion *necessary*
rather than to second-guess it.
-/
structure Evidence where
  /-- Every external tool resolved *and executed* in the environment the run will
  actually use. Resolution alone is insufficient: an unauthorised CLI fails exactly
  like an absent one, and a `systemd --user` unit has a narrower `PATH` than the shell
  that launched it, so a tool can work interactively and be missing in the unit. -/
  toolchainExercised : Bool
  /-- The remote is at the expected commit, asserted rather than assumed. A pull that
  fails on a dirty tree leaves stale code running and reports little. -/
  codeIdentityAsserted : Bool
  /-- The teardown path was itself exercised. A teardown verified with a tool that is
  absent reports success while doing nothing, which is worse than no teardown because
  it looks handled. -/
  teardownExercised : Bool
  /-- The arms were observed to produce distinct output. Two arms that cannot differ
  will agree, and their agreement reads as robustness when it is an inert treatment;
  this is not decidable from the declaration, so it must be observed. -/
  armsShownDistinct : Bool

/-- The apparatus fields, which are prerequisites for any obligation being meaningful. -/
def Evidence.apparatusSound (e : Evidence) : Prop :=
  e.toolchainExercised = true ∧ e.codeIdentityAsserted = true ∧ e.teardownExercised = true

/-! ## Discharging an obligation -/

/--
What it takes to discharge each obligation.

This is the seam between the two modules. A new obligation constructor in the
preregistration forces a new case here, so a newly-recognised way for an experiment to
be vacuous cannot be added without saying what would rule it out.
-/
def Discharged {Trace : Type u} (r : Registration Trace) (e : Evidence) (smoke : Trace) :
    Obligation Trace → Prop
  | Obligation.axisNavigable a => a.Navigable
  | Obligation.controlPresent => ∃ a ∈ r.arms, a.neutral = true
  | Obligation.armsSeparable => e.armsShownDistinct = true
  | Obligation.flagHonoured f => f.honoured smoke
  | Obligation.withinBudget => r.estimatedCost ≤ r.budgetCap
  | Obligation.teardownScheduled => r.teardownDeadline.isSome = true

/-! ## The witness -/

/--
An experiment is ready when its apparatus is sound and every obligation its
registration generates is discharged.

`smoke` is a trace from a short run made before the real one. It is the part a unit
test cannot replace: it exercises the path from the command line through to the
function, which is exactly where a setting can be parsed, ignored, and reported as
applied.
-/
structure ReadyToRun {Trace : Type u} (r : Registration Trace) (e : Evidence)
    (smoke : Trace) where
  apparatus : e.apparatusSound
  discharged : ∀ o ∈ r.obligations, Discharged r e smoke o

/--
Launching requires a witness.

The gate is an argument, so there is no path that starts a run without it. This is the
whole of the structural claim; everything else in the file is about making the witness
hard to obtain dishonestly.
-/
def Launch {Trace : Type u} (r : Registration Trace) (e : Evidence) (smoke : Trace)
    (_w : ReadyToRun r e smoke) (run : Registration Trace → Trace) : Trace := run r

/--
The stronger launch token for a prospective registration.  Besides the base readiness
gate, its smoke trace must show that none of the preregistered stop conditions already
fires.  Runtime supervisors remain responsible for applying the same exact checks to
later traces.
-/
structure ProspectiveReadyToRun {Trace : Type u} {Outcome : Type*}
    (r : ProspectiveRegistration Trace Outcome) (e : Evidence) (smoke : Trace) where
  baseReady : ReadyToRun r.base e smoke
  smokeClear : ∀ s ∈ r.stopRules, s.check smoke = false

/-- The designated launch entry point for a prospective registration. -/
def ProspectiveLaunch {Trace : Type u} {Outcome : Type*}
    (r : ProspectiveRegistration Trace Outcome) (e : Evidence) (smoke : Trace)
    (_w : ProspectiveReadyToRun r e smoke)
    (run : ProspectiveRegistration Trace Outcome → Trace) : Trace := run r

/-! ## The general refusal, and its instances -/

/--
**The gate.** An obligation that is generated and not discharged means no witness
exists, hence no launch.

Every specific refusal below is a corollary. Adding a new way for an experiment to be
vacuous therefore costs one constructor and one `Discharged` case, not a new theorem:
the refusal comes for free.
-/
theorem no_witness_of_undischarged {Trace : Type u} {r : Registration Trace}
    {e : Evidence} {smoke : Trace} {o : Obligation Trace}
    (hmem : o ∈ r.obligations) (hno : ¬ Discharged r e smoke o) :
    IsEmpty (ReadyToRun r e smoke) :=
  ⟨fun w => hno (w.discharged o hmem)⟩

/-- A dead axis admits no witness. The profile that was zero at every sampled level
but one is refused here rather than discovered afterwards. -/
theorem no_witness_of_dead_axis {Trace : Type u} {r : Registration Trace}
    {e : Evidence} {smoke : Trace} {a : Arm} (ha : a ∈ r.arms)
    {ax : Axis} (hax : ax ∈ a.axes) (hdead : ¬ ax.Navigable) :
    IsEmpty (ReadyToRun r e smoke) :=
  no_witness_of_undischarged (mem_obligations_axisNavigable ha hax) hdead

/-- A constant axis admits no witness, via the preregistration's lemma. -/
theorem no_witness_of_constant_axis {Trace : Type u} {r : Registration Trace}
    {e : Evidence} {smoke : Trace} {a : Arm} (ha : a ∈ r.arms)
    {ax : Axis} (hax : ax ∈ a.axes) (hconst : ∀ x y, ax.score x = ax.score y) :
    IsEmpty (ReadyToRun r e smoke) :=
  no_witness_of_dead_axis ha hax (not_navigable_of_constant hconst)

/-- A "rarer than chance" claim with no no-selection arm admits no witness. -/
theorem no_witness_of_missing_control {Trace : Type u} {r : Registration Trace}
    {e : Evidence} {smoke : Trace} (hclaim : r.claim = ClaimForm.rarerThanChance)
    (hnone : ∀ a ∈ r.arms, a.neutral = false) :
    IsEmpty (ReadyToRun r e smoke) := by
  refine no_witness_of_undischarged (mem_obligations_controlPresent hclaim) ?_
  rintro ⟨a, ha, hneutral⟩
  rw [hnone a ha] at hneutral
  exact Bool.false_ne_true hneutral

/-- A flag not observed to act on the smoke trace admits no witness. This is the
refusal that a silently no-opping setting triggers. -/
theorem no_witness_of_inert_flag {Trace : Type u} {r : Registration Trace}
    {e : Evidence} {smoke : Trace} {f : Flag Trace} (hf : f ∈ r.flags)
    (hinert : ¬ f.honoured smoke) : IsEmpty (ReadyToRun r e smoke) :=
  no_witness_of_undischarged (mem_obligations_flagHonoured hf) hinert

/-- An over-budget registration admits no witness. -/
theorem no_witness_of_over_budget {Trace : Type u} {r : Registration Trace}
    {e : Evidence} {smoke : Trace} (h : r.budgetCap < r.estimatedCost) :
    IsEmpty (ReadyToRun r e smoke) :=
  no_witness_of_undischarged (mem_obligations_budget r) (not_le.mpr h)

/-- A registration with no scheduled teardown admits no witness. -/
theorem no_witness_of_no_teardown {Trace : Type u} {r : Registration Trace}
    {e : Evidence} {smoke : Trace} (h : r.teardownDeadline = none) :
    IsEmpty (ReadyToRun r e smoke) := by
  refine no_witness_of_undischarged (mem_obligations_teardown r) ?_
  simp only [Discharged, h, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]

/-! ## What a witness buys -/

/--
**A certified null is informative.**

The reason the gate is worth its cost. If a certified run returns nothing, the absence
is a fact about the object rather than about the apparatus: every axis could have
moved, the control obligation was discharged, and every setting was observed to act.
Without certification a null distinguishes nothing at all --- which is what a set of
null results can quietly be worth.
-/
theorem certified_axes_are_navigable {Trace : Type u} {r : Registration Trace}
    {e : Evidence} {smoke : Trace} (w : ReadyToRun r e smoke)
    {a : Arm} (ha : a ∈ r.arms) {ax : Axis} (hax : ax ∈ a.axes) :
    0 < ax.gradientSteps :=
  w.discharged _ (mem_obligations_axisNavigable ha hax)

/-- Under certification, every declared setting was in force during the smoke run. -/
theorem certified_flags_act {Trace : Type u} {r : Registration Trace}
    {e : Evidence} {smoke : Trace} (w : ReadyToRun r e smoke)
    {f : Flag Trace} (hf : f ∈ r.flags) : f.honoured smoke :=
  w.discharged _ (mem_obligations_flagHonoured hf)

/-- Under certification the run is within its stated cap, so a budget overrun is a
failure of the estimate rather than of the gate. -/
theorem certified_within_budget {Trace : Type u} {r : Registration Trace}
    {e : Evidence} {smoke : Trace} (w : ReadyToRun r e smoke) :
    r.estimatedCost ≤ r.budgetCap :=
  w.discharged _ (mem_obligations_budget r)

/-- Under certification a teardown is scheduled, independently of whether the run
succeeds. -/
theorem certified_teardown_scheduled {Trace : Type u} {r : Registration Trace}
    {e : Evidence} {smoke : Trace} (w : ReadyToRun r e smoke) :
    r.teardownDeadline.isSome = true :=
  w.discharged _ (mem_obligations_teardown r)

end ExperimentalDesign
