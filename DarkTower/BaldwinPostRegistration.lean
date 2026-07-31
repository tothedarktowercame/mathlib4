/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.ExperimentalDesign
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Post-registration of the Baldwin hold-only battery

A post hoc registration of the battery specified in `holes/BALDWIN-PAID-RUN-PLAN.md`,
carried out to test whether the gate in `ExperimentalDesign` can certify a real
protocol rather than only refuse synthetic bad ones.

The exercise is honest in one direction and not the other. The protocol was written
independently of this model, so its satisfying the obligations is *convergent* rather
than circular. But the obligations themselves were derived from earlier failures, so a
pass here shows the gate is *satisfiable by good practice* --- not that it discriminates.
Discrimination needs held-out designs the obligations were not fitted to.

`certifiable` at the end is the deliverable: a constructed `ReadyToRun`, i.e. a proof
that this battery *could* have been provisioned under the gate.

## What the exercise surfaced

Confronting the model with an independently-written protocol found three obligations
the protocol requires and the model does not. These are gaps in the MODEL, recorded in
`ExperimentPreregistration` as future work rather than papered over here:

1. **Seed replication.** The protocol states that a headline result must be replicated
   under preregistered additional evolution seeds, and that duplicating cost arms under
   one hard-coded seed is not replication. The model has no such obligation, and would
   certify a single-seed battery as ready.
2. **Stop rules.** The protocol fixes abort conditions in advance --- a failed mode
   assertion, an inert treatment ranking, an arm timeout. The model treats readiness as
   a property of the start only, and says nothing about conditions under which a
   running experiment must halt.
3. **Pre-committed interpretation.** The protocol fixes what will count as evidence
   before the run, including that holding rising while function falls is loss of
   function and that an inert cost is not a negative result. The model records a
   `ClaimForm` but not the decision rule that maps outcomes onto conclusions.

That the protocol independently reaches the fail-closed principle --- "authentication
errors, missing executables, empty output, and HTTP errors are failures, never evidence
of absence" --- is the same content as `Observable.check_sound`, arrived at from the
operational side.
-/

namespace BaldwinPostRegistration

open ExperimentPreregistration ExperimentalDesign

/-! ## The trace this battery emits -/

/--
The observable facts a generation record carries, reduced to what the declared modes
constrain. These are exactly the contracts the runner asserts "over every genome at
generation entry and after breeding".
-/
structure Trace where
  /-- `gamma = 1` for every individual, every generation. -/
  gammaPinned : Bool
  /-- `update-prob = 1` likewise. -/
  updatePinned : Bool
  /-- Every mask bit live. -/
  maskAllLive : Bool
  /-- Every hold bit fixed (the additional `static-search` contract). -/
  holdBitsFixed : Bool
  deriving Repr

/-! ## The two modes, as flags that carry their own falsifiers -/

/-- `hold-only`: gamma, update-prob and mask pinned, so holding is the only route by
which measured dependence can fall. -/
def holdOnly : Flag Trace where
  name := "--mode hold-only"
  observable :=
    { name := "gamma = 1, update-prob = 1, every mask bit live"
      holds := fun t =>
        t.gammaPinned = true ∧ t.updatePinned = true ∧ t.maskAllLive = true
      check := fun t => t.gammaPinned && t.updatePinned && t.maskAllLive
      check_sound := by
        intro t h
        simp only [Bool.and_eq_true] at h
        exact ⟨h.1.1, h.1.2, h.2⟩ }

/-- `static-search`: the hold-only contracts plus every hold bit fixed, so only the
inherited rule field can evolve. -/
def staticSearch : Flag Trace where
  name := "--mode static-search"
  observable :=
    { name := "hold-only invariants, and every hold bit fixed"
      holds := fun t =>
        t.gammaPinned = true ∧ t.updatePinned = true ∧ t.maskAllLive = true ∧
        t.holdBitsFixed = true
      check := fun t =>
        t.gammaPinned && t.updatePinned && t.maskAllLive && t.holdBitsFixed
      check_sound := by
        intro t h
        simp only [Bool.and_eq_true] at h
        exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩ }

/-! ## Axes -/

/--
The cost axis, at the levels the battery actually visits: `0`, `0.05`, `2`.

Navigability here is *not* assumed. The protocol makes it an observation: step 6 checks
treatment separation over every post-warm-up generation for `0 vs 0.05` and `0.05 vs 2`,
and step 7 runs the stronger cost "only if the observed c05 populations prove that the
stronger cost can change selection ordering". The score below is the one that check is
required to exhibit; a run in which it is flat trips the protocol's own stop rule.
-/
noncomputable def costAxis : Axis where
  name := "c"
  levels := [0, 0.05, 2]
  score := fun c => c

theorem costAxis_navigable : costAxis.Navigable := by
  unfold Axis.Navigable Axis.gradientSteps costAxis
  have hmem : ((0 : ℝ), (5e-2 : ℝ)) ∈
      (costAxis.levels.zip costAxis.levels.tail).filter
        (fun p => costAxis.score p.1 ≠ costAxis.score p.2) := by
    rw [List.mem_filter]
    refine ⟨by simp [costAxis], ?_⟩
    simp only [costAxis, decide_eq_true_eq, ne_eq]
    norm_num
  exact List.length_pos_of_mem hmem

/-! ## Arms -/

/-- The empirical mutation-only null, using the production breeding operator. -/
noncomputable def nullArm : Arm where
  name := "mutation-only null"
  neutral := true
  axes := [costAxis]

/-- `hold-only` at `c = 0.05`. -/
noncomputable def holdOnlyArm : Arm where
  name := "hold-only c=0.05"
  neutral := false
  axes := [costAxis]

/-- `static-search` at `c = 0`. -/
noncomputable def staticSearchArm : Arm where
  name := "static-search c=0"
  neutral := false
  axes := [costAxis]

/-! ## The registration -/

/--
The battery as registered.

`estimatedCost` and `budgetCap` are in minutes: the protocol's 240 is an outer
emergency ceiling, and the canary at step 3 supplies the estimate that must fit under
it. 150 is the pre-canary projection for the sequential battery.
-/
noncomputable def battery : Registration Trace where
  name := "baldwin-hold-only"
  claim := ClaimForm.rarerThanChance
  arms := [nullArm, holdOnlyArm, staticSearchArm]
  flags := [holdOnly, staticSearch]
  estimatedCost := 150
  budgetCap := 240
  teardownDeadline := some 240

/-! ## Evidence -/

/--
What the protocol's supervisor establishes before and during provisioning.

`armsShownDistinct` is discharged by step 6 rather than assumed: the protocol treats
persistently equivalent treatment rankings as a stop condition, which is the
operational form of the model's separability obligation.
-/
def supervisorEvidence : Evidence where
  toolchainExercised := true      -- direct HTTPS client check; no bare CLI assumption
  codeIdentityAsserted := true    -- revision-bound preflight certificate
  teardownExercised := true       -- dead-man armed, deletion confirmed by API 404
  armsShownDistinct := true       -- step 6 treatment-separation check

/-- A smoke trace in which both declared modes are honoured, which is what the
runner's per-generation contract assertion produces. -/
def smokeTrace : Trace where
  gammaPinned := true
  updatePinned := true
  maskAllLive := true
  holdBitsFixed := true

/-! ## The witness -/

/--
**The battery is certifiable.**

A constructed `ReadyToRun`, so by `Launch` this protocol could have been provisioned
under the gate. This is the "could work" evidence: the model is satisfiable by a real
protocol written without reference to it.

It is not evidence that the model discriminates. Every obligation here was derived from
an earlier failure, so passing a well-written plan is the weakest of the three tests
worth running; held-out refusal and prospective refusal are the ones that would carry a
methods claim.
-/
noncomputable def certifiable : ReadyToRun battery supervisorEvidence smokeTrace where
  apparatus := ⟨rfl, rfl, rfl⟩
  discharged := by
    intro o ho
    -- The obligation list is concrete, so membership splits into finitely many cases.
    simp only [Registration.obligations, battery, nullArm, holdOnlyArm, staticSearchArm,
      List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with h | h | h | h | h | h | h | h <;> subst h
    · exact costAxis_navigable
    · exact costAxis_navigable
    · exact costAxis_navigable
    · exact ⟨nullArm, by simp [battery], rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · simp only [Discharged, battery]
      linarith
    · rfl

end BaldwinPostRegistration
