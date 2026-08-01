/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: claude-4
-/
import DarkTower.ExperimentPreregistration
import DarkTower.ExperimentalDesign

/-!
# Slice 5 — the ant epistemic-ablation experiment, registered

M-aif-stack S1. Registers the re-specified Slice 5 of `M-aif-ants-port`, and
proves that the *original* Slice 5 was not ready to run.

## Why this file exists

Slice 5 was designed on 2026-07-14 to test whether the epistemic term drives
exploration in the AIF ant forager:

> pre-registered contrast: `aif-full − aif-no-epistemic > 0` on patchy/sparse
> (CI excludes 0), `≈ 0` on snowdrift.

On 2026-08-01 a static faithfulness scan and a causal-authority measurement
established that the canonical Gaussian ambiguity term in
`futon2/src/ants/aif/policy.clj:612-624` is computed from `(:var mu)` — the
*current belief variance* — which is identical across candidate actions, while
the predicted means vary by action. A term identical across candidates is a
constant, and a constant changes neither a softmax ordering nor an argmax.

The lane's history shows three attempts on this contrast in one day, the second
and third adding a harsher environment and a scarcity condition. That is what
chasing a structurally impossible effect looks like from the inside.

**This module states that impossibility as a theorem rather than as a
recollection.** `not_navigable_of_constant` is exactly the right instrument: the
ablation dial for a cancelling term has a constant score profile, so the axis is
not navigable, so the obligation the registration generates for it cannot be
discharged, so the design was never `ReadyToRun`.

The same argument applies a second time, to the commitment temperature: selection
is `(apply max-key :p policies)`, and argmax over `−G/τ` is argmax over `−G` for
every `τ > 0`, so the τ dial is also a constant-score axis. This was measured
independently — arm `:a3` was bit-identical to baseline on every seed.
-/

namespace DarkTower.Slice5

open ExperimentPreregistration
open ExperimentalDesign

/-! ## The trace

What a single ant run emits. Yields are per-arm mean food returned; the
`ambiguityDelta` field is singled out because the positive control reads it.
-/

/-- One completed sweep of the ant foraging experiment. -/
structure AntTrace where
  /-- Mean yield per arm name, per scenario. -/
  yields : String → String → ℝ
  /-- Share of runs with yield exactly 0. -/
  starvation : String → String → ℝ
  /-- Paired difference between `aif-full` and the canonical-ambiguity ablation.
  The positive control asserts this is exactly zero everywhere. -/
  ambiguityDelta : String → ℝ
  /-- Whether the harness observed ANY non-zero canonical-ambiguity delta on any
  seed. Recorded by the runtime gate rather than derived here: deciding equality
  of reals is not computable, and the same split is used by `Axis.gradientSteps`
  in the parent module. -/
  ambiguityMoved : Bool
  /-- Whether every logged seed reproduced bit-identically on replay. -/
  replayIdentical : Bool
  /-- Whether the environment config was frozen before the first arm ran. -/
  environmentFrozen : Bool

/-! ## The axes

An axis is an ablation dial. `levels` is the reachable set — here `[0, 1]`,
ablated and full — and `score` is the effect that dial has on selection.

The doc comment on `Axis` is the operative one: *a value present in the type and
absent from the mutation operator is in the representation and not in the
experiment*. Three of the four dials below are in the representation. Two of them
are not in the experiment, and this file proves it.
-/

/-- The canonical Gaussian ambiguity term. Its score profile is constant: the
term is computed from the current belief variance, identical across candidate
actions, so ablating it cannot change a selection. -/
noncomputable def ambiguityAxis : Axis where
  name := "canonical-gaussian-ambiguity"
  levels := [0, 1]
  score := fun _ => 0

/-- The commitment temperature τ. Also constant, for an independent reason:
selection is argmax over the softmax probabilities, and argmax over `−G/τ` is
argmax over `−G` for every positive τ. Measured: arm `:a3` was bit-identical to
baseline on all 90 runs. -/
noncomputable def tauAxis : Axis where
  name := "commitment-temperature"
  levels := [0, 1]
  score := fun _ => 0

/-- The directed-EIG proxy over the food-belief. Action-dependent, therefore a
candidate for carrying real gradient. Whether it does is the hypothesis. -/
noncomputable def directedEigAxis : Axis where
  name := "directed-eig-proxy"
  levels := [0, 1]
  score := fun x => x

/-- The KL risk leg. Action-dependent. Predicted to carry most of the authority,
by elimination from the 2026-08-01 measurement (score-permutation destroyed the
effect as completely as uniform-random selection). -/
noncomputable def riskAxis : Axis where
  name := "kl-risk"
  levels := [0, 1]
  score := fun x => x

/-! ## The impossibility results

These are the point of the file. -/

/-- The canonical ambiguity dial is not navigable. Ablating a term that is
constant across candidate actions cannot move behaviour. -/
theorem ambiguity_not_navigable : ¬ ambiguityAxis.Navigable :=
  not_navigable_of_constant (fun _ _ => rfl)

/-- The commitment-temperature dial is not navigable, for an independent reason:
argmax invariance under positive scaling. -/
theorem tau_not_navigable : ¬ tauAxis.Navigable :=
  not_navigable_of_constant (fun _ _ => rfl)

/-! ## The original design, and why it was not ready

The original Slice 5 arms were `:aif-full`, `:aif-no-epistemic`, `:classic`. The
ablation arm moved along exactly one dial — the canonical ambiguity term.
-/

/-- The original ablation arm: one axis, and that axis is the cancelling one. -/
noncomputable def originalAblationArm : Arm where
  name := "aif-no-epistemic"
  neutral := false
  axes := [ambiguityAxis]

/-- The original registration, reconstructed from `M-aif-ants-port.md` Slice 5. -/
noncomputable def originalRegistration : Registration AntTrace where
  name := "M-aif-ants-port Slice 5 (2026-07-14, as written)"
  claim := ClaimForm.comparative
  arms := [⟨"aif-full", false, [ambiguityAxis]⟩, originalAblationArm,
           ⟨"classic", true, []⟩]
  flags := []
  estimatedCost := 1
  budgetCap := 1
  teardownDeadline := some 1

/--
**The original Slice 5 generated an obligation it could not discharge.**

Every axis of every arm generates a navigability obligation. The ablation arm's
only axis is the cancelling ambiguity term, which is not navigable. So the
registration carries an obligation whose content is false, and no discharge of
the obligation list is possible.

This is the formal statement of what three runs on 2026-07-14 discovered
empirically and attributed to the environment.
-/
theorem original_obligation_undischargeable :
    Obligation.axisNavigable ambiguityAxis ∈ originalRegistration.obligations ∧
    ¬ ambiguityAxis.Navigable := by
  constructor
  · exact mem_obligations_axisNavigable (a := originalAblationArm)
      (by simp [originalRegistration]) (by simp [originalAblationArm])
  · exact ambiguity_not_navigable

/-! ## The re-specified design

Arms are split so that the cancelling term is isolated as a *positive control on
the instrument* rather than serving as a hypothesis arm, and the dials that can
actually carry gradient are ablated separately.
-/

/-- The positive control. Predicted to produce exactly zero difference on every
seed. It is retained deliberately, and its non-navigability is the prediction —
if it moves, the analysis behind this registration is wrong. -/
noncomputable def positiveControlArm : Arm where
  name := "no-canonical-ambiguity"
  neutral := false
  axes := [ambiguityAxis]

/-- The live epistemic test. -/
noncomputable def eigArm : Arm where
  name := "no-directed-eig"
  neutral := false
  axes := [directedEigAxis]

/-- The risk-leg ablation, absent from every previous design. -/
noncomputable def riskArm : Arm where
  name := "no-risk"
  neutral := false
  axes := [riskAxis]

/-- The stop rule that makes the positive control load-bearing: if the cancelling
term moves anything, the run halts and is not interpreted. -/
noncomputable def positiveControlStop : StopRule AntTrace where
  name := "positive-control-violated"
  fires := fun t => t.ambiguityMoved = true
  check := fun t => t.ambiguityMoved
  check_iff := fun _ => Iff.rfl

/-!
`check_iff` is `Iff.rfl` because the harness reports the comparison, rather than
the specification attempting to decide equality of reals. This follows the split
the parent module already makes for `Axis.gradientSteps`, which is noncomputable
"because it decides equality of reals: this is the specification, and the runtime
gate evaluates the corresponding test on measured values."

The obligation this moves rather than removes: `ambiguityMoved` must be computed
by the harness as *any non-zero paired delta on any seed*, not as a threshold
test. A harness that sets it from `|delta| > epsilon` would satisfy this file and
silently weaken the control. That is the first review item.
-/

end DarkTower.Slice5
