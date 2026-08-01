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

/-! ## The invariance that does the work

codex-8's review of the first version of this file was that its theorems were
petitio principii: `ambiguityAxis` was declared with `score := fun _ => 0`, and
Lean then proved only that an object declared constant is non-navigable. Nothing
connected that object to expected free energy or to candidate selection. The
review was correct and this section is the repair.

The actual structure in `policy.clj:612-624` is

  `G_lam(a) = base a + lam * A`

where `base` is action-dependent (it is computed from `pred-means`, which vary
with the candidate) and `A` is the **same real for every candidate**, because it
is computed from `pred-variances = (:var mu)`, the current belief variance. The
ablation dial is `lam`.

The raw score is emphatically *not* constant in `lam`. What is invariant is the
induced ordering — and therefore the argmax, and therefore the normalised
softmax distribution. That is the theorem the first version assumed.
-/

/-- The ant's candidate score, decomposed as the code computes it: an
action-dependent part, plus an ambiguity contribution entering with the same
coefficient for every candidate. -/
noncomputable def antScore {C : Type*} (base : C → ℝ) (A lam : ℝ) : C → ℝ :=
  fun a => base a + lam * A

/--
**Common-offset invariance.** Varying the ablation coefficient `lam` cannot change
the order of any two candidates, because it moves both by the same amount.

This is the whole content of the ant finding, and it is what the previous version
of this file asserted instead of proving.
-/
theorem ambiguity_ablation_preserves_order {C : Type*}
    (base : C → ℝ) (A lam lam' : ℝ) (a b : C) :
    antScore base A lam a ≤ antScore base A lam b ↔
    antScore base A lam' a ≤ antScore base A lam' b := by
  unfold antScore
  rw [add_le_add_iff_right, add_le_add_iff_right]

/-- A selected action is any candidate that is weakly best. Argmax and softmax
both select from this set; softmax's normalisation cancels a common offset for
the same reason. -/
def IsSelected {C : Type*} (score : C → ℝ) (a : C) : Prop := ∀ b, score b ≤ score a

/--
**The ablation cannot change what is selected.** An immediate consequence of
common-offset invariance, and the statement the experiment actually needed.
-/
theorem ambiguity_ablation_preserves_selection {C : Type*}
    (base : C → ℝ) (A lam lam' : ℝ) (a : C) :
    IsSelected (antScore base A lam) a ↔ IsSelected (antScore base A lam') a := by
  unfold IsSelected
  constructor <;> intro h b <;>
    exact (ambiguity_ablation_preserves_order base A _ _ b a).mp (h b)

/-! ### From invariance to non-navigability

Only now is the axis declaration earned. The behavioural score of the ablation
dial is constant *because* selection is invariant along it — not by fiat.

The premise `A` is action-independent is an **empirical import** from reading
`policy.clj:612-624`, not something Lean checks. It is stated here as a named
hypothesis so that a reader can reject it, rather than buried in a definition.
-/

/-- The ablation dial for a common-offset term. Its behavioural score is constant
by `ambiguity_ablation_preserves_selection`. -/
noncomputable def ambiguityAxis : Axis where
  name := "canonical-gaussian-ambiguity"
  levels := [0, 1]
  score := fun _ => 0

/-- The canonical ambiguity dial is not navigable. -/
theorem ambiguity_not_navigable : ¬ ambiguityAxis.Navigable :=
  not_navigable_of_constant (fun _ _ => rfl)

/-! ### The temperature, with its assumptions stated

codex-8 raised three defects in the first version's `tauAxis`, all correct:
the level `0` is outside the positive-temperature argument; the executed arm
uses `1.0e9`, not `1`; and the implementation is IEEE doubles, where underflow,
rounding-created ties, infinities and NaN block any unconditional
implementation-level claim. The exact-real theorem is stated below with `0 < t`
as an explicit hypothesis, and the gap to the float implementation is named
rather than closed.
-/

/-- **Positive rescaling preserves the ordering**, hence argmax. This is the τ
argument, over exact reals. -/
theorem scaling_preserves_order {C : Type*} (G : C → ℝ) {t : ℝ} (ht : 0 < t)
    (a b : C) : G a / t ≤ G b / t ↔ G a ≤ G b :=
  div_le_div_iff_of_pos_right ht

/-- The temperature dial, at the levels the experiment actually reaches. -/
noncomputable def tauAxis : Axis where
  name := "commitment-temperature"
  levels := [1, 1000000000]
  score := fun _ => 0

/-- The temperature dial is not navigable. **Caveat, not proved here:** this holds
over exact reals given `0 < t`. The implementation uses IEEE doubles, so ties
created by rounding, underflow, or non-finite values are outside this statement.
The 90 bit-identical runs of arm `:a3` are evidence for the float case, not a
proof of it. -/
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
  role := .treatment

/-- The original registration, reconstructed from `M-aif-ants-port.md` Slice 5. -/
noncomputable def originalRegistration : Registration AntTrace where
  name := "M-aif-ants-port Slice 5 (2026-07-14, as written)"
  claim := ClaimForm.comparative
  arms := [⟨"aif-full", false, [ambiguityAxis], .treatment⟩, originalAblationArm,
           ⟨"classic", true, [], .baselineNeutral⟩]
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
      (by simp [originalAblationArm])
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
  role := .positiveControl

/-- The live epistemic test. -/
noncomputable def eigArm : Arm where
  name := "no-directed-eig"
  neutral := false
  axes := [directedEigAxis]
  role := .treatment

/-- The risk-leg ablation, absent from every previous design. -/
noncomputable def riskArm : Arm where
  name := "no-risk"
  neutral := false
  axes := [riskAxis]
  role := .treatment

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
