# Checked return observation: execution receipt

- Date: 2026-10-24 UTC. Author: claude-14 (requested by codex-11).
- Base: `152247b978` (darktower). Branch: `wm-checked-return-observation`.
- Worktree: `/home/joe/worktrees/mathlib4-checked-return-observation` (`.lake` symlinked to `~/code/mathlib4/.lake`, as for the previous modules). Toolchain `leanprover/lean4:v4.31.0-rc1`.
- Module: `DarkTower/WarMachine/CheckedReturnObservation.lean` (568 lines), SHA-256 `bc776dde50e18ecf03a76b54d5210815ab5b88a41290c2e5e8455c2e0ef903b6`. Copy of this receipt beside it.
- Probes here: `Axioms.lean` (`65aa6092…`), `FalseObservation.lean` (`27a380cb…`).
- No existing definition changed. No Clojure, runtime, reload, click or main merge.

## Commands and exits (from the worktree)

| Command | Exit | Log |
|---|---|---|
| `lake env lean DarkTower/WarMachine/CheckedReturnObservation.lean` | 0, no output | `lean.log` |
| `lake build DarkTower.WarMachine.CheckedReturnObservation` | 0, 3362 jobs | `build.log` |
| `lake env lean …/Axioms.lean` (28 theorems) | 0 | `axioms.log` |
| `lake env lean …/FalseObservation.lean` | 1, expected | `false-observation.log` |
| `git diff --check` | 0 | — |

Axioms: 27 theorems `[propext, Classical.choice, Quot.sound]`, one (`present_reports_claim_consumer`) `[propext, Quot.sound]`. `sorryAx`: 0. `sorry` in module: 0. `Classical.choice` enters through the noncomputable `closedSet`, the reals, and the choice in `labelFactors_iff`.

## What is defined (reusing, not duplicating)

- `closureObs scored m := scored ∩ closedSet m`; `returnObs m₀ scored realize a := closureObs scored (update m₀ (realize a))`. Uses `CheckedProblemMap.update`/`closedSet` only. Label and `claimedClosed` are never read.
- `realize : A → Option (ReturnReport I Label)` is an explicit parameter: supplied synthetic scenario assumptions, not a decoder or authenticity result. Proof payloads need not be finite; only `A` is `Fintype`.
- `observationKernel … k := AIFReportEncoding.reportKernel k (returnObs …)` (the reviewed deterministic post-composition). `conditionalObservation` specialises it to `OuterReturnModel.conditionalReturn`. Latent integration is the existing `CascadeEFE.push`.
- `LabelFactors`: the separately stated condition that labels determine the observation. Not assumed anywhere.

## General theorems

- `mem_returnObs`: `s ∈ returnObs … a ↔ s ∈ scored ∧ Closed (update m₀ (realize a)) s`; `returnObs_sound`: membership gives `I s`, for every return value whatever its mass.
- `preexisting_subset_returnObs`, `returnObs_absent` (absent = preexisting scored closures, not ∅), `returnObs_unchecked` (empty checked part = absent), `returnObs_eq_of_checked` (observation depends only on `Option.map checked`).
- `labelFactors_iff`: factorisation through labels ↔ observation constant on label fibres of present reports.
- `observationKernel_normalised`; `observationKernel_mass` (exact); `observationKernel_event`: for any decidable event `P` on observations, its mass = return-kernel mass of `{a | P (returnObs a)}`; `observationKernel_closure_marginal`; `preexisting_observed_surely` (probability 1, any kernel, absent mass included); `push_observationKernel` (push commutes with observation, via `push_report_mass`).
- `conditionalObservation_normalised`, `conditionalObservation_mass` (verdict mass × joint result mass over the fibre), `conditionalObservation_closure_marginal`, `push_conditionalObservation` (predictive observation = observation of `predictiveReturn`).

## Controls (six-ID `m0` of CheckedProblemMap; scored {consumer, adapter, cycA})

- `foundationOnly_not_observed`: labelled closed, claims the consumer, consumer not observed.
- `foundationAndAdapter_observed`: consumer observed.
- `absent_on_m0_not_observed`; on `m1 = update m0 (some foundationAndAdapter)`: `absent_preserves_preexisting`, `absent_observation_nonempty`.
- `predictionOnly_unchanged` (any map): equals the absent observation.
- `censored_helper_observed`: adapter observed, consumer not.
- `same_label_different_observation` (same label, same claims, different checked content, different observation) and `labels_do_not_factor` (¬ `LabelFactors`).
- Finite outer return `Sigma Res` (present: Bool "adapter checked"; absent: Unit), verdict surely present, result copies a uniform latent bit. `present_reports_claim_consumer`: every present report is labelled closed and claims the consumer; `consumer_observed_half`, `adapter_observed_half`: each 1/2; `shared_latent_joint_closure`: joint 1/2 ≠ product 1/4 of the actual marginals.
- `m1_consumer_observed_surely`: on `m1`, probability 1 under every kernel over the alphabet, including ones with positive absent mass.

## Deliberate false theorems (`FalseObservation.lean`, exit 1)

1. `false_label_predicts_closure` (consumer observed with probability 1): unsolved `False` after rewriting with the proved value 1/2.
2. `false_absent_observes_nothing`: type mismatch against the proved `consumer ∈ obsOf m1 none`.
3. `false_foundation_only_observed`, attempted through the real `viaFoundation` constructor: unsolved goal `adapterArt ∈ m0.artifacts ∨ adapterArt = foundationArt`, i.e. the adapter artifact was never admitted.

## Boundary and open items

- AIF: observation-through-normalised-likelihood framing per Parr et al. 2022 ch. 7 (eqs. 7.9–7.11), as in `OuterReturnModel`; Da Costa 2020 eq. 15 approximation boundary untouched. Grounding of the observation in proof closure is problem-map domain semantics, not an AIF theorem.
- Open: executable/decidable closure and its agreement with `Closed`; decoder and authenticity of runtime records; ID↔Lean-name/commit binding; growing `S`; chosen probabilities, preferences, admission or learning rule; multi-iteration binding (next packet). No R20, full-loop or runtime claim.
