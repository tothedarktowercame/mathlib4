# O2: outer objective versus canonical cascade G

Source inspected: futon2 `src/futon2/aif/outer_policy_objective.clj`.

| Clojure term | Lines | Lean definition |
| --- | --- | --- |
| `risk = kl q c` | 137 | `outerG` input `risk` |
| `ambiguity = ambiguity-nats alpha` | 137 | `outerG` input `ambiguity` |
| `eig` / novelty | 105-107, 130-145 | `outerG` input `novelty` |
| `G = risk + ambiguity - eig` | 137-144 | `outerG` |
| `lnE` | 107, 126-129, 143-145 | `OuterPolicy.lnE` |
| `gamma` | 84, 97, 139, 145 | `OuterPolicy.gamma` |
| `objective = gamma * G - lnE` | 137-145 | `outerObjective` |
| equal minima / uniform draw | 158-164, 205-212 | `minimums`, `choose` (`drawSlot` is the already-drawn discrete slot) |

The canonical score is `GOverCascades.cascadeGrainG`, an alias of
`CascadeCoApplyGNovelty.scoreCascadeCoN`; `compareAtHorizonN` evaluates every
candidate at the common H (`CascadeCoApplyGNovelty.lean:267-276`).

The theorem `chooseBy_outerObjective` proves agreement only if the aligned
canonical score list equals `outerObjective` for every policy.  The explicit
counterexample proves that equal canonical G does not in general agree with
today's objective: policy-dependent `lnE` reverses its choice.  This is the
exact O3 input: bind/remove the extra terms, or change the selection seam; do
not call the current values formally the same merely because both expose `G`.
