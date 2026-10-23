# O2: outer objective versus canonical cascade G

Source inspected: futon2 `src/futon2/aif/outer_policy_objective.clj`.

| Clojure term | Lines | Lean definition |
| --- | --- | --- |
| `risk = kl q c` | 137 | `outerG` input `risk` |
| `ambiguity = ambiguity-nats alpha` | 137 | `outerG` input `ambiguity` |
| `eig` / novelty | 105-107, 130-145 | `outerG` input `novelty` |
| `G = risk + ambiguity - eig` | 137-144 | `outerG` |
| `lnE` | 107, 126-129, 143-145 | `OuterPolicy.lnE` |
| `gamma` (one menu value) | 82-85, 95-98, 139, 145 | argument to `outerObjective` / `outerSelection` |
| `objective = gamma * G - lnE` | 137-145 | `outerObjective` |
| assessed-only population | 101-148, 153-164 | `assessedPairs` drops `.error`; `canonicalSelection` compares only those pairs |
| equal minima / uniform draw | 158-164, 205-212 | `outerSelection`, `TieDraw`, `applyTieDraw` |

The canonical score is `GOverCascades.cascadeGrainG`, an alias of
`CascadeCoApplyGNovelty.scoreCascadeCoN`; `compareAtHorizonN` evaluates every
candidate at the common H (`CascadeCoApplyGNovelty.lean:267-276`).

`outerSelection_eq_G_frontier` proves the real order condition: with one
positive menu gamma and a constant `lnE` over that menu, minimising
`gamma * G - lnE` has the same frontier as minimising G. The explicit
counterexample proves that the `lnE` condition cannot be dropped: equal G
does not generally agree with today's objective. `refused_dropped` establishes
that a canonical refusal is absent from the canonical selection population,
never converted to a score. This is the O3 input: bind/remove the extra terms,
or change the selection seam; do not call the current values formally the same
merely because both expose `G`.
