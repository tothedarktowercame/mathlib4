# DarkTower evaluator-comb — DERIVE spec (before INSTANTIATE)

**Status:** DERIVE (2026-07-14). This specifies the evaluator side of the
"everything is a comb" unification (`M-metaca-search` §3.6) so that discriminators
are DarkTower-native — a comb DERIVED before any Clojure/Lean is INSTANTIATEd.
Companion to [`AIF-COMPLIANCE.md`](./AIF-COMPLIANCE.md) (generator/controller
side) and the generator exemplar [`MetaCAExample.lean`](./MetaCAExample.lean).

**Motive (why DERIVE first).** AIS and nearest-neighbor TE were INSTANTIATEd in
Clojure with no spec; only the ECA trust anchor, run *after* building, revealed
that nn-TE ranks chaotic above complex (it is not an EoC discriminator). Deriving
the comb first forces the structure — and the validation property — to be stated
before code exists.

## 1. The evaluator-comb skeleton

An evaluator is a comb `behaviour → score`, feed-forward (like the CA generators,
so it fits the current `Fill`/`BV` machinery — no open-diagram layer):

```
readSpacetime  ◁  selectSources  ◁  estimate  ◁  aggregate
```

- `readSpacetime` — the spacetime grid (a bitplane of it) is the input behaviour.
- `selectSources` — for each destination cell/next-state, choose which *source*
  observations condition the prediction. **This stage is the entire discriminator
  family** (see §2).
- `estimate` — a corrected conditional-mutual-information estimator
  `I(source ; dest-next | dest-past)` (Miller–Madow), over the selected sources.
- `aggregate` — reduce per-cell/per-plane estimates to one scalar score.

## 2. The variation holes (and why the discriminators are occupants)

Two `TypedHole`s carry the variation, exactly as `combine`/`mutate` do for
generators:

**`sourceHole`** — the policy for `selectSources`. Its fills:
- `selfPast` — source = the destination cell's own past. → **AIS** (`storage`).
- `nearestNeighbor` — source = the adjacent cell's past. → **nn-TE** (`local transfer`).
- `offset (d, τ)` — source = the cell `d` sites away, `τ` steps back. → **distance/lagged TE**.

**`paramHole`** — `{destPast k, sourcePast l, offset (d,τ), alphabet, correction, aggregate}`
(the `alphabet` fill is load-bearing — see §3.5).

So **AIS, nn-TE, and distance-TE are three occupants of ONE evaluator-comb**,
differing only by the `sourceHole` fill — the precise mirror of the 9 CA
dynamics being occupants of one generator-comb. `DynamicOccupant` has a twin:
`EvaluatorOccupant { sourceFill, paramFill }`.

## 3. The distance-TE occupant (ARGUE)

- **IF** the eye's EoC signal is coherent, long-range, constant-velocity
  propagating structure (gliders — confirmed on the seed-42 diagrams: template &
  w=0.9 show diagonals, w=0.5 dissolves them),
- **HOWEVER** `selfPast` (AIS) measures only per-cell memory and `nearestNeighbor`
  (nn-TE) measures only `d=1` flow — which is maximal in *chaos* (dense local
  dependence), so nn-TE ranked chaotic > complex and *failed* the trust anchor,
- **THEN** the correct occupant sets `sourceHole := offset (d, τ)` with `(d, τ)`
  matched to the glider velocity (diagonal ⇒ `d = v·τ`), estimating directed
  information *along the propagation direction*,
- **BECAUSE** a glider carries information coherently at its velocity, so
  `I(source@offset ; dest-next | dest-past)` is high exactly when a coherent
  structure connects them, and low for chaos (no coherent velocity) and for
  frozen (no information). This is the occupant that should reproduce the eye.

## 3.5 Rotation and alphabet — an open empirical question (Joe, 2026-07-14)

§3 tacitly assumed a glider is a *same-value* diagonal. In a 256-valued (8-bit)
MetaCA rendered in greyscale we **cannot know in advance** whether gliders stay
one value or *rotate* — change value as they propagate while keeping a coherent
trajectory. Two facts shape the design:

- **TE is value-mapping-agnostic.** `I(source@offset ; dest-next | dest-past)`
  measures whether the source *reduces uncertainty* about the destination, not
  whether they carry the *same* symbol. A glider whose value maps `X → Y`
  consistently as it moves still scores high TE. So the estimator is already
  partly robust to rotation — it detects coherent *dependence*, not identity.
- **The alphabet decides which rotation is visible** (the `alphabet` fill of
  `paramHole`):
  - `bitplane` (binary, one plane) — estimable, but blind to a rotation that is
    not bit-aligned (a value cycle one plane reads as noise);
  - `fullCell` (256 symbols) — rotation-aware, but sample-starved (severe
    entropy-estimation bias);
  - `coarse` (a few bins over the 8-bit value) — a middle ground.

**Resolution: VERIFY answers it; do not assume.** The INSTANTIATE runs the
distance-TE occupant across alphabets. If `fullCell`/`coarse` distance-TE
satisfies `SeparatesEoC` and reproduces the eye ordering where `bitplane` does
not, **that is evidence the gliders rotate** (their coherence is not per-bit). If
all alphabets agree, they stay same-value. Either way the measure *reports* the
answer instead of presuming it — the honest form of "we can't know in advance."

## 4. Evaluator-blend = comb-fill

A blended evaluator ("3 AIS : 2 TE") is a `Fill` mixing two evaluator-occupants,
on **normalized** scores (each mapped frozen→0, complex-class→1 against the ECA
reference, per `M-metaca-search` §3.6). The blend weight is a `paramHole` fill,
so evaluator-blends are the *same* comb operation as generator-blends. The eye
calibrates the weight (human as xenotype).

## 5. Validation property (state it now, VERIFY later)

The evaluator-comb carries an R9-style property that the INSTANTIATE must
satisfy — stated in the DERIVE, not discovered after coding:

> **`SeparatesEoC occ`** — on the ECA reference set, `occ`'s score on the complex
> class (110/54/137) has a 95% lower bound strictly above the frozen and chaotic
> upper bounds.

`selfPast` (AIS) satisfies it; `nearestNeighbor` (nn-TE) provably does not
(chaotic 0.208 > complex 0.072). The distance-TE occupant is a *candidate* for
`SeparatesEoC` — and, additionally, must reproduce the **eye-calibration
ordering** (w=0.9 high, w=0.5 low on the stochastic sweep). No occupant is
accepted as a discriminator until it holds both.

## 6. INSTANTIATE plan (only after this DERIVE is approved)

1. `DarkTower/EvaluatorExample.lean` — the skeleton `BV` expr + `sourceHole`/
   `paramHole` `TypedHole`s + the three occupants (AIS, nn-TE, distance-TE) +
   `SeparatesEoC` as a `Prop`, mirroring `MetaCAExample.lean`. `lake build` green.
2. Clojure INSTANTIATE — the distance-TE estimator (offset along the glider
   velocity), refactoring the existing AIS/nn-TE code to expose the `sourceHole`
   seam so all three are one parameterized estimator, not three copies.
3. VERIFY — `SeparatesEoC` on the ECAs (recomputed independently) **and** the
   eye-calibration ordering on the sweep.
