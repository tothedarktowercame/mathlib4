# DarkTower-native AIF apparatus — compliance standard

**Purpose.** A protocol for building an active-inference (AIF) apparatus so that
it is a DarkTower object *from the start* — its control loop, its input
dependencies, and its validation properties are DarkTower/Lean constructs, not
prose that a formalism is bolted onto later. Target: the **MetaCA tokamak** (an
AIF controller ported into the MetaCA domain) and any future AIF port. The
reference exemplar is [`WMPipelineExample.lean`](./WMPipelineExample.lean) — the
War Machine flight as a DarkTower-native AIF loop. Primitives:
`BV`, `TypedHole`, `Fill`, `Comb`, `Coverage`, `Discharge`, `ScopeQuery`.

## The core claim

An AIF apparatus is a control loop that **perceives → evaluates expected free
energy → acts → learns**. *DarkTower-native* means five things:

1. the loop is a **`BV` process expression** over its stages;
2. every external dependency (observation/feed) is a **satiety-graded
   `TypedHole`**, so **starvation is a theorem**;
3. the EFE decomposition is **`copar` (⅋) gate legs** — non-signalling
   simultaneous readings, never sequenced;
4. the validation properties are **Lean theorems** a repair must flip;
5. completeness is a **`Coverage`** proof.

## Generators, evaluators, and the Tokamak are one comb

The generator / evaluator / controller distinction is **wiring**, not species:

- a **generator** is a comb `state → state` (produces behaviour;
  cf. `MetaCAExample.lean`);
- an **evaluator** is a comb `behaviour → score` (consumes behaviour — e.g. a
  spatial transfer-entropy discriminator);
- a **Tokamak** is this AIF loop — `perceive ◁ evaluate ◁ act ◁ learn`, with
  feedback — carrying **both** an evaluate-leg (`gateF`/`gateG`) and an act-leg
  (`enact`).

So the AIF loop is the **general** comb; a pure generator and a pure evaluator
are its degenerate cases (drop the evaluate-leg / drop the act-leg). The Tokamak
is therefore the **self-evaluating generator** — its free energy over what it
observes *is* the score of what it generates. Hand-crafted evaluators
(`behaviour → score`) are feed-forward and fit the current machinery; the
Tokamak is recurrent and is the construction that forces the open-diagram layer
(below). Build the tokamak as this general comb, with the CA-dynamic occupants
and the discriminators recognised as the same object with legs removed. `blend`
(fill-mixing) is one operation over all of them.

## Shared substrate — local causal states (for the AIF build team)

The DarkTower evaluator work is building the piece the tokamak's generative model
needs. **A local-causal-state model *is* an AIF generative model**: the causal
states are the minimal sufficient statistics of the past for predicting the future
— i.e. the belief-states a controller maintains. The evaluator uses them to detect
domains/particles (edge-of-chaos structure); the tokamak uses the same causal
states as beliefs. Two consumers, one substrate.

For the AIF build team, in order of readiness:

- **Spec (DERIVE, ready):** `DarkTower/EVALUATOR-SPEC.md` §3.9 — Rupe–Crutchfield
  local causal states (light-cones → CSSR clustering with a significance test →
  causal-state field → domains/particles), with the tokamak-reuse framing. §3.1–3.8
  are the surrounding evaluator-comb derivation.
- **Requirements (ready):** `futon5/data/particle-detection-SCOPE.md` — the exact
  CSSR / ε-machine / particle-tracking / boundary-audit requirements, and the
  evidence for *why* the tile/translation shortcuts fail (Rule 110).
- **Code (in flight):** `futon5/src/futon5/mmca/local_causal_states.clj` — a
  standalone, refactorable causal-state inference module (light-cones + CSSR +
  significance test), being built as shared substrate. Not yet committed; lands
  from the current evaluator slice. The reusability into the AIF generative model
  is an intended path, not a coincidence.

## Mapping — AIF feature → DarkTower construct

The AIF feature column follows the R1–R12 audit of the ants reference
implementation (`futon2/docs/ants-aif-audit.md`), the "modern AIF controller"
being ported.

| AIF feature | DarkTower construct | Requirement |
|---|---|---|
| the control cycle | `BV` expr, `◁` (`BV.seq`) spine | one tick = one BV process expression over a `Stage` enum |
| R1 belief state | a `Fill` / the value threaded through | belief = what fills the perception port; typed by `holeType` |
| R2 observation channels | a feed `TypedHole`, one port per channel | `satiety` records fed vs hungry per channel |
| R3/R4 predictive-coding + forward model | a BV sub-expression (the cascade) | perception/rollout is a stage or sub-flight; fixed-count micro-steps unroll as `seq` (see feedback note) |
| R5 EFE terms | `BV.copar` (⅋) gate legs | epistemic (ΔF) ⅋ pragmatic (ΔG) held simultaneous; extend to N legs for an N-term EFE |
| R6 softmax + abstain | a `select` stage + an abstain `Prop` | "abstain fires" is a provable condition |
| R7 adaptive precision | `Fill` parameters / graded `satiety` | precision enters as a fill or a satiety grade |
| R8 per-tick trace | a `trace` atom in the BV expr | present as a stage |
| R9 validation properties | **theorems** | starvation (`IsHungry`), conservation, coverage, abstain-fires — each a Lean theorem |
| R11 hierarchical composition | `Comb.comp` / nested `Fill` | sub-apparatus compose via comb composition |
| (completeness) | `Coverage` | discharge projections are all views of existing facets |
| (search, if any) | `ScopeQuery` | fill-enumeration from a store (`answers_eq_fills`) |

## The load-bearing invariants (what makes it native, not metaphor)

1. **Starvation is provable.** Every input feed is a satiety-graded `TypedHole`
   (cf. `gammaFeedHole`). A severed feed → a provable `IsHungry hole port`
   (`IsHungry T a := T.satiety a = SatietyGrade.payoff`). Repairing the feed
   flips the satiety to `canon`, turning the theorem into its negation
   (`¬ IsHungry`) — so a feed regression **breaks the build**. This is the single
   most important property: the apparatus can *prove* whether it is fed.
2. **EFE is non-signalling.** The epistemic and pragmatic legs are held by
   `BV.copar` (⅋), **not** `BV.seq`: they are independent readings of the same
   cascade and cannot signal one another. Never sequence ΔF before ΔG.
3. **Conservation is a theorem.** The control law conserves
   normalization/causality — the discard equation ↔ VFE normalization
   (`E-the-dark-tower-2` §4). State it and prove it.
4. **Coverage.** The apparatus's discharge/output projections are all views of
   existing facets — no orphan outputs — via `Coverage`.
5. **Repair-flips-the-theorem.** R9 properties are theorems whose truth tracks
   apparatus health; a fix must flip the relevant theorem (the FirstFlights
   idiom that `WMPipelineExample` demonstrates for γ-starvation).

## Feed-forward per tick vs. within-diagram feedback (the complexity boundary)

The CA-dynamics occupants (`MetaCAExample.lean`) are feed-forward
(`read ◁ combine ◁ mutate ◁ write`) and fit the current `Fill`/`BV` machinery
with **no** open-diagram layer. An AIF apparatus is richer (belief state,
recurrence, iterated precision), so this is where "more complex than the CA
examples" actually bites:

- **DEFAULT — model one tick as a feed-forward BV expression; recurrence is
  external.** This is exactly what `WMPipelineExample` does: one flight = one
  tick; the `learn → next wake` loop is external iteration, precisely like CA
  generations iterate the one-step object. Fixed-count inner loops (e.g. the 5
  predictive-coding micro-steps in `perceive`) **unroll** as a `seq` chain. This
  fits current machinery and should be the default.
- **FLAG — genuine within-diagram feedback** (a stage's output feeds an *earlier*
  open port of the *same* diagram; or a dynamic-count loop that cannot be
  unrolled) is where the deferred `Comb.lean` open-diagram (Roman coend) layer
  becomes load-bearing. The CA dynamics never needed it (all 9 are feed-forward);
  **the AIF tokamak is the likely first construction that does.** If so: STOP,
  record *which stage and why* in a committed note, and do **not** force it or
  edit `Comb.lean`. That report is the scoped trigger to finally build the
  open-diagram layer — a real result, not a failure.

## Compliance checklist (a tokamak is DarkTower-native iff)

- [ ] one tick = a `BV` process expression over a `Stage` enum (seq spine; EFE legs via `copar`)
- [ ] every observation/feed is a port on a satiety-graded `TypedHole`
- [ ] a severed feed is a provable `IsHungry`; the fed apparatus proves `¬ IsHungry`
- [ ] belief / policy / precision enter as `Fill`s with declared `holeType`
- [ ] R9 properties (starvation, conservation, coverage, abstain-fires) are Lean theorems
- [ ] `lake build DarkTower` exit 0; no `sorry` / `admit` / `axiom`
- [ ] recurrence is external (feed-forward per tick), OR the feedback need is reported as the open-diagram trigger
- [ ] the Clojure controller and the Lean object **agree**: the Lean `Stage`s mirror the controller's *actual* stages (a faithful mirror, never a plausible-looking stand-in — the same surface-contract fidelity we hold Codex ports to)

## Process for the porting agent

1. Port the AIF controller to the target domain in Clojure (ants → MetaCA) —
   the running apparatus.
2. In parallel, write `DarkTower/MetaCATokamakExample.lean` mirroring
   `WMPipelineExample`: the `Stage` enum, the `flight`/tick `BV` expr, the feed
   `TypedHole`(s), the EFE `copar` legs, and the R9 theorems.
3. Prove starvation + `¬ IsHungry`-when-fed for at least one real feed; prove
   `Coverage`; state conservation.
4. If a feedback need surfaces, stop and file the open-diagram trigger note
   (above) instead of forcing it.
5. Gate: `lake build DarkTower` exit 0, no cheats, Lean stages ≙ Clojure stages.
