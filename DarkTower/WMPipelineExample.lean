import Mathlib
import DarkTower.TypedHole
import DarkTower.BV

/-!
# The War Machine pipeline as a DarkTower object

Operator direction (2026-07-05): the pipeline we are building needs *a wiring
diagram* in the proper formalism — because a checkable wiring makes severed
feeds obvious.  The motivating incident, same day: the classical fold was
retired as a ΔG route (a correct ruling), which *silently severed* γ's
expected-ΔG feed; γ coasted for hours before a cosmetic task tripped over it.

This file states the pipeline in the DarkTower vocabulary:

* the flight is a `BV` process expression over `Stage` — sequencing by
  `BV.seq` (◁), and the act-gate's two evaluations held together by
  `BV.copar` (⅋): the argument's quality (ΔF) and the plan's promise (ΔG) are
  simultaneous readings of one cascade, exactly the scope/organism idiom of
  `MissionExample.readings`;
* the feeds into γ are a `TypedHole`: positions are γ's consumer ports,
  directions are what can fill them, and satiety grades record fed vs hungry;
* **the starvation is a theorem**: `IsHungry gammaFeedHole GammaPort.expectedDG`
  holds — and the repair (escrow ΔG feeding the expected leg, dispatched
  2026-07-05) will be the edit that flips that satiety grade and *breaks this
  example*, which is the point: the formal file must be updated in the same
  commit as the rewire, or the build fails.  A wiring diagram that compiles is
  a wiring diagram someone must keep true.

Grounding: `futon2/holes/wm-pipeline-wiring.edn` (the operational map this
formalizes), `futon2/holes/flight-pipeline-cards-ii.html` (the pre-registered
v2 shapes), `E-live-loop-3.md` (the rulings cited).
-/

namespace DarkTower

namespace WMPipelineExample

/-- Stages of one flight (pipeline cards II, cards 1–9). -/
inductive Stage where
  | wake
  | judge
  | psi
  | cascade
  | gateF      -- the epistemic leg: ΔF over the argument
  | gateG      -- the pragmatic leg: ΔG over the plan
  | gate       -- the ∧
  | select
  | enact
  | trace
  | learn
  deriving DecidableEq, Repr

/--
One flight as a BV process expression: a `seq` spine, with the two gate legs
held simultaneous by `copar` — ΔF and ΔG are independent readings of the same
cascade, neither may signal the other (the AND-gate demands both, separately).
-/
def flight : BV Stage :=
  BV.seq (BV.atom Stage.wake)
    (BV.seq (BV.atom Stage.judge)
      (BV.seq (BV.atom Stage.psi)
        (BV.seq (BV.atom Stage.cascade)
          (BV.seq (BV.copar (BV.atom Stage.gateF) (BV.atom Stage.gateG))
            (BV.seq (BV.atom Stage.gate)
              (BV.seq (BV.atom Stage.select)
                (BV.seq (BV.atom Stage.enact)
                  (BV.seq (BV.atom Stage.trace) (BV.atom Stage.learn)))))))))

/-- A three-stage prefix, left-associated. -/
def wakeJudgePsiLeft : BV Stage :=
  BV.seq (BV.seq (BV.atom Stage.wake) (BV.atom Stage.judge)) (BV.atom Stage.psi)

/-- The reassociated form. -/
def wakeJudgePsiRight : BV Stage :=
  BV.seq (BV.atom Stage.wake) (BV.seq (BV.atom Stage.judge) (BV.atom Stage.psi))

/-- The flight prefix reassociates by BV structural congruence. -/
example : BV.Cong wakeJudgePsiLeft wakeJudgePsiRight :=
  BV.Cong.seq_assoc (BV.atom Stage.wake) (BV.atom Stage.judge) (BV.atom Stage.psi)

/-- ΔG sources in the reconciliation (pipeline card 6). -/
inductive DGSource where
  | rollout    -- depth-1 valuation (the depth>1 search is retired on theory)
  | classical  -- the 10-entry rule table: RETIRED as a route, 2026-07-05
  | escrow     -- the LLM fold's pinned deposits: the ΔG economy
  deriving DecidableEq, Repr

/-- The operator's ruling, as a predicate: which sources are retired routes. -/
def retiredRoute : DGSource → Prop
  | DGSource.classical => True
  | _ => False

/-- The escrow is not a retired route. -/
example : ¬ retiredRoute DGSource.escrow := by
  simp [retiredRoute]

/-- γ's consumer ports (the learning stage's inputs). -/
inductive GammaPort where
  | expectedDG   -- the promise: what the plan said it would close
  | realizedDG   -- the outcome: what the executor actually reproduced
  deriving DecidableEq, Repr

/-- What can fill each γ port. -/
inductive GammaFeed where
  | fromSource (s : DGSource)  -- an expected-ΔG feed, tagged by its source
  | fromExecutor               -- the realized leg: the deterministic executor
  deriving DecidableEq, Repr

/--
γ's feeds as a typed-hole interface.  Satiety records the live wiring as of
2026-07-05, post-classical-retirement, pre-repair:

* `realizedDG` is FED (the executor edge is live) — graded `canon`;
* `expectedDG` is HUNGRY — its only live feed was the classical fold's ΔG,
  severed by the retirement ruling; graded `payoff` (the hungry grade).

THE CONTRACT OF THIS FILE: when the repair lands (escrow ΔG → expected leg),
this satiety must flip to `canon` in the same commit — the `IsHungry` example
below will fail to compile until it is rewritten as its negation, forcing the
formal wiring to track the real one.
-/
def gammaFeedHole : TypedHole where
  poly :=
    { A := GammaPort
      B := fun _ => GammaFeed }
  satiety := fun port =>
    match port with
    | GammaPort.expectedDG => SatietyGrade.payoff
    | GammaPort.realizedDG => SatietyGrade.canon

/-- A port is hungry when its satiety is the payoff grade (FirstFlights idiom). -/
def IsHungry (T : TypedHole) (a : T.poly.A) : Prop :=
  T.satiety a = SatietyGrade.payoff

/-- **The γ starvation, as a theorem.**  The expected-ΔG port is hungry:
its classical feed was severed by the retirement ruling and the escrow
repair has not yet landed.  This example is MEANT to be broken by the
repair commit. -/
example : IsHungry gammaFeedHole GammaPort.expectedDG := by
  simp [IsHungry, gammaFeedHole]

/-- The realized leg is fed — the executor edge survived the ruling. -/
example : ¬ IsHungry gammaFeedHole GammaPort.realizedDG := by
  simp [IsHungry, gammaFeedHole]

/-- Both γ ports accept `GammaFeed` directions (the interface types check). -/
example : gammaFeedHole.holeType GammaPort.expectedDG = GammaFeed :=
  rfl

end WMPipelineExample

end DarkTower
