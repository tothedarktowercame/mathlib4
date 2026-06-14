import Mathlib
import DarkTower.TypedHole
import DarkTower.Fill
import DarkTower.Comb
import DarkTower.Discharge
import DarkTower.ScopeQuery
import DarkTower.BV

/-!
# First-flights fill fold example

This file records the M-first-flights by-example for the fold grain of `fill`:
the cascade-selected graph rewrite that turns a sorry topology into a wiring
diagram.  This complements the atomic `PFunctor.comp` grain in `DarkTower.Fill`.

Grounding:
* `futon3c/holes/missions/M-typed-holes-example-first-flights.md`, especially
  section 4, names the two grains of fill: atomic polynomial substitution and
  cascade-driven graph-rewrite fold.
* `futon3c/holes/flights/first-flights-wiring.edn` records the triple
  `(typed hole arr-7535a5b6-e59, term flight-pretty-print+migration, wiring)`.
  Its boundary has a full `have-port` and a `want-port` whose satiety is
  `{:hungry-for :payoff}`.
* `futon3c/holes/flights/first-flights-cascade.edn` records the candidate
  pattern language, including `:differentiates` and `:jointly-with` edges.

The example is intentionally small: a four-checkpoint `BV.seq` slice for the
mined `:composes` chain, a `ScopeQuery` store for cascade selection, a
`BV.copar` witness for `:jointly-with`, and a `Fill`/`Discharge` witness that
the selected fold closes the payoff-hungry port.
-/

namespace DarkTower

open CategoryTheory

namespace FirstFlightsExample

/-- Checkpoints from the first-flights wiring slice. -/
inductive Checkpoint where
  | havePort
  | schemaV04
  | logicModel
  | substrateRoundtrip
  | prettyPrint
  | wantPort
  deriving DecidableEq, Repr

/-- A four-checkpoint slice of the mined `:composes` chain. -/
def checkpointChain : BV Checkpoint :=
  BV.seq (BV.atom Checkpoint.havePort)
    (BV.seq (BV.atom Checkpoint.schemaV04)
      (BV.seq (BV.atom Checkpoint.logicModel) (BV.atom Checkpoint.substrateRoundtrip)))

/-- A local left-associated prefix of the checkpoint chain. -/
def checkpointPrefixLeft : BV Checkpoint :=
  BV.seq
    (BV.seq (BV.atom Checkpoint.havePort) (BV.atom Checkpoint.schemaV04))
    (BV.atom Checkpoint.logicModel)

/-- The same prefix reassociated to the right. -/
def checkpointPrefixRight : BV Checkpoint :=
  BV.seq
    (BV.atom Checkpoint.havePort)
    (BV.seq (BV.atom Checkpoint.schemaV04) (BV.atom Checkpoint.logicModel))

/-- Directions available at the first-flights want-port. -/
inductive WantDirection where
  | payoff
  deriving DecidableEq, Repr

/-- The sorry topology: the want port is a typed hole hungry for payoff. -/
def wantPortHole : TypedHole where
  poly :=
    { A := Checkpoint
      B := fun _ => WantDirection }
  satiety := fun checkpoint =>
    if checkpoint = Checkpoint.wantPort then SatietyGrade.payoff else SatietyGrade.parse

/-- The folded topology: the former want port has received its payoff. -/
def foldedPort : TypedHole where
  poly :=
    { A := Checkpoint
      B := fun _ => WantDirection }
  satiety := fun checkpoint =>
    if checkpoint = Checkpoint.wantPort then SatietyGrade.canon else SatietyGrade.parse

/-- A position is hungry in this example exactly when its satiety asks for payoff. -/
def IsHungry (T : TypedHole) (checkpoint : T.poly.A) : Prop :=
  T.satiety checkpoint = SatietyGrade.payoff

/-- The mined checkpoint chain supports BV reassociation. -/
example : BV.Cong checkpointPrefixLeft checkpointPrefixRight :=
  BV.Cong.seq_assoc
    (BV.atom Checkpoint.havePort)
    (BV.atom Checkpoint.schemaV04)
    (BV.atom Checkpoint.logicModel)

/-- The want port exposes payoff-shaped typed holes. -/
example : wantPortHole.holeType Checkpoint.wantPort = WantDirection :=
  rfl

/-- Before the fold, the want port is hungry for payoff. -/
example : IsHungry wantPortHole Checkpoint.wantPort := by
  simp [IsHungry, wantPortHole]

/-- After the fold, the checkpoint is no longer hungry for payoff. -/
example : Not (IsHungry foldedPort Checkpoint.wantPort) := by
  simp [IsHungry, foldedPort]

/-- Cascade edge kinds used in the first-flights pattern language. -/
inductive EdgeKind where
  | differentiates
  | jointlyWith
  deriving DecidableEq, Repr

/-- Roles on cascade hyperedges. -/
inductive Role where
  | context
  | pattern
  deriving DecidableEq, Repr

/-- Candidate patterns from the cascade slice. -/
inductive Pattern where
  | structuredEvents
  | twoProjections
  | measurementWindow
  | noSelfCertification
  deriving DecidableEq, Repr

/-- The variable selected by answering the cascade query. -/
inductive Var where
  | selected
  deriving DecidableEq, Repr

/-- The tiny cascade signature. -/
def sig : ScopeQuery.Sig where
  Kind := EdgeKind
  Role := Role

instance : DecidableEq sig.Kind := by
  dsimp [sig]
  infer_instance

instance : DecidableEq sig.Role := by
  dsimp [sig]
  infer_instance

/-- A tiny store of candidate cascade edges. -/
def cascadeStore : ScopeQuery.Store sig Pattern :=
  [{ kind := EdgeKind.differentiates
     ends := [(Role.context, Pattern.structuredEvents), (Role.pattern, Pattern.twoProjections)] },
   { kind := EdgeKind.jointlyWith
     ends := [(Role.context, Pattern.twoProjections), (Role.pattern, Pattern.measurementWindow)] },
   { kind := EdgeKind.differentiates
     ends := [(Role.context, Pattern.noSelfCertification),
       (Role.pattern, Pattern.measurementWindow)] }]

/-- Select the pattern that differentiates structured events in this slice. -/
def selectedQuery : ScopeQuery.Query sig Pattern Var :=
  { kind := EdgeKind.differentiates
    ends := [(Role.context, Sum.inr Pattern.structuredEvents),
      (Role.pattern, Sum.inl Var.selected)] }

/-- The selected cascade filler. -/
def selectedBinding : ScopeQuery.Binding Var Pattern
  | Var.selected => some Pattern.twoProjections

/-- Selecting the cascade pattern is answering the query by finite fill. -/
example : ScopeQuery.answers selectedQuery cascadeStore = [selectedBinding] :=
  rfl

/-- The explicit `answers = fills` bridge for the selected cascade query. -/
example : ScopeQuery.answers selectedQuery cascadeStore =
    ScopeQuery.fills selectedQuery cascadeStore :=
  rfl

/-- The answer really selects the two-projections pattern. -/
example : (ScopeQuery.answers selectedQuery cascadeStore).map (fun binding => binding Var.selected) =
    [some Pattern.twoProjections] :=
  rfl

/--
The `:jointly-with` cascade edge is a `BV.copar`, exercising the connective that
the linear mined `:composes` chain cannot express.
-/
def jointlyWithPair : BV Pattern :=
  BV.copar (BV.atom Pattern.twoProjections) (BV.atom Pattern.measurementWindow)

/-- The `:jointly-with` pair is literally the copar pattern. -/
example : jointlyWithPair =
    BV.copar (BV.atom Pattern.twoProjections) (BV.atom Pattern.measurementWindow) :=
  rfl

/-- The payoff term supplied by the graph-rewrite fold. -/
inductive Payoff where
  | canonicalOrganOrder
  deriving DecidableEq, Repr

/-- The fold's operational discharge polarity: a query is answered by the selected fill. -/
def foldDischargeKind : DischargeKind :=
  DischargeKind.queryAnswer

/-- Filling the identity polynomial with the selected payoff returns the payoff. -/
example : Fill.I.get (Fill.I.mk Payoff.canonicalOrganOrder) =
    Payoff.canonicalOrganOrder :=
  rfl

/-- The first-flights fold uses the query-answer discharge reading. -/
example : foldDischargeKind = DischargeKind.queryAnswer :=
  rfl

#check checkpointChain
#check ScopeQuery.answers
#check jointlyWithPair
#check Fill.I.get

end FirstFlightsExample

end DarkTower
