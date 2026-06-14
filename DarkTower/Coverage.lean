import DarkTower.TypedHole
import DarkTower.Fill
import DarkTower.Comb
import DarkTower.Discharge
import DarkTower.ScopeQuery

/-!
# Coverage certificate for typed-hole projections

This file records the design certificate for the six typed-hole discharge
projections used by the DarkTower/futon typed-hole mission.  The point is not to
add a seventh fill operation.  Each projection is classified as a view of one of
the existing DarkTower facets:

* polynomial substitution `Fill.fill` / `PFunctor.comp`;
* the comonad counit `Discharge.filled`;
* dependent-lens composition `Comb.comp` into the identity fill interface;
* finite scope-query answering `ScopeQuery.fills`;
* a `TypedHole` node's `SatietyGrade` projection.

Grounding anchors:
* Niu--Spivak, *Polynomial Functors: A Mathematical Theory of Interaction*,
  arXiv:2312.00990, for polynomial positions/directions and dependent-lens
  morphisms.
* Gambino--Kock, *Polynomial functors and polynomial monads*, for polynomial
  substitution/composition.
* Eilenberg--Moore, *Adjoint functors and triples*, and the nLab pages
  "comonad" / "coalgebra over a comonad", for the counit reading used by
  `Discharge.filled`.
* Mathlib anchors: `PFunctor.comp`, `CategoryTheory.Comonad`, and
  `CategoryTheory.Comonad.Coalgebra`.
-/

namespace DarkTower

open CategoryTheory

universe u v uA uB uAP uBP uAQ uBQ uAR uBR uK uR uN uV

/-- The six operational projections whose coverage is certified here. -/
inductive Projection where
  /-- DERIVE: cascade-feed/mining — a hungry mined node filled by satiety. -/
  | cascadeFeed
  /-- DERIVE: discharge/proof — a `sorry` filled by a proof. -/
  | discharge
  /-- DERIVE: ground/symbol — an ungrounded symbol filled by a binder. -/
  | ground
  /-- DERIVE: compose/comb — a comb hole filled by a `:composes` edge. -/
  | compose
  /-- DERIVE: answer/query — a scope hole filled by a store binding. -/
  | answer
  /-- DERIVE: reply/bell — a query bell filled by an answer bell. -/
  | reply
  deriving DecidableEq, Fintype, Repr

/-- Existing DarkTower fill facets through which the projections route. -/
inductive FillFacet where
  /-- A `TypedHole.satiety` / `SatietyGrade` node view. -/
  | satiety
  /-- A comonad-counit discharge at the given DarkTower polarity. -/
  | counit (kind : DischargeKind)
  /-- A dependent-lens/comb composition facet. -/
  | comb
  /-- A finite scope-query fill facet. -/
  | scopeQuery
  deriving DecidableEq

/--
Total classifier from each projection to its existing fill facet.

The match has one branch for each `Projection` constructor and no catch-all.  If
a seventh projection is added, this definition stops compiling until the new
case is classified.
-/
def fillFacet : Projection → FillFacet
  | Projection.cascadeFeed => FillFacet.satiety
  | Projection.discharge => FillFacet.counit DischargeKind.sorryProof
  | Projection.ground => FillFacet.counit DischargeKind.ungroundedBinder
  | Projection.compose => FillFacet.comb
  | Projection.answer => FillFacet.scopeQuery
  | Projection.reply => FillFacet.counit DischargeKind.queryAnswer

/-- Exhaustiveness certificate: the projection type has exactly the six constructors above. -/
theorem noOrphan : Fintype.card Projection = 6 := by
  rfl

/-- Every projection is assigned an existing fill facet by the total classifier. -/
theorem coverageComplete (p : Projection) : ∃ facet : FillFacet, fillFacet p = facet :=
  ⟨fillFacet p, rfl⟩

/-- Cascade-feed reads the existing `TypedHole.satiety` grade of a typed-hole node. -/
theorem cascadeFeed_routes_through_satiety (T : TypedHole.{uA, uB})
    (grade : SatietyGrade) (a : T.nodesBySatiety grade) :
    T.satiety a.1 = grade :=
  a.2

/-- Proof discharge routes through the existing comonad counit `Discharge.filled`. -/
theorem discharge_routes_through_filled {C : Type u} [Category.{v} C] {G : Comonad C}
    (D : Discharge G) (_h : D.kind = DischargeKind.sorryProof) :
    D.opened ≫ D.filled = 𝟙 D.carrier.A :=
  Discharge.open_filled D

/-- Symbol grounding routes through the same existing comonad counit. -/
theorem ground_routes_through_filled {C : Type u} [Category.{v} C] {G : Comonad C}
    (D : Discharge G) (_h : D.kind = DischargeKind.ungroundedBinder) :
    D.opened ≫ D.filled = 𝟙 D.carrier.A :=
  Discharge.open_filled D

/-- Bell reply routes through the same existing comonad counit. -/
theorem reply_routes_through_filled {C : Type u} [Category.{v} C] {G : Comonad C}
    (D : Discharge G) (_h : D.kind = DischargeKind.queryAnswer) :
    D.opened ≫ D.filled = 𝟙 D.carrier.A :=
  Discharge.open_filled D

/-- Compose/comb uses the existing dependent-lens composition operator. -/
theorem compose_routes_through_comb_comp
    {P : PFunctor.{uAP, uBP}} {Q : PFunctor.{uAQ, uBQ}} {R : PFunctor.{uAR, uBR}}
    (f : Comb P Q) (g : Comb Q R) (a : P.A) :
    (Comb.comp f g).onPos a = g.onPos (f.onPos a) :=
  Comb.comp_onPos f g a

/-- The direction side of compose/comb is the existing `Comb.comp` backward map. -/
theorem compose_direction_routes_through_comb_comp
    {P : PFunctor.{uAP, uBP}} {Q : PFunctor.{uAQ, uBQ}} {R : PFunctor.{uAR, uBR}}
    (f : Comb P Q) (g : Comb Q R) (a : P.A)
    (dir : R.B (g.onPos (f.onPos a))) :
    (Comb.comp f g).onDir a dir = f.onDir a (g.onDir (f.onPos a) dir) :=
  Comb.comp_onDir f g a dir

/-- Answer/query reuses `ScopeQuery.answers_eq_fills`: answers are fills. -/
theorem answer_routes_through_fills {S : ScopeQuery.Sig.{uK, uR}} {N : Type uN}
    {V : Type uV} [DecidableEq S.Kind] [DecidableEq S.Role] [DecidableEq N]
    [DecidableEq V] (q : ScopeQuery.Query S N V) (db : ScopeQuery.Store S N) :
    ScopeQuery.answers q db = ScopeQuery.fills q db :=
  ScopeQuery.answers_eq_fills q db

/-- The query comb points from `Fill.I` into the query's hole polynomial. -/
theorem answer_queryComb_routes_from_fill_identity {S : ScopeQuery.Sig.{uK, uR}}
    {N : Type uN} {V : Type uV} (q : ScopeQuery.Query S N V) :
    (ScopeQuery.queryComb q).onPos PUnit.unit = PUnit.unit :=
  rfl

/-- The classifier sends each constructor to the facet claimed by the design certificate. -/
theorem coverageComplete_by_cases :
    fillFacet Projection.cascadeFeed = FillFacet.satiety ∧
    fillFacet Projection.discharge = FillFacet.counit DischargeKind.sorryProof ∧
    fillFacet Projection.ground = FillFacet.counit DischargeKind.ungroundedBinder ∧
    fillFacet Projection.compose = FillFacet.comb ∧
    fillFacet Projection.answer = FillFacet.scopeQuery ∧
    fillFacet Projection.reply = FillFacet.counit DischargeKind.queryAnswer := by
  simp [fillFacet]

#print axioms DarkTower.noOrphan
#print axioms DarkTower.coverageComplete
#print axioms DarkTower.coverageComplete_by_cases
#print axioms DarkTower.cascadeFeed_routes_through_satiety
#print axioms DarkTower.discharge_routes_through_filled
#print axioms DarkTower.ground_routes_through_filled
#print axioms DarkTower.reply_routes_through_filled
#print axioms DarkTower.compose_routes_through_comb_comp
#print axioms DarkTower.compose_direction_routes_through_comb_comp
#print axioms DarkTower.answer_routes_through_fills
#print axioms DarkTower.answer_queryComb_routes_from_fill_identity

end DarkTower
