import DarkTower.WarMachine.GOverCascades
import DarkTower.WarMachine.OuterCascadePolicyObjective

/-!
# Outer selection and canonical cascade G

Faithful comparison model for `outer_policy_objective/evaluate`: `outerG` is
lines 137--139 (risk + ambiguity - novelty), `outerObjective` is line 139
(gamma * G - lnE), and `minimumsBy` is lines 158--164/205--212: retain all
equal minima in menu order before the recorded uniform tie draw. The draw is a
valid slot into that retained list.

`canonicalSelection` consumes actual `compareAtHorizonN` output, dropping
refusals before comparison exactly as Clojure forms `assessed` at lines
153--164. Agreement requires successful canonical scores to equal outer G,
while one menu gamma and constant lnE make that order-equivalent to the outer
objective. -/

namespace DarkTower.WarMachine.Proof2.OuterSelectionCanonicalG

open DarkTower.WarMachine.CascadeCoApplyG
open DarkTower.WarMachine.CascadeCoApplyGNovelty

noncomputable section

abbrev Nats := ℝ

structure OuterPolicy where
  id : Nat
  risk : Nats
  ambiguity : Nats
  novelty : Nats
  lnE : Nats
  deriving DecidableEq

def outerG (p : OuterPolicy) : Nats := p.risk + p.ambiguity - p.novelty
def outerObjective (gamma : Nats) (p : OuterPolicy) : Nats := gamma * outerG p - p.lnE

def minimum? : List Nats → Option Nats
  | [] => none
  | x :: xs => some (xs.foldl min x)

/-- Equal minima, in input-menu order. -/
def minimumsBy (scores : List Nats) (ps : List OuterPolicy) : List OuterPolicy :=
  match minimum? scores with
  | none => []
  | some m => ((List.zip ps scores).filter (fun x => x.2 = m)).map Prod.fst

def outerSelection (gamma : Nats) (ps : List OuterPolicy) : List OuterPolicy :=
  ps.filter fun p => ∀ q ∈ ps, outerObjective gamma p ≤ outerObjective gamma q

/-- The recorded Clojure draw is valid exactly when it indexes the
equal-minimum frontier. Uniformity is an obligation of the producer, not a
claim about Lean randomness. -/
structure TieDraw (tied : List OuterPolicy) where
  slot : Nat
  valid : slot < tied.length

def applyTieDraw (tied : List OuterPolicy) (draw : TieDraw tied) : OuterPolicy :=
  tied.get ⟨draw.slot, draw.valid⟩

def assessedPairs (ps : List OuterPolicy) (scores : List (Except CascadeCoApplyG.Refusal Nats)) :
    List (OuterPolicy × Nats) :=
  (List.zip ps scores).filterMap fun x => match x.2 with | .ok n => some (x.1, n) | .error _ => none

noncomputable def canonicalSelection {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (H : Nat) (cands : List (CandidateN ι V))
    (ps : List OuterPolicy) : List OuterPolicy :=
  let assessed := assessedPairs ps (compareAtHorizonN H cands)
  (assessed.filter fun x => ∀ y ∈ assessed, x.2 ≤ y.2).map Prod.fst

/-- A refused singleton menu leaves nothing to select. -/
theorem refused_dropped (p : OuterPolicy) (r : CascadeCoApplyG.Refusal) :
    p ∉ (assessedPairs [p] [.error r]).map Prod.fst := by simp [assessedPairs]

theorem objective_order_iff_G_order (gamma k : Nats) (hgamma : 0 < gamma)
    (p q : OuterPolicy) (hp : p.lnE = k) (hq : q.lnE = k) :
    outerObjective gamma p ≤ outerObjective gamma q ↔ outerG p ≤ outerG q := by
  rw [outerObjective, outerObjective, hp, hq]
  constructor <;> intro h <;> nlinarith

/-- On a fixed menu gamma and a constant lnE, the Clojure frontier is precisely
the canonical-G frontier. -/
theorem outerSelection_eq_G_frontier (gamma k : Nats) (hgamma : 0 < gamma)
    (ps : List OuterPolicy) (hlnE : ∀ p ∈ ps, p.lnE = k) :
    outerSelection gamma ps = ps.filter fun p => ∀ q ∈ ps, outerG p ≤ outerG q := by
  unfold outerSelection
  apply List.filter_congr
  intro p hp
  apply decide_eq_decide.mpr
  constructor <;> intro h q hq
  · exact (objective_order_iff_G_order gamma k hgamma p q (hlnE p hp) (hlnE q hq)).mp (h q hq)
  · exact (objective_order_iff_G_order gamma k hgamma p q (hlnE p hp) (hlnE q hq)).mpr (h q hq)

/-- On any menu, an assessed pair is exactly a policy aligned with a successful
canonical score: a refusal is never converted into a score. -/
theorem mem_assessedPairs (ps : List OuterPolicy)
    (scores : List (Except CascadeCoApplyG.Refusal Nats)) (x : OuterPolicy × Nats) :
    x ∈ assessedPairs ps scores ↔ (x.1, Except.ok x.2) ∈ List.zip ps scores := by
  obtain ⟨p, n⟩ := x
  simp only [assessedPairs, List.mem_filterMap]
  constructor
  · rintro ⟨⟨q, s⟩, hmem, hs⟩
    cases s <;> simp_all
  · intro h
    exact ⟨(p, .ok n), h, rfl⟩

theorem assessedPairs_ok (ps : List OuterPolicy) (f : OuterPolicy → Nats) :
    assessedPairs ps (ps.map fun p => Except.ok (f p)) = ps.map fun p => (p, f p) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [assessedPairs, List.map_cons, List.zip_cons_cons, List.filterMap_cons] at ih ⊢
    rw [ih]

/-- An aligned successful canonical score list equal to outer G, with one
positive menu gamma and constant lnE, has exactly the outer tie frontier, so the
same valid recorded draw slot chooses the same policy. -/
theorem canonicalSelection_agrees {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (H : Nat) (cands : List (CandidateN ι V))
    (ps : List OuterPolicy) (gamma k : Nats) (hgamma : 0 < gamma)
    (hlnE : ∀ p ∈ ps, p.lnE = k)
    (h : compareAtHorizonN H cands = ps.map fun p => Except.ok (outerG p)) :
    canonicalSelection H cands ps = outerSelection gamma ps := by
  rw [outerSelection_eq_G_frontier gamma k hgamma ps hlnE]
  simp only [canonicalSelection, h, assessedPairs_ok, List.filter_map, List.map_map]
  simp [Function.comp_def]

/-- Equal canonical G values can yield a different outer choice because today's
selector additionally subtracts lnE. -/
def counterA : OuterPolicy := ⟨1, 1, 0, 0, 0⟩
def counterB : OuterPolicy := ⟨2, 1, 0, 0, 1⟩

theorem counterexample_same_G : outerG counterA = outerG counterB := by
  norm_num [outerG, counterA, counterB]

theorem counterexample_outer_prefers_B :
    outerObjective 1 counterB < outerObjective 1 counterA := by
  norm_num [outerObjective, outerG, counterA, counterB]

theorem counterexample_outer_frontier : outerSelection 1 [counterA, counterB] = [counterB] := by
  norm_num [outerSelection, outerObjective, outerG, counterA, counterB]

theorem counterexample_G_frontier :
    minimumsBy [outerG counterA, outerG counterB] [counterA, counterB] = [counterA, counterB] := by
  norm_num [minimumsBy, minimum?, outerG, counterA, counterB]

#print axioms refused_dropped
#print axioms mem_assessedPairs
#print axioms canonicalSelection_agrees
#print axioms objective_order_iff_G_order
#print axioms outerSelection_eq_G_frontier
#print axioms counterexample_same_G
#print axioms counterexample_outer_prefers_B
#print axioms counterexample_outer_frontier
#print axioms counterexample_G_frontier

end

end DarkTower.WarMachine.Proof2.OuterSelectionCanonicalG
