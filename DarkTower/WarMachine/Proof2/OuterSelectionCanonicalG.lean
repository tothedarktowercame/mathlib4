import DarkTower.WarMachine.GOverCascades
import DarkTower.WarMachine.OuterCascadePolicyObjective

/-!
# Outer selection and canonical cascade G

Faithful comparison model for `outer_policy_objective/evaluate`: `outerG` is
lines 137--139 (risk + ambiguity - novelty), `outerObjective` is line 139
(gamma * G - lnE), and `minimumsBy` is lines 158--164/205--212: retain all
equal minima in menu order before the recorded uniform tie draw. The draw is a
valid slot into that retained list.

`canonicalSelection` consumes actual `compareAtHorizonN` output. Agreement
requires every canonical score to succeed and equal the outer *objective*, not
merely the outer G term. -/

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
  gamma : Nats
  deriving DecidableEq

def outerG (p : OuterPolicy) : Nats := p.risk + p.ambiguity - p.novelty
def outerObjective (p : OuterPolicy) : Nats := p.gamma * outerG p - p.lnE

def minimum? : List Nats → Option Nats
  | [] => none
  | x :: xs => some (xs.foldl min x)

/-- Equal minima, in input-menu order. -/
def minimumsBy (scores : List Nats) (ps : List OuterPolicy) : List OuterPolicy :=
  match minimum? scores with
  | none => []
  | some m => ((List.zip ps scores).filter (fun x => x.2 = m)).map Prod.fst

def outerSelection (ps : List OuterPolicy) : List OuterPolicy :=
  minimumsBy (ps.map outerObjective) ps

/-- The recorded Clojure draw is valid exactly when it indexes the
equal-minimum frontier. Uniformity is an obligation of the producer, not a
claim about Lean randomness. -/
structure TieDraw (tied : List OuterPolicy) where
  slot : Nat
  valid : slot < tied.length

def applyTieDraw (tied : List OuterPolicy) (draw : TieDraw tied) : OuterPolicy :=
  tied.get ⟨draw.slot, draw.valid⟩

noncomputable def canonicalSelection {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (H : Nat) (cands : List (CandidateN ι V))
    (ps : List OuterPolicy) : List OuterPolicy :=
  minimumsBy (compareAtHorizonN H cands |>.map (fun s => match s with | .ok x => x | .error _ => 0)) ps

/-- An aligned successful canonical score list has exactly the outer tie
frontier, so the same valid recorded draw slot chooses the same policy. -/
theorem canonicalSelection_agrees {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (H : Nat) (cands : List (CandidateN ι V))
    (ps : List OuterPolicy)
    (h : compareAtHorizonN H cands = ps.map (fun p => Except.ok (outerObjective p))) :
    canonicalSelection H cands ps = outerSelection ps := by
  simp only [canonicalSelection, outerSelection, h, List.map_map]
  rfl

/-- Equal canonical G values can yield a different outer choice because today's
selector additionally subtracts lnE. -/
def counterA : OuterPolicy := ⟨1, 1, 0, 0, 0, 1⟩
def counterB : OuterPolicy := ⟨2, 1, 0, 0, 1, 1⟩

theorem counterexample_same_G : outerG counterA = outerG counterB := by
  norm_num [outerG, counterA, counterB]

theorem counterexample_outer_prefers_B :
    outerObjective counterB < outerObjective counterA := by
  norm_num [outerObjective, outerG, counterA, counterB]

theorem counterexample_outer_frontier : outerSelection [counterA, counterB] = [counterB] := by
  norm_num [outerSelection, minimumsBy, minimum?, outerObjective, outerG, counterA, counterB]

theorem counterexample_G_frontier :
    minimumsBy [outerG counterA, outerG counterB] [counterA, counterB] = [counterA, counterB] := by
  norm_num [minimumsBy, minimum?, outerG, counterA, counterB]

#print axioms canonicalSelection_agrees
#print axioms counterexample_same_G
#print axioms counterexample_outer_prefers_B
#print axioms counterexample_outer_frontier
#print axioms counterexample_G_frontier

end

end DarkTower.WarMachine.Proof2.OuterSelectionCanonicalG
