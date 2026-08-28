/-!
# Cascade descent order

This standalone module introduces relation vocabulary because the existing
WarMachine families concern gain-chain records, not order structure.  It models
no probability, overlap, wiring, or fold behaviour.

The refusing witness is the two-edge cycle in
`data/wm-full-loop/wm-outer-loop-40-v1/attempt-001/003-construction.edn`,
recorded 2026-07-14.  Its carrier also contains the disconnected
`agent/sense-deliberate-act` pattern.  The accepting witness is the one-edge
descent in `attempt-008/003-construction.edn`, recorded 2026-07-16.
-/

universe u

inductive Reach {α : Type u} (r : α → α → Prop) : α → α → Prop where
  | single : r a b → Reach r a b
  | tail : Reach r a b → r b c → Reach r a c

def acyclicDescent {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ x, ¬ Reach r x x

def Below {α : Type u} (r : α → α → Prop) (a b : α) : Prop :=
  a = b ∨ Reach r a b

def IsMeet {α : Type u} (r : α → α → Prop) (a b m : α) : Prop :=
  Below r m a ∧ Below r m b ∧
    ∀ z, Below r z a → Below r z b → Below r z m

def hasMeets {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ a b, ∃ m, IsMeet r a b m

theorem reach_increases_rank {α : Type u} (r : α → α → Prop)
    (rank : α → Nat) (edge_increases : ∀ a b, r a b → rank a < rank b)
    {a b : α} (path : Reach r a b) : rank a < rank b := by
  induction path with
  | single edge => exact edge_increases _ _ edge
  | tail path edge ih => exact Nat.lt_trans ih (edge_increases _ _ edge)

theorem acyclic_of_increasing_rank {α : Type u} (r : α → α → Prop)
    (rank : α → Nat) (edge_increases : ∀ a b, r a b → rank a < rank b) :
    acyclicDescent r := by
  intro x path
  exact (Nat.lt_irrefl (rank x))
    (reach_increases_rank r rank edge_increases path)

inductive Attempt001Pattern where
  | agentSenseDeliberateAct
  | hexagram43Guai
  | hexagram44Gou
  deriving DecidableEq

open Attempt001Pattern

def attempt001Descent : Attempt001Pattern → Attempt001Pattern → Prop
  | hexagram43Guai, hexagram44Gou => True
  | hexagram44Gou, hexagram43Guai => True
  | _, _ => False

def attempt001OneWay : Attempt001Pattern → Attempt001Pattern → Prop
  | hexagram43Guai, hexagram44Gou => True
  | _, _ => False

theorem attempt001_one_way_edge {a b : Attempt001Pattern}
    (edge : attempt001OneWay a b) :
    a = hexagram43Guai ∧ b = hexagram44Gou := by
  cases a <;> cases b <;> simp_all [attempt001OneWay]

theorem attempt001_2026_07_14_two_cycle_is_refused :
    ¬ acyclicDescent attempt001Descent := by
  intro acyclic
  apply acyclic hexagram43Guai
  exact Reach.tail
    (Reach.single (r := attempt001Descent) (a := hexagram43Guai)
      (b := hexagram44Gou) trivial)
    trivial

theorem attempt001_one_way_reach {a b : Attempt001Pattern}
    (path : Reach attempt001OneWay a b) :
    a = hexagram43Guai ∧ b = hexagram44Gou := by
  induction path with
  | single edge =>
      exact attempt001_one_way_edge edge
  | tail path edge ih =>
      have edgeShape := attempt001_one_way_edge edge
      have impossible : hexagram44Gou = hexagram43Guai :=
        ih.2.symm.trans edgeShape.1
      contradiction

theorem dropping_reverse_edge_is_acyclic_but_not_a_semilattice :
    acyclicDescent attempt001OneWay ∧ ¬ hasMeets attempt001OneWay := by
  constructor
  · apply acyclic_of_increasing_rank attempt001OneWay
      (fun x => match x with
        | Attempt001Pattern.agentSenseDeliberateAct => 0
        | Attempt001Pattern.hexagram43Guai => 1
        | Attempt001Pattern.hexagram44Gou => 2)
    intro a b edge
    cases a <;> cases b <;> simp [attempt001OneWay] at edge ⊢
  · intro meets
    obtain ⟨m, hm⟩ := meets agentSenseDeliberateAct hexagram43Guai
    rcases hm with ⟨ma, mg, _⟩
    cases m with
    | agentSenseDeliberateAct =>
        rcases mg with h | path
        · contradiction
        · have shape := attempt001_one_way_reach path
          simp at shape
    | hexagram43Guai =>
        rcases ma with h | path
        · contradiction
        · have shape := attempt001_one_way_reach path
          simp at shape
    | hexagram44Gou =>
        rcases ma with h | path
        · contradiction
        · have shape := attempt001_one_way_reach path
          simp at shape

inductive Attempt008Pattern where
  | agentSenseDeliberateAct
  | hexagram05Xu
  | hexagram10Lu
  deriving DecidableEq

open Attempt008Pattern

def attempt008Descent : Attempt008Pattern → Attempt008Pattern → Prop
  | hexagram10Lu, hexagram05Xu => True
  | _, _ => False

theorem attempt008_2026_07_16_descent_is_accepted :
    acyclicDescent attempt008Descent := by
  apply acyclic_of_increasing_rank attempt008Descent
      (fun x => match x with
        | Attempt008Pattern.agentSenseDeliberateAct => 0
        | Attempt008Pattern.hexagram10Lu => 1
        | Attempt008Pattern.hexagram05Xu => 2)
  intro a b edge
  cases a <;> cases b <;> simp [attempt008Descent] at edge ⊢

#print axioms attempt001_2026_07_14_two_cycle_is_refused
#print axioms dropping_reverse_edge_is_acyclic_but_not_a_semilattice
#print axioms attempt008_2026_07_16_descent_is_accepted
