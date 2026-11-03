import DarkTower.WarMachine.R20Step

/-!
# Outer selection as an argumentation frame

This is the argument reading computed by
`argument-selection-2026-11-03-561c5ec3.edn`: lower `G` is preferred, attacks
from a worse (higher-`G`) argument against a better argument do not defeat,
and acceptability is iterated from the empty set to approximate the grounded
extension.

`G` is represented by `ℚ`, rather than `Float`.  The emitted decimal scores
therefore remain exact, ordered, and reducible by `native_decide`.  As in the
Babashka producer, attacks are between distinct arguments; a reflexive attack
is not a defeat.  An attack naming an absent argument is also not a defeat
(the producer constructs attacks only after constructing all arguments).
-/

namespace DarkTower.WarMachine.SelectionArgument

structure Argument where
  id : String
  G : ℚ
  deriving DecidableEq, Repr

structure Attack where
  src : String
  dst : String
  deriving DecidableEq, Repr

def argument? (args : List Argument) (id : String) : Option Argument :=
  match args with
  | [] => none
  | a :: rest => if a.id = id then some a else argument? rest id

/-- Preference-based defeat: an attack succeeds unless its target has lower G. -/
def defeats (args : List Argument) (attack : Attack) : Bool :=
  if attack.src = attack.dst then false
  else
    match argument? args attack.src, argument? args attack.dst with
    | some src, some dst => !(dst.G < src.G)
    | _, _ => false

def defeaters (args : List Argument) (attacks : List Attack) (id : String) : List String :=
  (attacks.filter fun attack => attack.dst = id && defeats args attack).map (·.src)

/-- Every successful attacker is itself successfully attacked by a member of `S`. -/
def acceptable (args : List Argument) (attacks : List Attack)
    (S : List String) (id : String) : Bool :=
  (defeaters args attacks id).all fun attacker =>
    S.any fun defender =>
      attacks.any fun attack =>
        attack.src = defender && attack.dst = attacker && defeats args attack

def groundedStep (args : List Argument) (attacks : List Attack)
    (S : List String) : List String :=
  (args.filter fun argument => acceptable args attacks S argument.id).map (·.id)

def iterateGrounded (args : List Argument) (attacks : List Attack) :
    ℕ → List String → List String
  | 0, S => S
  | n + 1, S => iterateGrounded args attacks n (groundedStep args attacks S)

/-- `args.length + 1` iterations suffice for this finite carrier. -/
def grounded (args : List Argument) (attacks : List Attack) : List String :=
  iterateGrounded args attacks (args.length + 1) []

def StrictMinimum (args : List Argument) (a : Argument) : Prop :=
  a ∈ args ∧
    argument? args a.id = some a ∧
    ∀ id b, argument? args id = some b → id ≠ a.id → a.G < b.G

private theorem argument?_of_strictMinimum {args : List Argument} {a : Argument}
    (minimum : StrictMinimum args a) : argument? args a.id = some a := by
  exact minimum.2.1

private theorem minimum_not_defeated {args : List Argument} {a : Argument}
    (minimum : StrictMinimum args a) (attack : Attack) (target : attack.dst = a.id) :
    defeats args attack = false := by
  simp only [defeats]
  split
  · rfl
  · rw [target, argument?_of_strictMinimum minimum]
    cases source : argument? args attack.src with
    | none => rfl
    | some b =>
      have distinct : attack.src ≠ a.id := by
        intro equal
        apply ‹attack.src ≠ attack.dst›
        rw [equal, target]
      have lower := minimum.2.2 attack.src b source distinct
      simp [lower]

private theorem no_defeaters_of_strictMinimum {args : List Argument} {attacks : List Attack}
    {a : Argument} (minimum : StrictMinimum args a) : defeaters args attacks a.id = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro id hid
  simp only [defeaters, List.mem_map, List.mem_filter] at hid
  obtain ⟨attack, ⟨_, condition⟩, rfl⟩ := hid
  simp only [Bool.and_eq_true] at condition
  have target : attack.dst = a.id := by simpa using condition.1
  rw [minimum_not_defeated minimum attack target] at condition
  simp at condition

private theorem minimum_mem_step {args : List Argument} {attacks : List Attack}
    {a : Argument} (minimum : StrictMinimum args a) (S : List String) :
    a.id ∈ groundedStep args attacks S := by
  simp only [groundedStep, List.mem_map, List.mem_filter]
  refine ⟨a, ⟨minimum.1, ?_⟩, rfl⟩
  simp [acceptable, no_defeaters_of_strictMinimum minimum]

private theorem minimum_mem_iterate {args : List Argument} {attacks : List Attack}
    {a : Argument} (minimum : StrictMinimum args a) (S : List String)
    (n : ℕ) (positive : 0 < n) :
    a.id ∈ iterateGrounded args attacks n S := by
  induction n generalizing S with
  | zero => simp at positive
  | succ n ih =>
    cases n with
    | zero => exact minimum_mem_step minimum S
    | succ n =>
      simp only [iterateGrounded]
      exact ih (groundedStep args attacks S) (Nat.zero_lt_succ _)

theorem minimum_in_grounded {args : List Argument} {attacks : List Attack}
    {a : Argument} (minimum : StrictMinimum args a) :
    a.id ∈ grounded args attacks := by
  exact minimum_mem_iterate minimum [] (args.length + 1) (Nat.zero_lt_succ _)

def frameArguments : List Argument :=
  [⟨"giraffe-order", 2.4694636005859008⟩,
   ⟨"find-out-before-building", 2.8567834606757225⟩,
   ⟨"serves-a-way", 2.1432169255819717⟩,
   ⟨"stopping", 13.730053366819615⟩]

def frameAttacks : List Attack :=
  [⟨"giraffe-order", "find-out-before-building"⟩,
   ⟨"giraffe-order", "serves-a-way"⟩,
   ⟨"find-out-before-building", "giraffe-order"⟩,
   ⟨"find-out-before-building", "serves-a-way"⟩,
   ⟨"serves-a-way", "giraffe-order"⟩,
   ⟨"serves-a-way", "find-out-before-building"⟩,
   ⟨"giraffe-order", "stopping"⟩,
   ⟨"find-out-before-building", "stopping"⟩,
   ⟨"serves-a-way", "stopping"⟩,
   ⟨"stopping", "giraffe-order"⟩,
   ⟨"stopping", "find-out-before-building"⟩,
   ⟨"stopping", "serves-a-way"⟩]

example : grounded frameArguments frameAttacks = ["serves-a-way"] := by native_decide

end DarkTower.WarMachine.SelectionArgument
