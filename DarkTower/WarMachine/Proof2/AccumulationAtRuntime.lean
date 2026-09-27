import DarkTower.WarMachine.MachineDirichletAccumulation
import DarkTower.WarMachine.DirichletLearning

/-! The numeric recurrence in futon2.aif.machine-accumulation/step, not a4a's
capability/mission recount. Named fixed carriers describe inputs after the runtime
support validator. Finite machine numbers embed into ℝ; NaN/infinity rejection
remains a runtime boundary. No normalization of observation channels is assumed.
-/
namespace DarkTower.WarMachine.Proof2.AccumulationAtRuntime
open DarkTower.WarMachine
open Holes MachineBeliefState MachineDirichletAccumulation

abbrev Matrix := Channel → Status → ℝ
abbrev TickValue := (Channel → ℝ) × (Status → ℝ)

def step (a : Matrix) (p : TickValue) : Matrix :=
  fun c s => a c s + p.1 c * p.2 s

def run : Matrix → List TickValue → Matrix
  | a, [] => a
  | a, p :: ps => run (step a p) ps

theorem run_eq_declared (a : Matrix) (ticks : List TickValue) :
    run a ticks = declaredAccumulation a ticks := by
  induction ticks generalizing a with
  | nil =>
    funext c s
    simp [run, declaredAccumulation]
  | cons p ps ih =>
    rw [run, ih]
    funext c s
    simp only [declaredAccumulation, step, List.map_cons, List.sum_cons]
    ring

theorem runtimeRealisesDeclaredAccumulation : RealisesDeclaredAccumulation run :=
  run_eq_declared

theorem posteriorBecomesPrior (a : Matrix) (xs ys : List TickValue) :
    run a (xs ++ ys) = run (run a xs) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simpa only [List.cons_append, run] using ih (step a x)

theorem positivePriorRemainsPositive (a : Matrix) (p : TickValue)
    (ha : ∀ c s, 0 < a c s) (ho : ∀ c, 0 ≤ p.1 c) (hs : ∀ s, 0 ≤ p.2 s) :
    ∀ c s, 0 < step a p c s := by
  intro c s
  exact add_pos_of_pos_of_nonneg (ha c s) (mul_nonneg (ho c) (hs s))

/-- Shape of the kernel's identity guard; the state passed on is the returned
matrix and current tick id, not a fresh prior. -/
structure Carried where
  concentrations : Matrix
  lastTick : Option Nat

def guardedStep (state : Carried) (id : Nat) (previous : Option Nat) (p : TickValue) :
    Option Carried :=
  if previous = state.lastTick then
    some ⟨step state.concentrations p, some id⟩ else none

theorem chainGapRefuses (state : Carried) (id : Nat) (previous : Option Nat)
    (p : TickValue) (h : previous ≠ state.lastTick) :
    guardedStep state id previous p = none := by simp [guardedStep, h]

theorem chainUsesReturnedPosterior (state : Carried) (id nextId : Nat)
    (p q : TickValue) :
    (guardedStep state id state.lastTick p).bind
      (fun next => guardedStep next nextId (some id) q) =
      some ⟨step (step state.concentrations p) q, some nextId⟩ := by
  simp [guardedStep]

/-- The real carrier has 14×7 cells, with soft increments, not corpus counts. -/
example : Channel.all.length = 14 := by decide
example : Status.all.length = 7 := by decide
example (c : Channel) (s : Status) :
    step (fun _ _ => 3/2) (fun _ => 1/2, fun _ => 1/4) c s = 13/8 := by
  norm_num [step]
#print axioms runtimeRealisesDeclaredAccumulation
#print axioms posteriorBecomesPrior
#print axioms positivePriorRemainsPositive
#print axioms chainGapRefuses
#print axioms chainUsesReturnedPosterior
end DarkTower.WarMachine.Proof2.AccumulationAtRuntime
