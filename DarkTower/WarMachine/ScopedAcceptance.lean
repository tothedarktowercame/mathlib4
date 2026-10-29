import Mathlib.Data.List.Basic

namespace DarkTower.WarMachine

/-- Predicates admitted by the cause-scope harness.  There is deliberately no
constant constructor: every predicate observes the invoked function's result. -/
inductive ResultPredicate where
  | equals : List String → String → ResultPredicate
  | present : List String → ResultPredicate
  deriving DecidableEq

structure ScopedAcceptance where
  proposal : String
  diagnosis : String
  causeEntry : String
  sourcePin : String
  inputPath : List String
  inputDigest : String
  predicate : ResultPredicate
  deriving DecidableEq

structure CauseScopeReceipt where
  proposal : String
  diagnosis : String
  observedEntry : String
  sourcePin : String
  inputPath : List String
  inputDigest : String
  predicate : ResultPredicate
  invoked : Bool
  predicateObservedResult : Bool
  failures : Nat
  errors : Nat
  deriving DecidableEq

def CauseScopeReceipt.checksBefore
    (a : ScopedAcceptance) (r : CauseScopeReceipt) : Prop :=
  r.proposal = a.proposal ∧ r.diagnosis = a.diagnosis ∧
  r.observedEntry = a.causeEntry ∧ r.sourcePin = a.sourcePin ∧
  r.inputPath = a.inputPath ∧ r.inputDigest = a.inputDigest ∧
  r.predicate = a.predicate ∧ r.invoked = true ∧
  r.predicateObservedResult = true ∧ 0 < r.failures ∧ r.errors = 0

def ScopedAcceptance.admits (a : ScopedAcceptance) (r : CauseScopeReceipt) : Prop :=
  r.checksBefore a

theorem scopedAcceptance_admits_iff_checked_red
    (a : ScopedAcceptance) (r : CauseScopeReceipt) :
    a.admits r ↔ r.checksBefore a := Iff.rfl

theorem scopedAcceptance_fabricatedValue_refused
    (a : ScopedAcceptance) (r : CauseScopeReceipt)
    (h : r.predicateObservedResult = false) : ¬ a.admits r := by
  intro admitted
  simp [ScopedAcceptance.admits, CauseScopeReceipt.checksBefore, h] at admitted

theorem scopedAcceptance_noInvocation_refused
    (a : ScopedAcceptance) (r : CauseScopeReceipt) (h : r.invoked = false) :
    ¬ a.admits r := by
  intro admitted
  simp [ScopedAcceptance.admits, CauseScopeReceipt.checksBefore, h] at admitted

structure ScopeReplayReceipt where
  scope : ScopedAcceptance
  invoked : Bool
  predicateObservedResult : Bool
  healthy : Bool

def ScopeReplayReceipt.repairs (a : ScopedAcceptance) (r : ScopeReplayReceipt) : Prop :=
  r.scope = a ∧ r.invoked = true ∧ r.predicateObservedResult = true ∧ r.healthy = true

theorem scopedAcceptance_replay_repairs_iff_identical_scope
    (a : ScopedAcceptance) (r : ScopeReplayReceipt) :
    r.repairs a ↔
      r.scope = a ∧ r.invoked = true ∧ r.predicateObservedResult = true ∧
        r.healthy = true := Iff.rfl

theorem scopedAcceptance_replay_scopeMismatch_refused
    (a : ScopedAcceptance) (r : ScopeReplayReceipt) (h : r.scope ≠ a) :
    ¬ r.repairs a := by
  intro repaired
  exact h repaired.1

end DarkTower.WarMachine
