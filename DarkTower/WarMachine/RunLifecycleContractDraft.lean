import DarkTower.WarMachine.Holes

/-!
PROPOSED contract extension after the 2026-09-11 RUN4 execution findings.
This module does not certify Clojure, filesystem serialization, or a live run.
It demonstrates a gap in the existing carrier and states separate fresh-start
and existing-attempt inspection rules. No registry disposition is changed.
-/
namespace DarkTower.WarMachine.RunLifecycleContractDraft

open DarkTower.WarMachine.Holes

/-- The existing carrier permits repeated local attempt IDs. -/
def duplicateAttempts : Cohort Nat Nat Nat Nat where
  id := 1
  semanticEpoch := 1
  stoppingTarget := 2
  positiveTarget := by decide
  preregisteredOutcomes := Set.univ
  attempts := [1, 1]
  withinWindow := by decide

theorem current_cohort_does_not_require_unique_attempts :
    ¬ duplicateAttempts.attempts.Nodup := by
  decide

/-- Proposed global key. Every durable consumer must preserve both fields.
The runtime encoding's injectivity is a separate correspondence obligation. -/
structure AttemptKey where
  cohort : Nat
  localOrdinal : Nat
  deriving DecidableEq, Repr

theorem distinct_cohorts_have_distinct_keys (a b : AttemptKey)
    (h : a.cohort ≠ b.cohort) : a ≠ b := by
  intro eq
  exact h (congrArg AttemptKey.cohort eq)

/-- Keeping only the local ordinal reproduces the global-key collision. -/
theorem local_projection_collides :
    (AttemptKey.mk 1 1).localOrdinal = (AttemptKey.mk 2 1).localOrdinal ∧
    AttemptKey.mk 1 1 ≠ AttemptKey.mk 2 1 := by
  decide

inductive Lifecycle where
  | fresh
  | started (key : AttemptKey)
  | terminal (key : AttemptKey)
  deriving DecidableEq, Repr

/-- Capacity controls new execution; a completed admission is never fresh. -/
def mayStart (remaining : Nat) : Lifecycle → Bool
  | .fresh => remaining > 0
  | _ => false

/-- Read-only inspection is independent of remaining capacity. This predicate
confers neither terminal classification nor dispatch authority. -/
def mayInspect : Lifecycle → Bool
  | .fresh => false
  | _ => true

theorem exhausted_fresh_refuses : mayStart 0 .fresh = false := by decide

theorem started_never_redispatches (n : Nat) (key : AttemptKey) :
    mayStart n (.started key) = false := rfl

theorem consumed_attempt_remains_inspectable (key : AttemptKey) :
    mayStart 0 (.started key) = false ∧ mayInspect (.started key) = true := by
  exact ⟨rfl, rfl⟩

/-- Missing terminal evidence must not be converted into completion. -/
def observeTerminal (key : AttemptKey) (evidence : Option AttemptKey) : Lifecycle :=
  match evidence with
  | none => .started key
  | some observed => if observed = key then .terminal key else .started key

theorem missing_evidence_stays_started (key : AttemptKey) :
    observeTerminal key none = .started key := rfl

theorem foreign_evidence_cannot_complete (key observed : AttemptKey)
    (h : observed ≠ key) : observeTerminal key (some observed) = .started key := by
  simp [observeTerminal, h]

#print axioms current_cohort_does_not_require_unique_attempts
#print axioms distinct_cohorts_have_distinct_keys
#print axioms consumed_attempt_remains_inspectable
#print axioms foreign_evidence_cannot_complete

end DarkTower.WarMachine.RunLifecycleContractDraft
