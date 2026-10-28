import Mathlib.Data.List.Basic

/-!
# Post-release retry coalescing

A newer post-release retry with the same complete
`(injury-id, repair-id, attempt)` key replaces the older request at its queue
position. Distinct keys preserve FIFO order. Requests without a complete key
append without coalescing.
-/

namespace DarkTower.WarMachine.PostReleaseRetryCoalescing

structure RetryKey where
  injuryId : Nat
  repairId : Nat
  attempt : Nat
  deriving DecidableEq, Repr

structure Retry where
  key : Option RetryKey
  payload : Nat
  deriving DecidableEq, Repr

def enqueue (queue : List Retry) (newer : Retry) : List Retry :=
  match newer.key with
  | none => queue ++ [newer]
  | some key =>
      if queue.any (fun queued => queued.key == some key) then
        queue.map (fun queued => if queued.key == some key then newer else queued)
      else queue ++ [newer]

def keyT : RetryKey := ⟨1, 10, 2⟩
def keyU : RetryKey := ⟨2, 20, 1⟩
def oldT : Retry := ⟨some keyT, 100⟩
def newerT : Retry := ⟨some keyT, 101⟩
def requestU : Retry := ⟨some keyU, 200⟩

/-- Positive law: replacement is in place, so T remains ahead of U. -/
example : enqueue [oldT, requestU] newerT = [newerT, requestU] := by decide

/-- Negative/control instance: a distinct tuple does not replace T and appends
after the existing FIFO entries. -/
example : enqueue [oldT] requestU ≠ [requestU] := by decide

/-- An unkeyed request retains the old append-only behavior. -/
example : enqueue [oldT] ⟨none, 300⟩ = [oldT, ⟨none, 300⟩] := by decide

end DarkTower.WarMachine.PostReleaseRetryCoalescing
