/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.CoolMemories
import Lean

/-!
# Checker for M40 snapshot-delta exports

The M40 exporter emits fact identifiers only.  This executable parses that interchange value and
checks the same endpoint equation formalised in `DarkTower.CoolMemories`; private fact text never
crosses the boundary.
-/

namespace DarkTower.CoolMemoriesTraceChecker

open Lean DarkTower.CoolMemories

structure Endpoint where
  «at» : String
  facts : List String
  deriving FromJson, Repr

structure ExportedDelta where
  remove : List String
  add : List String
  deriving FromJson, Repr

structure SnapshotDeltaExport where
  schema : String
  «from» : Endpoint
  «to» : Endpoint
  delta : ExportedDelta
  deriving FromJson, Repr

def source (e : SnapshotDeltaExport) : Snapshot String := e.«from».facts.toFinset
def target (e : SnapshotDeltaExport) : Snapshot String := e.«to».facts.toFinset

def applyExport (e : SnapshotDeltaExport) : Snapshot String :=
  (source e \ e.delta.remove.toFinset) ∪ e.delta.add.toFinset

def accepts (e : SnapshotDeltaExport) : Bool :=
  e.schema == "m40.snapshot-delta/v1" &&
  e.«from».«at» < e.«to».«at» &&
  (e.delta.remove.toFinset ∩ e.delta.add.toFinset == ∅) &&
  e.delta.remove.toFinset ⊆ source e &&
  Disjoint e.delta.add.toFinset (source e \ e.delta.remove.toFinset) &&
  applyExport e == target e

theorem accepts_implies_endpoint_equation (e : SnapshotDeltaExport)
    (h : accepts e = true) : applyExport e = target e := by
  simp [accepts] at h
  exact h.2

/-! Four executable corruptions of the interchange contract. -/

private def endpoint (timestamp : String) (facts : List String) : Endpoint := ⟨timestamp, facts⟩
private def exported (sourceFacts targetFacts remove add : List String) : SnapshotDeltaExport :=
  ⟨"m40.snapshot-delta/v1", endpoint "2026-01-01" sourceFacts,
    endpoint "2026-01-02" targetFacts, ⟨remove, add⟩⟩

/-- Wrong source: the edit removes a fact not present at its declared input boundary. -/
example : accepts (exported ["kept"] ["kept"] ["absent"] []) = false := by decide

/-- Wrong target: the edit result and declared output boundary disagree. -/
example : accepts (exported ["old"] ["wrong"] ["old"] ["new"]) = false := by decide

/-- Invalid cancellation: one fact is simultaneously removed and added. -/
example : accepts (exported ["x"] ["x"] ["x"] ["x"]) = false := by decide

/-- Interference cannot be passed off as independence: same-namespace add/remove order differs. -/
example :
    removeOne.apply (addOne.apply ∅) ≠
      addOne.apply (removeOne.apply ∅) := by decide

def checkFile (path : System.FilePath) : IO UInt32 := do
  let contents ← if path.toString == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse contents)
  let payload : SnapshotDeltaExport ← IO.ofExcept (fromJson? json)
  if accepts payload then
    IO.println s!"M40-DELTA-ACCEPTED {payload.«from».facts.length}→{payload.«to».facts.length}"
    pure 0
  else
    IO.eprintln "M40-DELTA-REJECTED"
    pure 1

def run (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: CoolMemoriesTraceChecker SNAPSHOT-DELTA.json|-"
      pure 2

end DarkTower.CoolMemoriesTraceChecker

def main (args : List String) : IO UInt32 :=
  DarkTower.CoolMemoriesTraceChecker.run args
