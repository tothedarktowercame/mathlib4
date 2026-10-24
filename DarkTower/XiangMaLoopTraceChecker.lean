/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.XiangMaLoopExample
import Lean

/-!
# Checker for measured 象/狗/馬 port satiety

`DarkTower.XiangMaLoopExample.satietyToday` is a table written by hand from the
inventory, so the theorems there pin the table, not the running loop. This
executable binds the table to the live turn store. The exporter
`futon3c/scripts/xiangma_port_export.py` measures every `Port` from the turn
records and emits, per port, how many records were eligible and how many
carried it:

```
python3 -I ~/code/futon3c/scripts/xiangma_port_export.py \
  | lake env lean --run DarkTower/XiangMaLoopTraceChecker.lean -
```

The checker regrades each port from its two counts by the fixed rule
(`measuredGrade`: canon iff every one of a non-empty eligible set carries
it), rejects an export whose own grade disagrees with that rule, and compares
the measured grades with `satietyToday`. A port missing from the export, an
unknown port name, or a port named twice is a rejection, never a skip.

Output: `XIANGMA-PORTS-AGREE <n>` and exit 0; or `XIANGMA-PORTS-DISAGREE`
followed by one line per disagreeing port and exit 1; or
`XIANGMA-PORTS-REJECTED <reason>` and exit 1.
-/

namespace DarkTower.XiangMaLoopTraceChecker

open Lean DarkTower.XiangMaLoopExample

/-! ## Port names, as the exporter spells them -/

/-- Every port, in declaration order. -/
def allPorts : List Port :=
  [Port.operatorText, Port.xiangTags, Port.proposedPatterns, Port.agentReply,
   Port.commits, Port.maCard, Port.maAlignment, Port.patternVerdict,
   Port.outcomeJoin, Port.memoryWrite, Port.citesUsedMemory,
   Port.storesFinding, Port.marksParagraphs, Port.commitTrailers]

theorem mem_allPorts (p : Port) : p ∈ allPorts := by
  cases p <;> decide

/-- The constructor's own name, which is what the exporter writes. -/
def portName : Port → String
  | Port.operatorText => "operatorText"
  | Port.xiangTags => "xiangTags"
  | Port.proposedPatterns => "proposedPatterns"
  | Port.agentReply => "agentReply"
  | Port.commits => "commits"
  | Port.maCard => "maCard"
  | Port.maAlignment => "maAlignment"
  | Port.patternVerdict => "patternVerdict"
  | Port.outcomeJoin => "outcomeJoin"
  | Port.memoryWrite => "memoryWrite"
  | Port.citesUsedMemory => "citesUsedMemory"
  | Port.storesFinding => "storesFinding"
  | Port.marksParagraphs => "marksParagraphs"
  | Port.commitTrailers => "commitTrailers"

def portOfName? (s : String) : Option Port :=
  allPorts.find? (fun p => portName p == s)

/-- Names round-trip, so no two ports share a name. -/
theorem portOfName?_portName (p : Port) : portOfName? (portName p) = some p := by
  cases p <;> decide

/-! ## The grading rule -/

/-- Fixed by packet 3, not tuned to the data: a port is fed (`canon`) iff the
eligible set is non-empty and every eligible record carries it. A partial feed
is hungry, which matches `XiangMaLoopExample`'s convention. -/
def measuredGrade (eligible carrying : Nat) : SatietyGrade :=
  if 0 < eligible ∧ carrying = eligible then SatietyGrade.canon else SatietyGrade.payoff

theorem measuredGrade_canon_iff (e c : Nat) :
    measuredGrade e c = SatietyGrade.canon ↔ 0 < e ∧ c = e := by
  unfold measuredGrade; split <;> simp_all

/-- No eligible record means hungry, whatever the carrying count. -/
theorem measuredGrade_empty (c : Nat) : measuredGrade 0 c = SatietyGrade.payoff := by
  simp [measuredGrade]

/-- One record short of full is hungry. -/
theorem measuredGrade_partial (e : Nat) : measuredGrade (e + 1) e = SatietyGrade.payoff := by
  simp [measuredGrade]

def gradeName : SatietyGrade → String
  | SatietyGrade.canon => "canon"
  | SatietyGrade.payoff => "payoff"
  | SatietyGrade.parse => "parse"
  | SatietyGrade.bundling => "bundling"
  | SatietyGrade.role => "role"

/-! ## Comparing measured grades with the table -/

/-- One measured port. -/
structure Measured where
  port : Port
  eligible : Nat
  carrying : Nat
  deriving DecidableEq, Repr

def Measured.grade (m : Measured) : SatietyGrade := measuredGrade m.eligible m.carrying

def lookup (ms : List Measured) (p : Port) : Option Measured :=
  ms.find? (fun m => m.port == p)

/-- The measured grade of every port equals `satietyToday`. -/
def agrees (ms : List Measured) : Bool :=
  allPorts.all fun p => decide ((lookup ms p).map Measured.grade = some (satietyToday p))

/-- Agreement means each port was measured and its measured grade is the table's. -/
theorem agrees_spec (ms : List Measured) (h : agrees ms = true) (p : Port) :
    (lookup ms p).map Measured.grade = some (satietyToday p) := by
  simp only [agrees, List.all_eq_true, decide_eq_true_eq] at h
  exact h p (mem_allPorts p)

/-- The ports whose measured grade differs from the table, in port order. -/
def disagreements (ms : List Measured) : List Measured :=
  ms.filter fun m => decide (m.grade ≠ satietyToday m.port)

/-! ## Controls on the comparison itself -/

/-- Counts that reproduce the table exactly: a fed port fully carried by one
record, a hungry port carried by none. -/
def tableCounts : List Measured :=
  allPorts.map fun p =>
    if satietyToday p = SatietyGrade.canon then ⟨p, 1, 1⟩ else ⟨p, 1, 0⟩

example : agrees tableCounts = true := by decide

/-- Severing 馬's alignment in one record of two is caught. -/
example :
    agrees (tableCounts.map fun m =>
      if m.port = Port.maAlignment then ⟨m.port, 2, 1⟩ else m) = false := by decide

/-- A port the table calls hungry, measured fully carried, is caught too. -/
example :
    agrees (tableCounts.map fun m =>
      if m.port = Port.xiangTags then ⟨m.port, 3, 3⟩ else m) = false := by decide

/-- A missing port is not agreement. -/
example : agrees (tableCounts.filter fun m => m.port ≠ Port.maCard) = false := by decide

/-! ## The interchange value -/

structure PortEntry where
  port : String
  measure : String
  eligible : Nat
  carrying : Nat
  grade : String
  deriving FromJson, Repr

structure Window where
  since : String
  deriving FromJson, Repr

structure PortExport where
  schema : String
  store : String
  window : Window
  ports : List PortEntry
  deriving FromJson, Repr

/-- Resolve names and counts. Rejects an unknown name, a port named twice, a
missing port, `carrying > eligible`, and a grade that is not the rule's. -/
def resolve (e : PortExport) : Except String (List Measured) := do
  unless e.schema == "xiangma.port-measure/v1" do
    throw s!"schema {e.schema}"
  let ms ← e.ports.mapM fun entry => do
    let some p := portOfName? entry.port | throw s!"unknown port {entry.port}"
    unless entry.carrying ≤ entry.eligible do
      throw s!"{entry.port}: carrying {entry.carrying} > eligible {entry.eligible}"
    let m : Measured := ⟨p, entry.eligible, entry.carrying⟩
    unless entry.grade == gradeName m.grade do
      throw s!"{entry.port}: exported grade {entry.grade}, rule gives {gradeName m.grade}"
    pure m
  for p in allPorts do
    match (ms.filter fun m => m.port == p).length with
    | 0 => throw s!"missing port {portName p}"
    | 1 => pure ()
    | _ => throw s!"port {portName p} named twice"
  pure ms

def disagreementLine (m : Measured) : String :=
  s!"{portName m.port} table={gradeName (satietyToday m.port)} measured={gradeName m.grade} " ++
    s!"eligible={m.eligible} carrying={m.carrying}"

def checkFile (path : System.FilePath) : IO UInt32 := do
  let contents ← if path.toString == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
  let payload? : Except String PortExport := do
    let json ← Json.parse contents
    fromJson? json
  match payload? >>= resolve with
  | Except.error err =>
      IO.println s!"XIANGMA-PORTS-REJECTED {err}"
      pure 1
  | Except.ok ms =>
      if agrees ms then
        IO.println s!"XIANGMA-PORTS-AGREE {ms.length}"
        pure 0
      else
        IO.println "XIANGMA-PORTS-DISAGREE"
        for m in disagreements ms do
          IO.println (disagreementLine m)
        pure 1

def run (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: XiangMaLoopTraceChecker PORT-EXPORT.json|-"
      pure 2

end DarkTower.XiangMaLoopTraceChecker

def main (args : List String) : IO UInt32 :=
  DarkTower.XiangMaLoopTraceChecker.run args
