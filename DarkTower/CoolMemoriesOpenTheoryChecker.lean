/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.CoolMemories
import Lean

/-!
# Transfer check: the public open-theory glue fixture

`open_theory/glue` warrants construction of a validated union DAG.  It does not define a
sequential-composition operation on theories, so this file does not assert that stronger claim.
It checks the smaller transfer: the producer and consumer arrows inhabit the same
`TypedDiagram` syntax used by the M40 proof, and interpreting that typed two-box diagram yields
the arrow chain exported by the real Clojure glue implementation.
-/

namespace DarkTower.CoolMemoriesOpenTheoryChecker

open Lean DarkTower.CoolMemories

abbrev Boundary := Finset String

structure Arrow where
  «from» : String
  «to» : String
  deriving BEq, DecidableEq, FromJson, Repr

structure TheoryView where
  id : String
  interface : List String
  «variables» : List String
  arrows : List Arrow
  deriving FromJson, Repr

structure GlueView where
  glued : Bool
  inputs : List String
  «variables» : List String
  arrows : List Arrow
  deriving FromJson, Repr

structure GlueExport where
  schema : String
  theories : List TheoryView
  glue : GlueView
  deriving FromJson, Repr

/-- An atomic arrow box can only connect the singleton boundary named by the arrow. -/
structure ArrowBox (A B : Boundary) where
  arrow : Arrow
  source_eq : A = {arrow.«from»}
  target_eq : B = {arrow.«to»}

def producer : ArrowBox ({"source"} : Boundary) {"shared"} :=
  ⟨⟨"source", "shared"⟩, rfl, rfl⟩

def consumer : ArrowBox ({"shared"} : Boundary) {"result"} :=
  ⟨⟨"shared", "result"⟩, rfl, rfl⟩

/-- The shared variable is a real typed middle boundary, not a matching string checked later. -/
def producerConsumerDiagram :
    TypedDiagram ArrowBox ({"source"} : Boundary) {"result"} :=
  .seq (.atom producer) (.atom consumer)

def interpret : {A B : Boundary} → TypedDiagram ArrowBox A B → List Arrow
  | _, _, .id _ => []
  | _, _, .atom b => [b.arrow]
  | _, _, .seq f g => interpret f ++ interpret g

theorem producerConsumer_arrows :
    interpret producerConsumerDiagram =
      [⟨"source", "shared"⟩, ⟨"shared", "result"⟩] := rfl

def expectedArrows : List Arrow := [⟨"source", "shared"⟩, ⟨"shared", "result"⟩]

def accepts (e : GlueExport) : Bool :=
  e.schema == "futon3c.open-theory-glue/v1" &&
  e.glue.glued &&
  e.glue.inputs == ["source"] &&
  e.glue.«variables».toFinset == ({"source", "shared", "result"} : Boundary) &&
  e.glue.arrows == expectedArrows &&
  e.theories.map (·.interface) == [["shared"], ["shared"]] &&
  decide (e.theories.flatMap (·.arrows) = interpret producerConsumerDiagram)

theorem accepts_implies_same_arrow_interpretation (e : GlueExport) (h : accepts e = true) :
    e.theories.flatMap (·.arrows) = interpret producerConsumerDiagram := by
  simp [accepts] at h
  exact h.2

def checkFile (path : System.FilePath) : IO UInt32 := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse contents)
  let payload : GlueExport ← IO.ofExcept (fromJson? json)
  if accepts payload then
    IO.println "OPEN-THEORY-TYPED-DIAGRAM-ACCEPTED source→shared→result"
    pure 0
  else
    IO.eprintln "OPEN-THEORY-TYPED-DIAGRAM-REJECTED"
    pure 1

def run (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: CoolMemoriesOpenTheoryChecker OPEN-THEORY-GLUE.json"
      pure 2

end DarkTower.CoolMemoriesOpenTheoryChecker

def main (args : List String) : IO UInt32 :=
  DarkTower.CoolMemoriesOpenTheoryChecker.run args
