/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.CoolMemories
import Mathlib.Data.Finset.Sort

/-!
# A renderer for the first Cool Memories proof diagram

Mathlib's string-diagram widget expects equality of global morphisms in a monoidal category.
M40 endpoint deltas are state-relative: their equality is checked at a typed source snapshot.
This small renderer therefore consumes the checked endpoint witness directly and emits Mermaid.
It does not establish correctness; its `checked` field can only be built from the Lean theorem.
-/

namespace DarkTower.CoolMemoriesDiagram

open DarkTower.CoolMemories

structure DeltaCompositionWitness (Fact : Type*) [DecidableEq Fact] where
  source : Snapshot Fact
  middle : Snapshot Fact
  target : Snapshot Fact
  checked :
    (Delta.between middle target).apply ((Delta.between source middle).apply source) =
      (Delta.between source target).apply source

def witness {Fact : Type*} [DecidableEq Fact]
    (A B C : Snapshot Fact) : DeltaCompositionWitness Fact where
  source := A
  middle := B
  target := C
  checked := Derivation.between_seq_eq_between A B C

private def snapshotLabel {Fact : Type*} [LinearOrder Fact] [Repr Fact]
    (s : Snapshot Fact) : String :=
  reprStr (s.sort (· ≤ ·))

/-- Render the checked two-box path and its canonical one-box normal form.

The middle node is the typed boundary retained by `TypedDiagram.seq`; the direct edge is the
normal form whose equality is carried by `checked`. -/
def toMermaid {Fact : Type*} [LinearOrder Fact] [Repr Fact]
    (w : DeltaCompositionWitness Fact) : String :=
  let a := snapshotLabel w.source
  let b := snapshotLabel w.middle
  let c := snapshotLabel w.target
  s!"flowchart LR\n  A[\"{a}\"] -->|Δ A B| B[\"{b}\"]\n  B -->|Δ B C| C[\"{c}\"]\n  A ==>|endpoint equality: checked by Lean| C"

def sampleWitness : DeltaCompositionWitness Nat :=
  witness ({1, 2} : Snapshot Nat) ({2, 3} : Snapshot Nat) ({2, 4} : Snapshot Nat)

/-- Render the concrete checked rewrite path for the transient-fact cancellation.

The unused-looking argument is the trust boundary: this renderer cannot be called for this claim
without constructing the `Path` whose `dropRemove` row carries the proof `1 ∉ source`. -/
def renderTransientCancellation
    (_certificate : Derivation.Path
      (.seq (.atom transientFirst) (.atom transientSecond))
      (.atom (CertifiedDelta.between ∅ ∅))) : String :=
  "flowchart TD\n" ++
  "  D0[\"∅ --add 1--> {1} --remove 1--> ∅\"]\n" ++
  "  D1[\"fused: remove {1}; add ∅\"]\n" ++
  "  D2[\"dropRemove 1; license: 1 ∉ source ∅\"]\n" ++
  "  D3[\"canonical Δ(∅,∅): identity\"]\n" ++
  "  D0 -->|fuse; global apply_comp| D1\n" ++
  "  D1 -->|checked local cancellation| D2\n" ++
  "  D2 -->|identify equal edits| D3"

end DarkTower.CoolMemoriesDiagram

def main : IO Unit :=
  IO.println
    (DarkTower.CoolMemoriesDiagram.toMermaid DarkTower.CoolMemoriesDiagram.sampleWitness) *>
  IO.println
    (DarkTower.CoolMemoriesDiagram.renderTransientCancellation
      DarkTower.CoolMemories.transientCancellationPath)
