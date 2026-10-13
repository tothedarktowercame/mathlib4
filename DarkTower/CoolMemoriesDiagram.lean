/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.CoolMemories
import Mathlib.Data.Finset.Sort

/-!
# A renderer for the first Cool Memories proof diagram

Mathlib's string-diagram widget expects morphisms in one monoidal category.  The parallel M40
syntax now exists, but its tensor combines diagrams over potentially different fact types into a
`Sum`-tagged type, and its rewrites remain state-relative.  Packaging those heterogeneous objects
as one category would be new mathematics, not a rendering adapter.  These small renderers therefore
consume checked `Path` or `ParallelStep` certificates directly and emit Mermaid.  They do not
establish correctness; the certificate arguments are the trust boundary.
-/

namespace DarkTower.CoolMemoriesDiagram

open DarkTower.CoolMemories

structure DeltaCompositionWitness (Fact : Type*) [DecidableEq Fact] where
  source : Snapshot Fact
  middle : Snapshot Fact
  target : Snapshot Fact
  checked : Derivation.Path
    (.seq (.atom (CertifiedDelta.between source middle))
      (.atom (CertifiedDelta.between middle target)))
    (.atom (CertifiedDelta.between source target))

def witness {Fact : Type*} [DecidableEq Fact]
    (A B C : Snapshot Fact) : DeltaCompositionWitness Fact where
  source := A
  middle := B
  target := C
  checked := Derivation.betweenSeqNormalizationPath A B C

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

/-- Render checked interchange as two lanes and two schedules.

The certificate is indexed by the exact diagrams shown: changing a lane boundary or either
schedule makes the call fail to elaborate. -/
def renderParallelInterchange {Left Right : Type*}
    [DecidableEq Left] [DecidableEq Right] [LinearOrder Left] [LinearOrder Right]
    [Repr Left] [Repr Right]
    {A A' : Snapshot Left} {B B' : Snapshot Right}
    (p : @Derivation Left _ A A') (q : @Derivation Right _ B B')
    (_certificate : Derivation.ParallelStep
      (Derivation.par p q) (Derivation.parRightFirst p q)) : String :=
  let a := snapshotLabel A
  let a' := snapshotLabel A'
  let b := snapshotLabel B
  let b' := snapshotLabel B'
  "flowchart LR\n" ++
  s!"  subgraph LR1[\"left then right\"]\n    L0[\"L {a}\"] -->|p| L1[\"L {a'}\"]\n" ++
  s!"    R0[\"R {b}\"] -->|q| R1[\"R {b'}\"]\n  end\n" ++
  s!"  subgraph RF1[\"right then left\"]\n    R2[\"R {b}\"] -->|q| R3[\"R {b'}\"]\n" ++
  s!"    L2[\"L {a}\"] -->|p| L3[\"L {a'}\"]\n  end\n" ++
  "  LR1 ==>|checked interchange; Sum-tagged independence| RF1"

end DarkTower.CoolMemoriesDiagram

def main : IO Unit :=
  IO.println
    (DarkTower.CoolMemoriesDiagram.toMermaid DarkTower.CoolMemoriesDiagram.sampleWitness) *>
  IO.println
    (DarkTower.CoolMemoriesDiagram.renderTransientCancellation
      DarkTower.CoolMemories.transientCancellationPath) *>
  IO.println
    (DarkTower.CoolMemoriesDiagram.renderParallelInterchange
      (.atom DarkTower.CoolMemories.leftParallel)
      (.atom DarkTower.CoolMemories.rightParallel)
      DarkTower.CoolMemories.parallelInterchange)
