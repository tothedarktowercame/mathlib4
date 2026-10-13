/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.SymmDiff

/-!
# Cool memories: certified temporal-memory deltas

This file is the pure trusted core for `futon3c/holes/excursions/E-cool-memories.md`.
It deliberately contains no database or JSON code.  A snapshot is a finite set of facts;
the canonical net delta from `A` to `B` removes `A \ B` and adds `B \ A`.

There are three levels:

* `Delta` is an edit, meaningful on any snapshot;
* `CertifiedDelta A B` carries the proof that an edit takes the declared source to target;
* `Derivation A B` is a typed diagram (identity, one box, or sequential composition).

Sequential derivations retain their intermediate boundary.  `normalise` forgets that syntax only
after proving its interpretation and returns the canonical one-box delta between the endpoints.
-/

namespace DarkTower.CoolMemories

variable {Fact : Type*} [DecidableEq Fact]

/-- The live facts at one instant. -/
abbrev Snapshot (Fact : Type*) := Finset Fact

/-- A net edit: remove these facts, then add these facts. -/
structure Delta (Fact : Type*) where
  remove : Finset Fact
  add : Finset Fact
  disjoint : Disjoint remove add
  deriving DecidableEq

namespace Delta

/-- Interpret an edit as a state transformation. -/
def apply (d : Delta Fact) (s : Snapshot Fact) : Snapshot Fact :=
  (s \ d.remove) ∪ d.add

/-- The canonical endpoint difference. -/
def between (A B : Snapshot Fact) : Delta Fact where
  remove := A \ B
  add := B \ A
  disjoint := by
    rw [Finset.disjoint_left]
    intro x hxAB hxBA
    simp only [Finset.mem_sdiff] at hxAB hxBA
    exact hxAB.2 hxBA.1

@[simp] theorem mem_apply (d : Delta Fact) (s : Snapshot Fact) (x : Fact) :
    x ∈ d.apply s ↔ (x ∈ s ∧ x ∉ d.remove) ∨ x ∈ d.add := by
  simp [apply]

/-- Applying the canonical endpoint difference reaches its declared target. -/
@[simp] theorem apply_between (A B : Snapshot Fact) :
    (between A B).apply A = B := by
  ext x
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [between, apply, hxA, hxB]

/-- Fuse two edits as global state transformations.  This operation is not endpoint-relative. -/
def comp (p q : Delta Fact) : Delta Fact where
  remove := (p.remove ∪ q.remove) \ q.add
  add := (p.add \ q.remove) ∪ q.add
  disjoint := by
    rw [Finset.disjoint_left]
    intro x hxRemove hxAdd
    simp only [Finset.mem_sdiff, Finset.mem_union] at hxRemove hxAdd
    rcases hxRemove with ⟨hpq, hnqa⟩
    rcases hxAdd with hpa | hqa
    · rcases hpa with ⟨hpa, hnqr⟩
      rcases hpq with hpr | hqr
      · exact (Finset.disjoint_left.mp p.disjoint hpr hpa)
      · exact hnqr hqr
    · exact hnqa hqa

/-- Structural fusion has exactly the semantics of sequential execution, on every state. -/
theorem apply_comp (p q : Delta Fact) (s : Snapshot Fact) :
    (comp p q).apply s = q.apply (p.apply s) := by
  ext x
  have hp := Finset.disjoint_left.mp p.disjoint
  have hq := Finset.disjoint_left.mp q.disjoint
  by_cases hs : x ∈ s <;>
    by_cases hpr : x ∈ p.remove <;> by_cases hpa : x ∈ p.add <;>
    by_cases hqr : x ∈ q.remove <;> by_cases hqa : x ∈ q.add <;>
    simp_all [apply, comp]

/-- Remove one redundant removal instruction. -/
def eraseRemove (d : Delta Fact) (f : Fact) : Delta Fact where
  remove := d.remove.erase f
  add := d.add
  disjoint := d.disjoint.mono_left (Finset.erase_subset _ _)

/-- At a source where `f` is absent, erasing an instruction to remove `f` changes nothing. -/
theorem apply_eraseRemove_of_not_mem (d : Delta Fact) (s : Snapshot Fact) (f : Fact)
    (hs : f ∉ s) (hr : f ∈ d.remove) :
    (eraseRemove d f).apply s = d.apply s := by
  ext x
  by_cases hxf : x = f
  · subst x
    have hna : f ∉ d.add := fun ha ↦ Finset.disjoint_left.mp d.disjoint hr ha
    simp [apply, eraseRemove, hs, hna]
  · simp [apply, eraseRemove, hxf]

/-- Remove one redundant addition instruction. -/
def eraseAdd (d : Delta Fact) (f : Fact) : Delta Fact where
  remove := d.remove
  add := d.add.erase f
  disjoint := d.disjoint.mono_right (Finset.erase_subset _ _)

/-- At a source where `f` is already present, erasing an instruction to add `f` changes nothing. -/
theorem apply_eraseAdd_of_mem (d : Delta Fact) (s : Snapshot Fact) (f : Fact)
    (hs : f ∈ s) (ha : f ∈ d.add) :
    (eraseAdd d f).apply s = d.apply s := by
  ext x
  by_cases hxf : x = f
  · subst x
    have hnr : f ∉ d.remove := fun hr ↦ Finset.disjoint_left.mp d.disjoint hr ha
    simp [apply, eraseAdd, hs, hnr]
  · simp [apply, eraseAdd, hxf]

end Delta

/-- A delta together with the boundary equation it claims. -/
structure CertifiedDelta (A B : Snapshot Fact) where
  edit : Delta Fact
  correct : edit.apply A = B

namespace CertifiedDelta

/-- The canonical certified delta between any two snapshots. -/
def between (A B : Snapshot Fact) : CertifiedDelta A B :=
  ⟨Delta.between A B, Delta.apply_between A B⟩

/-- Identity edit at a snapshot. -/
def nil (A : Snapshot Fact) : CertifiedDelta A A := between A A

@[ext] theorem ext {A B : Snapshot Fact} {p q : CertifiedDelta A B}
    (h : p.edit = q.edit) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- Fuse adjacent certified boxes without losing their checked middle boundary. -/
def comp {A B C : Snapshot Fact} (p : CertifiedDelta A B) (q : CertifiedDelta B C) :
    CertifiedDelta A C where
  edit := Delta.comp p.edit q.edit
  correct := by rw [Delta.apply_comp, p.correct, q.correct]

/-- A source-licensed removal cancellation. -/
def dropRemove {A B : Snapshot Fact} (d : CertifiedDelta A B) (f : Fact)
    (hA : f ∉ A) (hf : f ∈ d.edit.remove) : CertifiedDelta A B where
  edit := Delta.eraseRemove d.edit f
  correct := (Delta.apply_eraseRemove_of_not_mem d.edit A f hA hf).trans d.correct

/-- A source-licensed addition cancellation. -/
def dropAdd {A B : Snapshot Fact} (d : CertifiedDelta A B) (f : Fact)
    (hA : f ∈ A) (hf : f ∈ d.edit.add) : CertifiedDelta A B where
  edit := Delta.eraseAdd d.edit f
  correct := (Delta.apply_eraseAdd_of_mem d.edit A f hA hf).trans d.correct

end CertifiedDelta

/-- Domain-independent syntax for a typed proof diagram.

`seq` is vertical gluing.  Its middle object is an actual boundary in the type, so a producer
ending at the wrong object cannot be connected to a consumer.  M40 deltas and open-theory boxes
use the same syntax while supplying different `Box` types and interpretations. -/
inductive TypedDiagram {Obj : Type*} (Box : Obj → Obj → Type*) : Obj → Obj → Type _
  | id (A) : TypedDiagram Box A A
  | atom {A B} (d : Box A B) : TypedDiagram Box A B
  | seq {A B C} (f : TypedDiagram Box A B) (g : TypedDiagram Box B C) : TypedDiagram Box A C

/-- M40 proof diagrams are typed diagrams whose atomic boxes are certified deltas. -/
abbrev Derivation := TypedDiagram (@CertifiedDelta Fact _)

namespace Derivation

/-- Execute a derivation.  This is the semantic interpretation of its diagram. -/
def run : {A B : Snapshot Fact} → Derivation A B → Snapshot Fact → Snapshot Fact
  | _, _, .id _ => fun s => s
  | _, _, .atom d => d.edit.apply
  | _, _, .seq f g => fun s => run g (run f s)

/-- Every well-typed diagram takes its declared source to its declared target. -/
theorem run_source : {A B : Snapshot Fact} → (d : Derivation A B) → d.run A = B
  | _, _, .id _ => by simp [run]
  | _, _, .atom d => by simpa [run] using d.correct
  | _, _, .seq f g => by
      change run g (run f _) = _
      rw [run_source f, run_source g]

/-- Named semantic steps corresponding to the two boxes of the composition diagram. -/
theorem between_seq_run (A B C : Snapshot Fact) :
    run (TypedDiagram.seq
      (.atom (CertifiedDelta.between A B))
      (.atom (CertifiedDelta.between B C))) A = C := by
  apply run_source

/-- The local cancellation calculation behind delta composition.

Unlike `between_seq_run`, this proof does not appeal to the endpoints stored in
`CertifiedDelta`.  It checks all eight possible membership states of one fact across `A`, `B`,
and `C`.  Those cases are the local remove/keep/add rewrites from which the whole diagram
equality follows. -/
theorem between_seq_pointwise (A B C : Snapshot Fact) (x : Fact) :
    x ∈ (Delta.between B C).apply ((Delta.between A B).apply A) ↔
      x ∈ (Delta.between A C).apply A := by
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> by_cases hC : x ∈ C <;>
    simp [Delta.apply, Delta.between, hA, hB, hC]

/-- The first proof diagram, extensionally: the checked two-box path and the canonical one-box
path have the same result at their shared typed source. -/
theorem between_seq_eq_between (A B C : Snapshot Fact) :
    (Delta.between B C).apply ((Delta.between A B).apply A) =
      (Delta.between A C).apply A := by
  ext x
  exact between_seq_pointwise A B C x

/-! ### Checked local rewrites between typed proof diagrams -/

/-- One locally checkable rewrite between diagrams with identical boundaries. -/
inductive Step : {A B : Snapshot Fact} → Derivation A B → Derivation A B → Type _
  | fuse {A B C} (p : CertifiedDelta A B) (q : CertifiedDelta B C) :
      Step (.seq (.atom p) (.atom q)) (.atom (CertifiedDelta.comp p q))
  | dropRemove {A B} (d : CertifiedDelta A B) (f : Fact)
      (hA : f ∉ A) (hf : f ∈ d.edit.remove) :
      Step (.atom d) (.atom (CertifiedDelta.dropRemove d f hA hf))
  | dropAdd {A B} (d : CertifiedDelta A B) (f : Fact)
      (hA : f ∈ A) (hf : f ∈ d.edit.add) :
      Step (.atom d) (.atom (CertifiedDelta.dropAdd d f hA hf))
  | identify {A B} (p q : CertifiedDelta A B) (h : p.edit = q.edit) :
      Step (.atom p) (.atom q)
  | idLeft {A B} (d : Derivation A B) : Step (.seq (.id A) d) d
  | idRight {A B} (d : Derivation A B) : Step (.seq d (.id B)) d

/-- A proof is a path of checked local rewrites between typed diagrams. -/
inductive Path : {A B : Snapshot Fact} → Derivation A B → Derivation A B → Type _
  | refl (d) : Path d d
  | cons {d e g} (head : Step d e) (tail : Path e g) : Path d g

/-- Every local rewrite preserves execution at the typed source. -/
theorem Step.sound : {A B : Snapshot Fact} → {d e : Derivation A B} →
    Step d e → run d A = run e A
  | _, _, _, _, .fuse p q => by
      simp only [run]
      exact (Delta.apply_comp p.edit q.edit _).symm
  | _, _, _, _, .dropRemove d f hA hf => by
      simp only [run]
      exact (Delta.apply_eraseRemove_of_not_mem d.edit _ f hA hf).symm
  | _, _, _, _, .dropAdd d f hA hf => by
      simp only [run]
      exact (Delta.apply_eraseAdd_of_mem d.edit _ f hA hf).symm
  | _, _, _, _, .identify p q h => by cases CertifiedDelta.ext h; rfl
  | _, _, _, _, .idLeft d => by simp [run]
  | _, _, _, _, .idRight d => by simp [run]

/-- A rewrite path preserves execution. -/
theorem Path.sound : {A B : Snapshot Fact} → {d e : Derivation A B} →
    Path d e → run d A = run e A
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .cons h t => (h.sound).trans t.sound

end Derivation

/-! ## Independent edits and interchange -/

namespace Delta

/-- Lift an edit to the left half of a disjoint sum of fact namespaces. -/
def inl {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
    (d : Delta Left) : Delta (Sum Left Right) where
  remove := d.remove.map ⟨Sum.inl, Sum.inl_injective⟩
  add := d.add.map ⟨Sum.inl, Sum.inl_injective⟩
  disjoint := by
    simpa [Finset.disjoint_left] using d.disjoint

/-- Lift an edit to the right half of a disjoint sum of fact namespaces. -/
def inr {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
    (d : Delta Right) : Delta (Sum Left Right) where
  remove := d.remove.map ⟨Sum.inr, Sum.inr_injective⟩
  add := d.add.map ⟨Sum.inr, Sum.inr_injective⟩
  disjoint := by
    simpa [Finset.disjoint_left] using d.disjoint

/-- Edits on disjoint fact namespaces commute.  This is the semantic interchange law. -/
theorem inl_inr_interchange {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
    (p : Delta Left) (q : Delta Right) (s : Snapshot (Sum Left Right)) :
    (inr q).apply ((inl p).apply s) = (inl p).apply ((inr q).apply s) := by
  ext x
  cases x <;> simp [apply, inl, inr]

end Delta

/-! ## Executable planted failures

These examples are small witnesses for the four rejection classes in the excursion.  Boundary
mismatches themselves are rejected by elaboration; the propositions below make the other planted
bad claims executable without keeping uncompilable source files in the build.
-/

section PlantedFailures

def a : Snapshot Nat := {1}
def b : Snapshot Nat := {2}
def c : Snapshot Nat := {3}

example : (Delta.between a b).apply a = b := by decide
example : (Delta.between a b).apply a ≠ c := by decide

/-- A false cancellation: adding `2` does not leave `{1}` unchanged. -/
example : (Delta.between a b).apply a ≠ a := by decide

/-- Interference is visible when both edits use the same namespace. -/
def addOne : Delta Nat := Delta.between ∅ {1}
def removeOne : Delta Nat := Delta.between {1} ∅

example :
    removeOne.apply (addOne.apply ∅) ≠ addOne.apply (removeOne.apply ∅) := by decide

/-! A complete checked cancellation path for a fact born and withdrawn between endpoints. -/

def transientFirst : CertifiedDelta (∅ : Snapshot Nat) {1} := CertifiedDelta.between ∅ {1}
def transientSecond : CertifiedDelta ({1} : Snapshot Nat) ∅ := CertifiedDelta.between {1} ∅
def transientFused : CertifiedDelta (∅ : Snapshot Nat) ∅ :=
  CertifiedDelta.comp transientFirst transientSecond
def transientDropped : CertifiedDelta (∅ : Snapshot Nat) ∅ :=
  CertifiedDelta.dropRemove transientFused 1 (by decide) (by decide)

theorem transientDropped_is_identity :
    transientDropped.edit = (CertifiedDelta.between ∅ ∅).edit := by decide

/-- The proof diagram has three checked rows: fuse, cancel the redundant removal using the
empty source boundary, and identify the resulting edit with the canonical identity. -/
def transientCancellationPath :
    Derivation.Path
      (.seq (.atom transientFirst) (.atom transientSecond))
      (.atom (CertifiedDelta.between ∅ ∅)) :=
  .cons (.fuse transientFirst transientSecond)
    (.cons (.dropRemove transientFused 1 (by decide) (by decide))
      (.cons (.identify transientDropped (CertifiedDelta.between ∅ ∅)
        transientDropped_is_identity) (.refl _)))

theorem transientCancellationPath_sound :
    Derivation.run (.seq (.atom transientFirst) (.atom transientSecond)) ∅ =
      Derivation.run (.atom (CertifiedDelta.between ∅ ∅)) ∅ :=
  transientCancellationPath.sound

end PlantedFailures

end DarkTower.CoolMemories
