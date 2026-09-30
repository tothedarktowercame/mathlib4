import DarkTower.WarMachine.CascadeOrder
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Dedup
import Mathlib.Data.Finset.Basic

/-!
# Reading-derived cascade policy sets

This module specifies the finite objects built by `analysis_cascade.clj`,
`pattern_retraction.clj`, `target_policy_family.clj`, and
`cascade_shape_g.clj`.  In particular, a policy set is the result of
`construct`; it is not a caller-supplied menu.  This supersedes the free
`menu` boundary of `Proof2.CascadePolicySet.cascadePolicySet` for new work,
without deleting that historical model.

The names correspond to countable runtime objects as follows:

| Lean | Clojure | counted object |
|---|---|---|
| `PatternId`, `Library` | pattern library | library pattern ids (1,431 in the 2026-09-30 census) |
| `Citation` | validated `:pattern-refs` | one library-pattern occurrence at a fragment index |
| `Unit` | `:nodes` / occurrence | one pattern occurrence in a cascade |
| `Cascade` | analysis cascade or graph retraction | one nonempty acyclic arranged cascade |
| `PatternGraph` | pattern relation graph | weighted graph edges, including authored direction when present |
| `Params.k` | `:k` | maximum number of retractions returned for one target |
| `PolicySet.members` | `policy-family` | structurally deduplicated policies for one target |

An “accepted seed” below means a seed actually passed to `retractions`.
The runtime first removes unknown and isolated reading citations; consequently
it would be false to require every raw citation to occur in every retraction.
-/

namespace DarkTower.WarMachine.CascadeSpec

noncomputable section
open Classical

abbrev PatternId := Nat
abbrev FragmentIndex := Nat
abbrev UnitId := Nat
abbrev Library := Finset PatternId

structure Citation (L : Library) where
  pattern : PatternId
  fragment : FragmentIndex
  inLibrary : pattern ∈ L
  deriving DecidableEq

structure Fragment (L : Library) where
  index : FragmentIndex
  citations : List (Citation L)
  deriving DecidableEq

structure Unit where
  id : UnitId
  pattern : PatternId
  deriving DecidableEq

abbrev DirectedEdge := Unit × Unit

/-- An overlap is represented canonically by its two endpoints in increasing
unit-id order.  This makes an undirected pair finite and decidable. -/
structure Overlap where
  left : Unit
  right : Unit
  canonical : left.id < right.id
  deriving DecidableEq

structure Cascade (L : Library) where
  units : Finset Unit
  nonempty : units.Nonempty
  precedes : Finset DirectedEdge
  overlap : Finset Overlap
  labelsInLibrary : ∀ u ∈ units, u.pattern ∈ L
  precedesEndpoints : ∀ e ∈ precedes, e.1 ∈ units ∧ e.2 ∈ units
  overlapEndpoints : ∀ e ∈ overlap, e.left ∈ units ∧ e.right ∈ units
  acyclic : acyclicDescent (fun a b => (a, b) ∈ precedes)
  deriving DecidableEq

def Cascade.roots {L : Library} (c : Cascade L) : Finset Unit :=
  c.units.filter fun u => ¬ ∃ v ∈ c.units, (v, u) ∈ c.precedes

def Cascade.containsPattern {L : Library} (c : Cascade L) (p : PatternId) : Prop :=
  ∃ u ∈ c.units, u.pattern = p

/-- A reading is the validated finite fragment analysis plus the cascades
actually constructed from that analysis.  Keeping these together records the
`analysis->cascades` boundary rather than inventing a second translation. -/
structure Reading (L : Library) where
  fragments : List (Fragment L)
  readingCascades : List (Cascade L)
  cascadeCites : ∀ c ∈ readingCascades,
    ∃ f ∈ fragments, ∃ q ∈ f.citations, c.containsPattern q.pattern
  noFragmentsNoCascades : fragments = [] → readingCascades = []

def Reading.citedPatterns {L : Library} (r : Reading L) : Finset PatternId :=
  (r.fragments.flatMap fun f => f.citations.map (·.pattern)).toFinset

structure GraphEdge where
  left : PatternId
  right : PatternId
  distinct : left ≠ right
  weight : ℚ
  /-- Direction authored in the evidence. `none` means overlap.  Direction is
  data; it is never derived from alphabetical or numeric ordering. -/
  authoredDirection : Option (PatternId × PatternId)
  directionEndpoints : ∀ d ∈ authoredDirection, d = (left, right) ∨ d = (right, left)
  deriving DecidableEq

structure PatternGraph (L : Library) where
  edges : Finset GraphEdge
  endpointsInLibrary : ∀ e ∈ edges, e.left ∈ L ∧ e.right ∈ L

def PatternGraph.incident {L : Library} (g : PatternGraph L) (p : PatternId) : Prop :=
  ∃ e ∈ g.edges, e.left = p ∨ e.right = p

def Reading.usableSeeds {L : Library} (r : Reading L) (g : PatternGraph L) : Finset PatternId :=
  r.citedPatterns.filter fun p => g.incident p

inductive WeightKind | authored | overlap deriving DecidableEq

structure Params where
  k : Nat
  weights : WeightKind → ℚ

def graphJoins {L : Library} (g : PatternGraph L) (a b : PatternId) : Prop :=
  ∃ e ∈ g.edges, (e.left = a ∧ e.right = b) ∨ (e.left = b ∧ e.right = a)

/-- The explicit contract of the graph-retraction implementation.  It says
only what construction relies on: supplied seeds survive, labels and edges
come from the graph/library, no seeds yields no result, and `k` bounds output. -/
structure RetractionSpec (L : Library) where
  retractions : PatternGraph L → Finset PatternId → Params → List (Cascade L)
  containsSeeds : ∀ g seeds p c, c ∈ retractions g seeds p →
    ∀ seed ∈ seeds, c.containsPattern seed
  labelsFromLibrary : ∀ g seeds p c, c ∈ retractions g seeds p →
    ∀ u ∈ c.units, u.pattern ∈ L
  edgesFromGraph : ∀ g seeds p c, c ∈ retractions g seeds p →
    ∀ e ∈ c.precedes, graphJoins g e.1.pattern e.2.pattern
  emptySeeds : ∀ g p, retractions g ∅ p = []
  bounded : ∀ g seeds p, (retractions g seeds p).length ≤ p.k

/-- Closed result type.  Its constructor is private: outside this module a
handwritten menu cannot be promoted to a `PolicySet`. -/
structure PolicySet (L : Library) where
  private mk ::
  data : List (Cascade L)

def PolicySet.members {L : Library} : PolicySet L → List (Cascade L)
  | .mk members => members

def source {L : Library} (r : Reading L) (g : PatternGraph L) (p : Params)
    (ret : RetractionSpec L) : List (Cascade L) :=
  r.readingCascades ++ ret.retractions g (r.usableSeeds g) p

/-- The policy family is exactly structural deduplication of reading cascades
and at most `k` graph retractions.  Equality of `Cascade` is equality of all
structural data; proof fields are propositionally irrelevant. -/
def construct {L : Library} (r : Reading L) (g : PatternGraph L) (p : Params)
    (ret : RetractionSpec L) : PolicySet L :=
  .mk (source r g p ret).dedup

theorem members_construct {L : Library} (r : Reading L) (g : PatternGraph L)
    (p : Params) (ret : RetractionSpec L) :
    (construct r g p ret).members = (source r g p ret).dedup := rfl

theorem member_is_valid {L : Library} (r : Reading L) (g : PatternGraph L)
    (p : Params) (ret : RetractionSpec L) (c : Cascade L)
    (_h : c ∈ (construct r g p ret).members) :
    c.units.Nonempty ∧ (∀ u ∈ c.units, u.pattern ∈ L) ∧
      acyclicDescent (fun a b => (a, b) ∈ c.precedes) :=
  ⟨c.nonempty, c.labelsInLibrary, c.acyclic⟩

theorem members_structurally_distinct {L : Library} (r : Reading L)
    (g : PatternGraph L) (p : Params) (ret : RetractionSpec L) :
    (construct r g p ret).members.Pairwise (· ≠ ·) := by
  exact List.nodup_dedup _

theorem member_cites_reading {L : Library} (r : Reading L) (g : PatternGraph L)
    (p : Params) (ret : RetractionSpec L) (c : Cascade L)
    (h : c ∈ (construct r g p ret).members) :
    ∃ f ∈ r.fragments, ∃ q ∈ f.citations, c.containsPattern q.pattern := by
  rw [members_construct] at h
  have hs : c ∈ source r g p ret := (List.mem_dedup.mp h)
  rcases List.mem_append.mp hs with hr | hx
  · exact r.cascadeCites c hr
  · have husable : (r.usableSeeds g).Nonempty := by
      by_contra hempty
      have heq : r.usableSeeds g = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      rw [heq, ret.emptySeeds] at hx
      simp at hx
    obtain ⟨seed, hseed⟩ := husable
    have hc := ret.containsSeeds g (r.usableSeeds g) p c hx seed hseed
    have hcited : seed ∈ r.citedPatterns := (Finset.mem_filter.mp hseed).1
    rw [Reading.citedPatterns, List.mem_toFinset] at hcited
    rcases List.mem_flatMap.mp hcited with ⟨f, hf, hfm⟩
    rcases List.mem_map.mp hfm with ⟨q, hq, rfl⟩
    exact ⟨f, hf, q, hq, hc⟩

theorem empty_reading_empty_policy_set {L : Library} (r : Reading L)
    (g : PatternGraph L) (p : Params) (ret : RetractionSpec L)
    (h : r.fragments = []) : (construct r g p ret).members = [] := by
  rw [members_construct, source, r.noFragmentsNoCascades h]
  have hs : r.usableSeeds g = ∅ := by
    ext seed
    simp [Reading.usableSeeds, Reading.citedPatterns, h]
  rw [hs, ret.emptySeeds]
  rfl

theorem policy_count_le_reading_plus_k {L : Library} (r : Reading L)
    (g : PatternGraph L) (p : Params) (ret : RetractionSpec L) :
    (construct r g p ret).members.length ≤ r.readingCascades.length + p.k := by
  rw [members_construct]
  calc
    (source r g p ret).dedup.length ≤ (source r g p ret).length :=
      (List.dedup_sublist _).length_le
    _ ≤ r.readingCascades.length + p.k := by
      simpa [source] using Nat.add_le_add_left (ret.bounded g (r.usableSeeds g) p)
        r.readingCascades.length

-- A list is not a policy set: callers must use `construct`.
/--
error: Type mismatch
  []
has type
  List ?m.1
but is expected to have type
  PolicySet L
-/
#guard_msgs in
example {L : Library} : PolicySet L := []

-- Cyclic and out-of-library examples are rejected at the proof fields of
-- `Cascade`; unlike a free menu, malformed data cannot enter `construct`.
/--
error: unsolved goals
⊢ ∀ (a b : Unit),
    (a, b) ∈
        {({ id := 0, pattern := 0 }, { id := 1, pattern := 1 }),
          ({ id := 1, pattern := 1 }, { id := 0, pattern := 0 })} →
      a.id < b.id
-/
#guard_msgs in
example : Cascade ({0, 1} : Library) where
  units := {⟨0, 0⟩, ⟨1, 1⟩}
  nonempty := by simp
  precedes := {(⟨0, 0⟩, ⟨1, 1⟩), (⟨1, 1⟩, ⟨0, 0⟩)}
  overlap := ∅
  labelsInLibrary := by simp
  precedesEndpoints := by simp
  overlapEndpoints := by simp
  acyclic := by
    apply acyclic_of_increasing_rank _ (fun u => u.id)

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : Cascade ({0} : Library) where
  units := {⟨0, 1⟩}
  nonempty := by simp
  precedes := ∅
  overlap := ∅
  labelsInLibrary := by simp
  precedesEndpoints := by simp
  overlapEndpoints := by simp
  acyclic := by
    apply acyclic_of_increasing_rank _ (fun _ => 0)
    simp

#print axioms member_is_valid
#print axioms members_structurally_distinct
#print axioms member_cites_reading
#print axioms empty_reading_empty_policy_set
#print axioms policy_count_le_reading_plus_k

end
end DarkTower.WarMachine.CascadeSpec
