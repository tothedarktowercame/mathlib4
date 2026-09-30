import DarkTower.WarMachine.CascadeOrder
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Dedup
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod

/-! Reading-derived cascades and graph-derived policy sets.

`readingCascades` mirrors `analysis_cascade.clj`: unsupported fragments are
skipped; alternatives select one citation per supported fragment; overlap
keeps all citations, overlaps citations in one fragment, and joins every unit
in consecutive supported fragments. Direction in graph retractions is data,
never inferred from pattern names.

| Lean | Clojure | countable thing |
|---|---|---|
| `Library` | pattern library | pattern ids (1,431 in the census) |
| `Citation` | validated `:pattern_refs` | cited patterns |
| `Unit` | `:nodes` | citation occurrences |
| `readingCascades` | `analysis->cascades` | reading-supported cascades |
| `PatternGraph` | relation graph | weighted edges and authored directions |
| `Params.k` | `:k` | maximum retractions |
| `PolicySet.members` | `policy-family` | deduplicated policies per target |

This construction supersedes the free `menu` boundary in
`Proof2.CascadePolicySet.cascadePolicySet` for new work. -/

namespace DarkTower.WarMachine.CascadeSpec
noncomputable section
open Classical

abbrev PatternId := Nat
abbrev Library := Finset PatternId

structure Citation (L : Library) where
  pattern : PatternId
  inLibrary : pattern ∈ L
  deriving DecidableEq

structure Fragment (L : Library) where
  citations : List (Citation L)
  deriving DecidableEq

structure Unit (L : Library) where
  fragment : Nat
  slot : Nat
  pattern : PatternId
  inLibrary : pattern ∈ L
  deriving DecidableEq

abbrev DirectedEdge (L : Library) := Unit L × Unit L

structure Overlap (L : Library) where
  left : Unit L
  right : Unit L
  canonical : left.fragment = right.fragment ∧ left.slot < right.slot
  deriving DecidableEq

structure Cascade (L : Library) where
  units : Finset (Unit L)
  nonempty : units.Nonempty
  precedes : Finset (DirectedEdge L)
  overlap : Finset (Overlap L)
  labelsInLibrary : ∀ u ∈ units, u.pattern ∈ L
  precedesEndpoints : ∀ e ∈ precedes, e.1 ∈ units ∧ e.2 ∈ units
  overlapEndpoints : ∀ e ∈ overlap, e.left ∈ units ∧ e.right ∈ units
  precedesForward : ∀ e ∈ precedes, e.1.fragment < e.2.fragment
  deriving DecidableEq

def Cascade.precedesRel {L : Library} (c : Cascade L) (a b : Unit L) : Prop :=
  (a, b) ∈ c.precedes

theorem Cascade.acyclic {L : Library} (c : Cascade L) : acyclicDescent c.precedesRel := by
  apply acyclic_of_increasing_rank c.precedesRel (·.fragment)
  intro a b h
  exact c.precedesForward (a, b) h

def Cascade.roots {L : Library} (c : Cascade L) : Finset (Unit L) :=
  c.units.filter fun u => ¬ ∃ v ∈ c.units, (v, u) ∈ c.precedes

def Cascade.containsPattern {L : Library} (c : Cascade L) (p : PatternId) : Prop :=
  ∃ u ∈ c.units, u.pattern = p

structure Reading (L : Library) where
  fragments : List (Fragment L)
  deriving DecidableEq

inductive ReadingMode | alternatives | overlap deriving DecidableEq

def unitsAtAux {L : Library} (fi : Nat) : Nat → List (Citation L) → List (Unit L)
  | _, [] => []
  | si, q :: qs => ⟨fi, si, q.pattern, q.inLibrary⟩ :: unitsAtAux fi (si + 1) qs

def unitsAt {L : Library} (fi : Nat) (f : Fragment L) : List (Unit L) :=
  unitsAtAux fi 0 f.citations

def fragmentUnitsAux {L : Library} : Nat → List (Fragment L) → List (List (Unit L))
  | _, [] => []
  | fi, f :: fs => unitsAt fi f :: fragmentUnitsAux (fi + 1) fs

def supportedUnits {L : Library} (r : Reading L) : List (List (Unit L)) :=
  (fragmentUnitsAux 0 r.fragments).filter (· ≠ [])

def alternatives : List (List α) → List (List α)
  | [] => [[]]
  | choices :: rest => choices.flatMap fun x => (alternatives rest).map (x :: ·)

def adjacentFragments {L : Library} (us : Finset (Unit L)) (i j : Nat) : Bool :=
  decide (i < j) && !(us.toList.any fun u => decide (i < u.fragment ∧ u.fragment < j))

def directedEdges {L : Library} (us : Finset (Unit L)) : Finset (DirectedEdge L) :=
  (us.product us).filter fun e => adjacentFragments us e.1.fragment e.2.fragment

def overlapPairs {L : Library} (us : Finset (Unit L)) : Finset (Overlap L) :=
  ((us.product us).filter fun e =>
    e.1.fragment = e.2.fragment ∧ e.1.slot < e.2.slot).attach.map
    ⟨fun e => ⟨e.1.1, e.1.2, by
        exact (Finset.mem_filter.mp e.property).2⟩,
      by
        intro a b h
        apply Subtype.ext
        exact Prod.ext (congrArg Overlap.left h) (congrArg Overlap.right h)⟩

def cascadeOfUnits? {L : Library} (row : List (Unit L)) : Option (Cascade L) :=
  let us := row.toFinset
  if h : us.Nonempty then
    some {
      units := us
      nonempty := h
      precedes := directedEdges us
      overlap := overlapPairs us
      labelsInLibrary := by intro u hu; exact u.inLibrary
      precedesEndpoints := by
        intro e he
        simp [directedEdges] at he
        exact ⟨he.1.1, he.1.2⟩
      overlapEndpoints := by
        intro e he
        rcases Finset.mem_map.mp he with ⟨x, hx, rfl⟩
        exact Finset.mem_product.mp (Finset.mem_filter.mp x.property).1
      precedesForward := by
        intro e he
        simp [directedEdges, adjacentFragments] at he
        exact he.2.1 }
  else none

def rawReadingCascades {L : Library} (mode : ReadingMode) (r : Reading L) : List (Cascade L) :=
  match mode with
  | .alternatives => (alternatives (supportedUnits r)).filterMap cascadeOfUnits?
  | .overlap =>
      match cascadeOfUnits? (supportedUnits r).flatten with
      | some c => [c]
      | none => []

def Reading.citedPatterns {L : Library} (r : Reading L) : Finset PatternId :=
  (r.fragments.flatMap fun f => f.citations.map (·.pattern)).toFinset

/-- The final check is redundant for correctly generated rows, but makes the
target-provenance invariant part of the executable constructor boundary. -/
def readingCascades {L : Library} (mode : ReadingMode) (r : Reading L) : List (Cascade L) :=
  (rawReadingCascades mode r).filter fun c =>
    c.units.toList.any fun u => u.pattern ∈ r.citedPatterns

structure GraphEdge where
  left : PatternId
  right : PatternId
  distinct : left ≠ right
  weight : ℚ
  authoredDirection : Option (PatternId × PatternId)
  directionEndpoints : ∀ d ∈ authoredDirection, d = (left, right) ∨ d = (right, left)
  deriving DecidableEq

structure PatternGraph (L : Library) where
  edges : Finset GraphEdge
  endpointsInLibrary : ∀ e ∈ edges, e.left ∈ L ∧ e.right ∈ L

def PatternGraph.incident {L : Library} (g : PatternGraph L) (p : PatternId) : Prop :=
  ∃ e ∈ g.edges, e.left = p ∨ e.right = p

def Reading.usableSeeds {L : Library} (r : Reading L) (g : PatternGraph L) : Finset PatternId :=
  r.citedPatterns.filter g.incident

inductive WeightKind | authored | overlap deriving DecidableEq
structure Params where
  mode : ReadingMode
  k : Nat
  weights : WeightKind → ℚ

def authoredGraphEdge {L : Library} (g : PatternGraph L) (a b : PatternId) : Prop :=
  ∃ e ∈ g.edges, e.authoredDirection = some (a, b)

def overlapGraphEdge {L : Library} (g : PatternGraph L) (a b : PatternId) : Prop :=
  ∃ e ∈ g.edges, e.authoredDirection = none ∧
    ((e.left = a ∧ e.right = b) ∨ (e.left = b ∧ e.right = a))

/-- The rejected implementation strategy: turn every graph edge into a
directed pair by numeric id, ignoring `authoredDirection`. -/
def alphabeticalRetractionEdges {L : Library} (g : PatternGraph L) :
    List (PatternId × PatternId) :=
  g.edges.toList.map fun e => if e.left < e.right then (e.left, e.right) else (e.right, e.left)

structure RetractionSpec (L : Library) where
  retractions : PatternGraph L → Finset PatternId → Params → List (Cascade L)
  containsSeeds : ∀ g seeds p c, c ∈ retractions g seeds p →
    ∀ seed ∈ seeds, c.containsPattern seed
  labelsFromLibrary : ∀ g seeds p c, c ∈ retractions g seeds p →
    ∀ u ∈ c.units, u.pattern ∈ L
  precedesAuthored : ∀ g seeds p c, c ∈ retractions g seeds p →
    ∀ e ∈ c.precedes, authoredGraphEdge g e.1.pattern e.2.pattern
  overlapUnauthored : ∀ g seeds p c, c ∈ retractions g seeds p →
    ∀ e ∈ c.overlap, overlapGraphEdge g e.left.pattern e.right.pattern
  usesEveryUnauthored : ∀ g seeds p c, c ∈ retractions g seeds p →
    ∀ ge ∈ g.edges, ge.authoredDirection = none →
      c.containsPattern ge.left → c.containsPattern ge.right →
      ∃ e ∈ c.overlap,
        (e.left.pattern = ge.left ∧ e.right.pattern = ge.right) ∨
        (e.left.pattern = ge.right ∧ e.right.pattern = ge.left)
  emptySeeds : ∀ g p, retractions g ∅ p = []
  bounded : ∀ g seeds p, (retractions g seeds p).length ≤ p.k

structure PolicySet (L : Library) where
  private mk ::
  data : List (Cascade L)

def PolicySet.members {L : Library} : PolicySet L → List (Cascade L)
  | .mk members => members

def source {L : Library} (r : Reading L) (g : PatternGraph L) (p : Params)
    (ret : RetractionSpec L) : List (Cascade L) :=
  readingCascades p.mode r ++ ret.retractions g (r.usableSeeds g) p

def construct {L : Library} (r : Reading L) (g : PatternGraph L) (p : Params)
    (ret : RetractionSpec L) : PolicySet L := .mk (source r g p ret).dedup

theorem members_construct {L : Library} (r : Reading L) (g : PatternGraph L)
    (p : Params) (ret : RetractionSpec L) :
    (construct r g p ret).members = (source r g p ret).dedup := rfl

theorem member_is_valid {L : Library} (r : Reading L) (g : PatternGraph L)
    (p : Params) (ret : RetractionSpec L) (c : Cascade L)
    (_h : c ∈ (construct r g p ret).members) :
    c.units.Nonempty ∧ (∀ u ∈ c.units, u.pattern ∈ L) ∧ acyclicDescent c.precedesRel :=
  ⟨c.nonempty, c.labelsInLibrary, c.acyclic⟩

theorem members_structurally_distinct {L : Library} (r : Reading L)
    (g : PatternGraph L) (p : Params) (ret : RetractionSpec L) :
    (construct r g p ret).members.Pairwise (· ≠ ·) := List.nodup_dedup _

theorem readingCascade_cites {L : Library} (mode : ReadingMode) (r : Reading L)
    (c : Cascade L) (h : c ∈ readingCascades mode r) :
    ∃ p ∈ r.citedPatterns, c.containsPattern p := by
  have ha := (List.mem_filter.mp h).2
  rw [List.any_eq_true] at ha
  obtain ⟨u, hu, hp⟩ := ha
  exact ⟨u.pattern, of_decide_eq_true hp, u, Finset.mem_toList.mp hu, rfl⟩

theorem member_cites_reading {L : Library} (r : Reading L) (g : PatternGraph L)
    (p : Params) (ret : RetractionSpec L) (c : Cascade L)
    (h : c ∈ (construct r g p ret).members) :
    ∃ q ∈ r.citedPatterns, c.containsPattern q := by
  rw [members_construct] at h
  have hs := List.mem_dedup.mp h
  rcases List.mem_append.mp hs with hr | hx
  · exact readingCascade_cites p.mode r c hr
  · have hn : (r.usableSeeds g).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty, ret.emptySeeds] at hx
      simp at hx
    obtain ⟨seed, hseed⟩ := hn
    exact ⟨seed, (Finset.mem_filter.mp hseed).1,
      ret.containsSeeds g (r.usableSeeds g) p c hx seed hseed⟩

theorem empty_reading_empty_policy_set {L : Library} (r : Reading L)
    (g : PatternGraph L) (p : Params) (ret : RetractionSpec L)
    (h : r.fragments = []) : (construct r g p ret).members = [] := by
  rw [members_construct]
  have hs : r.usableSeeds g = ∅ := by ext seed; simp [Reading.usableSeeds, Reading.citedPatterns, h]
  rw [source, hs, ret.emptySeeds]
  cases p.mode <;>
    simp [readingCascades, rawReadingCascades, supportedUnits, fragmentUnitsAux,
      h, alternatives, cascadeOfUnits?]

theorem policy_count_le_reading_plus_k {L : Library} (r : Reading L)
    (g : PatternGraph L) (p : Params) (ret : RetractionSpec L) :
    (construct r g p ret).members.length ≤ (readingCascades p.mode r).length + p.k := by
  rw [members_construct]
  calc
    (source r g p ret).dedup.length ≤ (source r g p ret).length :=
      (List.dedup_sublist _).length_le
    _ ≤ (readingCascades p.mode r).length + p.k := by
      simpa [source] using Nat.add_le_add_left (ret.bounded g (r.usableSeeds g) p)
        (readingCascades p.mode r).length

def fixtureLibrary : Library := {0, 1, 2}

def fixtureReading : Reading fixtureLibrary :=
  ⟨[⟨[⟨0, by simp [fixtureLibrary]⟩, ⟨1, by simp [fixtureLibrary]⟩]⟩,
    ⟨[⟨2, by simp [fixtureLibrary]⟩]⟩]⟩

def cascadeCounts {L : Library} (c : Cascade L) : Nat × Nat × Nat :=
  (c.units.card, c.precedes.card, c.overlap.card)

/-- Two alternatives, each a two-unit chain. -/
theorem fixture_alternatives :
    (readingCascades .alternatives fixtureReading).map cascadeCounts =
      [(2, 1, 0), (2, 1, 0)] := by
  simp +decide [readingCascades, rawReadingCascades, fixtureReading, fixtureLibrary,
    supportedUnits, fragmentUnitsAux, unitsAt, unitsAtAux, alternatives, cascadeOfUnits?,
    cascadeCounts, directedEdges, adjacentFragments, overlapPairs]

/-- One three-unit overlap cascade: the first fragment contributes one
overlap pair and both of its units precede the second fragment's unit. -/
theorem fixture_overlap :
    (readingCascades .overlap fixtureReading).map cascadeCounts = [(3, 2, 1)] := by
  simp +decide [readingCascades, rawReadingCascades, fixtureReading, fixtureLibrary,
    supportedUnits, fragmentUnitsAux, unitsAt, unitsAtAux, cascadeOfUnits?, cascadeCounts,
    directedEdges, adjacentFragments, overlapPairs]

-- An unoriented edge cannot justify alphabetical precedence.
/--
error: Tactic `assumption` failed

badGraph : PatternGraph {0, 1}
e : GraphEdge
he : e ∈ badGraph.edges
hl : e.left = 0
hr : e.right = 1
hn : e.authoredDirection = none
⊢ none = some (0, 1)
-/
#guard_msgs in
example (badGraph : PatternGraph ({0, 1} : Library))
    (h : ∃ e ∈ badGraph.edges, e.left = 0 ∧ e.right = 1 ∧ e.authoredDirection = none) :
    authoredGraphEdge badGraph 0 1 := by
  rcases h with ⟨e, he, hl, hr, hn⟩
  refine ⟨e, he, ?_⟩
  rw [hn]
  assumption

#print axioms Cascade.acyclic
#print axioms member_is_valid
#print axioms members_structurally_distinct
#print axioms readingCascade_cites
#print axioms member_cites_reading
#print axioms empty_reading_empty_policy_set
#print axioms policy_count_le_reading_plus_k
#print axioms fixture_alternatives
#print axioms fixture_overlap

end
end DarkTower.WarMachine.CascadeSpec
