import DarkTower.WarMachine.CascadeSpec
import DarkTower.WarMachine.ThreeHalvesBlend

/-!
# Executable cascades refine, and forget back to, the 象 structural cascade

This is the formal seam named by futon2's
`holes/E-implementing-G-over-cascades.md`.  It does not give descriptive
reading order an operational meaning.  The structural carrier binds distinct
occurrence ids to the squares and witnessed gluings of `ThreeHalvesBlend`.
The executable carrier may add only an independently authorized application
order and attributed operational clauses/open holes.

`forget` removes those executable additions.  `ExecutableCascade.Valid`
requires the result to be exactly the supplied structural carrier; an adapter
cannot repair a mismatch by inventing occurrences, squares, gluings or an
application order.
-/

namespace DarkTower.WarMachine.ExecutableCascadeRefinement

open DarkTower.WarMachine
open DarkTower.WarMachine.CascadeSpec
open DarkTower.WarMachine.ThreeHalvesBlend

abbrev OccurrenceId := Nat
abbrev CitationId := Nat

inductive CitationState
  | occurrence
  | void
  | unread
  deriving DecidableEq, Repr

/-- Void and unread citations stay in the construction census, but have no
occurrence id.  Only an instantiated four-map reading names an occurrence. -/
structure CitationResult where
  citation : CitationId
  state : CitationState
  occurrence : Option OccurrenceId
  deriving DecidableEq, Repr

def CitationResult.wellShaped (r : CitationResult) : Bool :=
  match r.state, r.occurrence with
  | .occurrence, some _ => true
  | .void, none => true
  | .unread, none => true
  | _, _ => false

def occurrenceResults (xs : List CitationResult) : List OccurrenceId :=
  xs.filterMap fun r => if r.state = .occurrence then r.occurrence else none

/-- Remove application order and retain exactly the squares and gluings.
Construction order is derived from the gluings and is therefore retained. -/
def forgetApplication (p : ThreeHalvesBlend.Policy) : ThreeHalvesBlend.Policy :=
  { p with applicationOrder := [] }

/-- Shared structural carrier.  `cascade` is the occurrence-level graph used
by G; `blend` supplies the four-map squares and witnessed gluings.  The list
`squareOccurrences` states which occurrence occupies each square index. -/
structure StructuralCascade where
  cascade : CascadeSpec.StructuralIdentity
  blend : ThreeHalvesBlend.Policy
  squareOccurrences : List OccurrenceId
  constructionOrder : List OccurrenceId
  census : List CitationResult
  sourceReceipt : Nat
  deriving DecidableEq

def StructuralCascade.occurrences (s : StructuralCascade) : Finset OccurrenceId :=
  s.cascade.units.image Prod.fst

def StructuralCascade.Valid (s : StructuralCascade) : Bool :=
  decide (s.sourceReceipt ≠ 0) &&
  s.blend.wellFormed &&
  decide (s.blend.applicationOrder = []) &&
  decide (s.squareOccurrences.length = s.blend.squares.length) &&
  decide s.squareOccurrences.Nodup &&
  decide (s.squareOccurrences.toFinset = s.occurrences) &&
  decide s.constructionOrder.Nodup &&
  decide (s.constructionOrder.toFinset = s.occurrences) &&
  decide ((s.census.map (·.citation)).Nodup) &&
  s.census.all CitationResult.wellShaped &&
  decide ((occurrenceResults s.census).Nodup) &&
  decide ((occurrenceResults s.census).toFinset = s.occurrences)

/-- The operational fields are deliberately opaque ids here.  Their runtime
records carry the attributed capability, operation and completion check; zero
means missing and is invalid. -/
structure OperationalClause where
  occurrence : OccurrenceId
  capability : Nat
  operation : Nat
  completionCheck : Nat
  deriving DecidableEq, Repr

structure OpenHole where
  occurrence : OccurrenceId
  owner : Nat
  question : Nat
  reentryCondition : Nat
  deriving DecidableEq, Repr

/-- The identity chain has two deliberately distinct stages.  Selection and
scoring bind the structural cascade; compilation creates a new executable
refinement identity, and the journal binds that executable identity.  The
projection clause in `ExecutableCascade.Valid` connects the stages without
falsely equating their digests. -/
structure IdentityChain where
  selectedStructural : Nat
  scoredStructural : Nat
  savedStructural : Nat
  savedExecutable : Nat
  journalExecutable : Nat
  deriving DecidableEq, Repr

def IdentityChain.Valid (i : IdentityChain) : Bool :=
  decide (i.selectedStructural ≠ 0) &&
  decide (i.savedExecutable ≠ 0) &&
  decide (i.selectedStructural = i.scoredStructural) &&
  decide (i.scoredStructural = i.savedStructural) &&
  decide (i.savedExecutable = i.journalExecutable)

/-- Executable refinement. `policy` may differ from `structural.blend` only by
its application order.  That order has a separately authorized certificate.
Every structural occurrence is either operationally closed or an explicit
open hole, never both. -/
structure ExecutableCascade where
  structural : StructuralCascade
  policy : ThreeHalvesBlend.Policy
  applicationCertificate : ThreeHalvesBlend.ApplicationOrderCertificate
  clauses : List OperationalClause
  holes : List OpenHole
  identity : IdentityChain
  deriving DecidableEq

def ExecutableCascade.closedOccurrences (e : ExecutableCascade) : List OccurrenceId :=
  e.clauses.map (·.occurrence)

def ExecutableCascade.openOccurrences (e : ExecutableCascade) : List OccurrenceId :=
  e.holes.map (·.occurrence)

/-- The forgetful projection is the structural record itself.  Validity below
also checks that clearing application order from the executable policy yields
the very same blend policy, preventing a substituted square or gluing graph. -/
def ExecutableCascade.forget (e : ExecutableCascade) : StructuralCascade :=
  e.structural

def ExecutableCascade.Valid (registry : List ThreeHalvesBlend.ApplicationOrderLaw)
    (e : ExecutableCascade) : Bool :=
  e.structural.Valid &&
  decide (forgetApplication e.policy = e.structural.blend) &&
  e.applicationCertificate.valid e.policy registry &&
  e.identity.Valid &&
  decide e.closedOccurrences.Nodup &&
  decide e.openOccurrences.Nodup &&
  decide (Disjoint e.closedOccurrences.toFinset e.openOccurrences.toFinset) &&
  decide ((e.closedOccurrences ++ e.openOccurrences).toFinset =
    e.structural.occurrences) &&
  e.clauses.all fun c =>
    decide (c.capability ≠ 0) && decide (c.operation ≠ 0) &&
      decide (c.completionCheck ≠ 0) && decide (c.occurrence ∈ e.structural.occurrences) &&
  e.holes.all fun h =>
    decide (h.owner ≠ 0) && decide (h.question ≠ 0) &&
      decide (h.reentryCondition ≠ 0) && decide (h.occurrence ∈ e.structural.occurrences)

theorem valid_forgets_exactly (registry : List ThreeHalvesBlend.ApplicationOrderLaw)
    (e : ExecutableCascade) (_h : e.Valid registry = true) :
    e.forget = e.structural := rfl

theorem valid_policy_projects_to_blend
    (registry : List ThreeHalvesBlend.ApplicationOrderLaw)
    (e : ExecutableCascade) (_h : e.Valid registry = true) :
    forgetApplication e.policy = e.structural.blend := by
  by_contra hne
  have hd : decide (forgetApplication e.policy = e.structural.blend) = false := by
    simp [hne]
  simp [ExecutableCascade.Valid, hd] at _h

/-! ## Decided positive and negative witnesses -/

private def unitIdentity : CascadeSpec.StructuralIdentity where
  units := {(0, 10), (1, 11), (2, 12), (3, 13)}
  precedes := {(0, 1), (0, 2), (1, 3), (2, 3)}
  overlap := ∅

private def structuralDiamond : StructuralCascade where
  cascade := unitIdentity
  blend := { ThreeHalvesBlend.diamondPolicy with applicationOrder := [] }
  squareOccurrences := [0, 1, 2, 3]
  constructionOrder := [0, 1, 2, 3]
  census := [⟨0, .occurrence, some 0⟩, ⟨1, .occurrence, some 1⟩,
    ⟨2, .occurrence, some 2⟩, ⟨3, .occurrence, some 3⟩,
    ⟨4, .void, none⟩, ⟨5, .unread, none⟩]
  sourceReceipt := 80

private def decodeFirst (rows : List (Nat × Nat × Nat)) : Option (List Nat) :=
  some (rows.map fun row => row.1)

private def exactLaw : ThreeHalvesBlend.ApplicationOrderLaw where
  identity := 81
  version := 1
  authority := 82
  receipt := 83
  decode := decodeFirst
  accepts := fun construction application =>
    decide (construction = [(0, 1), (0, 2), (1, 3), (2, 3)]) &&
      decide (application = [0, 1, 2, 3])

private def applicationRows : List (Nat × Nat × Nat) :=
  [(0, 10, 20), (1, 11, 21), (2, 12, 22), (3, 13, 23)]

private def executableDiamondPolicy : ThreeHalvesBlend.Policy :=
  { ThreeHalvesBlend.diamondPolicy with applicationOrder := applicationRows }

private def exactCertificate : ThreeHalvesBlend.ApplicationOrderCertificate where
  constructionOrder := [(0, 1), (0, 2), (1, 3), (2, 3)]
  applicationOrder := applicationRows
  applicationSequence := [0, 1, 2, 3]
  lawIdentity := 81
  lawVersion := 1
  lawAuthority := 82
  lawReceipt := 83
  selectorAuthority := 84

private def identity80 : IdentityChain := ⟨80, 80, 80, 96, 96⟩

private def closedClause (n : Nat) : OperationalClause := ⟨n, 90, 91, 92⟩

private def good : ExecutableCascade where
  structural := structuralDiamond
  policy := executableDiamondPolicy
  applicationCertificate := exactCertificate
  clauses := [closedClause 0, closedClause 1, closedClause 2]
  holes := [⟨3, 93, 94, 95⟩]
  identity := identity80

theorem structural_diamond_valid : structuralDiamond.Valid = true := by native_decide

theorem good_valid : good.Valid [exactLaw] = true := by native_decide

theorem reading_order_cannot_authorize_application :
    ({good with applicationCertificate :=
      { exactCertificate with lawIdentity := 0 }}).Valid [exactLaw] = false := by
  native_decide

theorem changed_gluing_graph_invalid :
    ({good with policy :=
      { executableDiamondPolicy with gluings := [] }}).Valid [exactLaw] = false := by
  native_decide

theorem void_citation_cannot_become_occurrence :
    ({good with structural :=
      { structuralDiamond with census :=
        [⟨0, .occurrence, some 0⟩, ⟨1, .occurrence, some 1⟩,
         ⟨2, .occurrence, some 2⟩, ⟨3, .occurrence, some 3⟩,
         ⟨4, .void, some 4⟩] }}).Valid [exactLaw] = false := by
  native_decide

theorem omitted_occurrence_invalid :
    ({good with clauses := [closedClause 0, closedClause 1]
                holes := [⟨3, 93, 94, 95⟩]}).Valid [exactLaw] = false := by
  native_decide

theorem substituted_identity_invalid :
    ({good with identity := ⟨80, 80, 81, 96, 96⟩}).Valid [exactLaw] = false := by
  native_decide

theorem journal_bound_to_structural_not_executable_invalid :
    ({good with identity := ⟨80, 80, 80, 96, 80⟩}).Valid [exactLaw] = false := by
  native_decide

#print axioms valid_forgets_exactly
#print axioms valid_policy_projects_to_blend
#print axioms good_valid

end DarkTower.WarMachine.ExecutableCascadeRefinement
