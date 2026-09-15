import DarkTower.WarMachine.CascadeEFEPolicies

/-!
# G over cascades — the ratified policy grain

SPECIFICATION DIRECTION. This module is built from the concept records, not
from the implementation, and it cites no implementation source. Where the
Machine* modules witness what the code runs, this module states what the code
must run to be conformant; an implementation that presents a different policy
grain to `G` is non-conformant with the ratified definition, whatever its
witnesses prove.

Sources (the intention, by record):
- futon3c:holes/flights/F-wm-piloted-2026-06-12.md §Sortie-12, Joe's ruling,
  verbatim: "policy-grade G(s, π) is defined over policies = distributions
  over CASCADES; it has nothing to range over until the substrate holds the
  terms — minted holes, cascades, wiring diagrams, witnessed discharges."
- futon2:holes/M-G-over-cascades.md §1 (thesis: `G` is a property of
  cascades; a single pattern is the degenerate length-1 case) and §2 (the
  non-additivity argument: per-pattern scoring "marginalises out the
  interaction terms that carry the signal").
- p4ng:sec-glossary.tex ¶Policy-π (a policy π IS the pattern
  language/cascade when the composition is being scored; the cascade is a
  semilattice — sequential descent AND co-application overlap — not a tree)
  and ¶Control-states-U (patterns are control schemas; the cascade is the
  policy composed from them).
- DarkTower.WarMachine.Holes:29 (`Cascade`, CLOSED-BY-RECORD 2026-08-30,
  P-validated-R5 §3e) and Holes:139 ("… not the cascade-grain policy π that
  G scores").
- Commissioned: Joe, emacs-repl, 2026-09-15 ("Lean is meant to define the
  core concepts, from the glossary, from the equations, and from the effort
  I put in to clarify what was meant by policy, G, cascades …").

The canonical mathematical definition is now CascadeEFE.scoreCascade, built
from filtered guarded transitions, finite predictions and their common joint.
CascadeEFE derives ambiguity + risk = pragmatic cost - information gain.
CascadeEFEPolicies supplies admissible candidate priors and model-derived
composition controls. None of those results proves the F13 runtime seam.
-/

universe u

namespace DarkTower.WarMachine.GOverCascades

open DarkTower.WarMachine.Holes

noncomputable section

/-- An interpreted policy retains the cascade and its precedence, with explicit
decidable node membership. Candidate admissibility is supplied separately by
CascadeEFEPolicies.CandidateFamily. -/
abbrev CascadePolicy (P : Type u) := CascadeEFE.Policy P

/-- One canonical cascade G: the checked model-based scoring interface, including
typed missing-interpretation and inadmissible-risk refusals. This is an alias,
not another risk/eig functional. -/
abbrev cascadeGrainG := @CascadeEFE.scoreCascade

/- The former cascadePolicyPosterior (arbitrary exp/log, risk/eig and F callbacks)
is retired. CascadeEFEPolicies.family_priors proves the four stated policy
PRIOR forms on successfully scored admissible candidates. Per-policy F and the
observed-data posterior remain deferred; there is no replacement callback. -/

/-- The empty relation reaches nothing, so it descends acyclically. -/
theorem acyclicDescent_empty {α : Type u} :
    acyclicDescent (fun _ _ : α => False) := by
  have h : ∀ x y : α, ¬ Reach (fun _ _ : α => False) x y := by
    intro x y hxy
    induction hxy with
    | single h => exact h
    | tail _ h => exact h
  exact fun x hx => h x x hx

/-- M-G-over-cascades §1: "Scoring or committing on a single pattern is the
degenerate length-1 case." The embedding that exhibits it: one node, no
authored additions, no edges, unit precedence. -/
def singletonCascade {P : Type u} (p : P) : Cascade P where
  nodes := {p}
  addedByOrganise := ∅
  edges := fun _ _ => False
  acyclic := acyclicDescent_empty
  precedence := [p]

/-- A score is composition-blind when it depends only on WHICH patterns a
cascade holds, never on how they compose (edges, precedence). This is the
"bag of patterns" reading — the grain the ratified definition retired. -/
def CompositionBlind {P : Type u} (score : Cascade P → ℝ) : Prop :=
  ∃ f : Set P → ℝ, ∀ c, score c = f c.nodes

/-- Two cascades over the same two patterns, differing only in composition
(precedence order); both trivially acyclic. -/
def sameBagFirst : Cascade Bool :=
  ⟨{true, false}, ∅, fun _ _ => False, acyclicDescent_empty, [true, false]⟩

def sameBagSecond : Cascade Bool :=
  ⟨{true, false}, ∅, fun _ _ => False, acyclicDescent_empty, [false, true]⟩

theorem sameBag_distinct : sameBagFirst ≠ sameBagSecond := by
  intro h
  have := congrArg Cascade.precedence h
  simp [sameBagFirst, sameBagSecond] at this

/-- M-G-over-cascades §2, made formal, one half: a composition-blind score
CANNOT separate two cascades that hold the same patterns — whatever
interaction structure distinguishes them is marginalised out by
construction. -/
theorem compositionBlind_cannot_separate
    (score : Cascade Bool → ℝ) (h : CompositionBlind score) :
    score sameBagFirst = score sameBagSecond := by
  obtain ⟨f, hf⟩ := h
  rw [hf, hf]
  rfl

/-- Control 6 now derives the separation from two overlapping guarded operators
and the shared predictive joint. See CascadeEFEPolicies.composition_control
and composition_outcomes_differ; no indicator score is used. -/
alias cascadeGrain_separates_sameBag := CascadeEFEPolicies.composition_control

/-- HOLE · contract kind HOLE intentionally · owner: F-wm-piloted-2026-06-12
§Sortie-12 · M-G-over-cascades §7 (stop-the-line before INSTANTIATE) ·
commissioned Joe 2026-09-15 · holder: by-record · evidence:
futon2:holes/labs/wm-contract/aif-equations.edn `:policy-set` binds `:lean`
to `machinePolicySet`, whose index (`MachineAction.Candidate`: id, score,
noOp) carries no nodes, edges, or precedence — the composition-blind grain
this module proves strictly weaker; futon2:holes/labs/M-evaluate-policies/
defect-dG-nil-for-cascades.md records production writing `:G-total 0.0`
placeholders on 293/293 rows · falsifier: a production selection seam that
presents `Cascade`-typed policies to `G`, with a witness module citing THIS
definition as its specification, elaborates — at which point this marker's
`owed` constructor is retired. The mathematical definition and decomposition now exist in CascadeEFE, with
model-derived controls in CascadeEFEPolicies. The running War Machine production
seam remains owed; until it exists, no
production quantity may be reported at the name `G(π)` at policy grain. -/
inductive CascadeGrainSeam where
  | owed
  deriving DecidableEq, Repr


#print axioms acyclicDescent_empty
#print axioms sameBag_distinct
#print axioms compositionBlind_cannot_separate
#print axioms cascadeGrain_separates_sameBag

end

end DarkTower.WarMachine.GOverCascades
