import DarkTower.WarMachine.ThreeHalvesBlend
import DarkTower.WarMachine.CascadeEFE

/-!
# The honest structural part of the ThreeHalves → CascadeEFE bridge

`CascadeEFE.Policy` is structural: transitions and predictive/preference
evidence live in `CascadeEFE.Model` and the arguments to scoring.  This file
projects only what a validated three-halves policy can support and leaves the
rest as typed residual obligations.
-/

namespace DarkTower.WarMachine.ThreeHalvesCascadeBridge
open Holes ThreeHalvesBlend CascadeEFE
noncomputable section

def squareNodes (p : ThreeHalvesBlend.Policy) : Set Nat :=
  { i | i < p.squares.length }

def constructionEdges (p : ThreeHalvesBlend.Policy) (i j : Nat) : Prop :=
  (i, j) ∈ p.constructionOrder

/-- Facts not derivable from the existing three-halves carrier.  In particular,
acyclicity is not implied by pairwise gluing well-formedness. -/
structure StructuralResidual (p : ThreeHalvesBlend.Policy)
    (c : ApplicationOrderCertificate) where
  addedByOrganise : Set Nat
  addedWithinNodes : addedByOrganise ⊆ squareNodes p
  acyclic : acyclicDescent (constructionEdges p)

def projectPolicy (p : ThreeHalvesBlend.Policy)
    (c : ApplicationOrderCertificate) (r : StructuralResidual p c) :
    CascadeEFE.Policy Nat where
  cascade :=
    { nodes := squareNodes p
      addedByOrganise := r.addedByOrganise
      edges := constructionEdges p
      acyclic := r.acyclic
      precedence := c.applicationSequence }
  nodeDecidable := fun i => Nat.decLt i p.squares.length

/-- The complete validated structural input.  The authorization registry is a
trust premise, as in `ApplicationOrderCertificate.valid`. -/
structure StructuralEvidence (p : ThreeHalvesBlend.Policy) where
  policyWellFormed : p.wellFormed = true
  registry : List ApplicationOrderLaw
  orderCertificate : ApplicationOrderCertificate
  orderValid : orderCertificate.valid p registry = true
  residual : StructuralResidual p orderCertificate

/-- Every field projected into `CascadeEFE.Policy` is exposed explicitly. -/
theorem valid_projects_structural_policy (p : ThreeHalvesBlend.Policy)
    (e : StructuralEvidence p) :
    let pi := projectPolicy p e.orderCertificate e.residual
    pi.cascade.nodes = squareNodes p ∧
      pi.cascade.addedByOrganise = e.residual.addedByOrganise ∧
      pi.cascade.edges = constructionEdges p ∧
      pi.cascade.precedence = e.orderCertificate.applicationSequence := by
  simp [projectPolicy]

/-- These are the non-structural inputs still required before G.  No default
transition, predictive kernel, horizon, or preference is manufactured. -/
structure EFEResidual {S O : Type*} [Fintype S]
    (pi : CascadeEFE.Policy Nat) (model : CascadeEFE.Model Nat S O)
    (horizon : Nat) where
  resolved : ∃ transitions, CascadeEFE.resolve model (CascadeEFE.firing pi) = some transitions
  preferences : Fin horizon → ProbabilityKernel Unit O

/-! ## Executable one-square witnesses -/

private def oneSquare : Square :=
  ⟨⟨∅, ∅⟩, ⟨∅, ∅⟩, ⟨∅, ∅⟩, ⟨∅, ∅⟩,
   PMap.empty, PMap.empty, PMap.empty, PMap.empty, true, true⟩

def onePolicy : ThreeHalvesBlend.Policy :=
  ⟨[oneSquare], [], [(0, 0, 0)]⟩

private def oneLaw : ApplicationOrderLaw :=
  { identity := 81, version := 1, authority := 82, receipt := 83
    decode := fun rows => some (rows.map (·.1))
    accepts := fun construction application =>
      decide (construction = []) && decide (application = [0]) }

private def oneCertificate : ApplicationOrderCertificate :=
  { constructionOrder := [], applicationOrder := [(0, 0, 0)]
    applicationSequence := [0], lawIdentity := 81, lawVersion := 1
    lawAuthority := 82, lawReceipt := 83, selectorAuthority := 84 }

private theorem emptyDescent : acyclicDescent (constructionEdges onePolicy) := by
  have hn : ∀ i j, ¬ constructionEdges onePolicy i j := by
    simp [constructionEdges, onePolicy, Policy.constructionOrder]
  have hreach : ∀ i j, ¬ Reach (constructionEdges onePolicy) i j := by
    intro i j h
    induction h with
    | single h => exact hn _ _ h
    | tail _ h => exact hn _ _ h
  exact fun i h => hreach i i h

def oneEvidence : StructuralEvidence onePolicy where
  policyWellFormed := by native_decide
  registry := [oneLaw]
  orderCertificate := oneCertificate
  orderValid := by native_decide
  residual :=
    { addedByOrganise := ∅
      addedWithinNodes := by simp
      acyclic := emptyDescent }

theorem one_policy_projects_every_structural_field :
    let pi := projectPolicy onePolicy oneEvidence.orderCertificate oneEvidence.residual
    pi.cascade.nodes = {0} ∧ pi.cascade.addedByOrganise = ∅ ∧
      (∀ i j, ¬ pi.cascade.edges i j) ∧ pi.cascade.precedence = [0] := by
  dsimp [projectPolicy, oneEvidence, oneCertificate]
  constructor
  · ext i
    simp [squareNodes, onePolicy]
  constructor
  · rfl
  constructor
  · intro i j
    simp [constructionEdges, onePolicy, Policy.constructionOrder]
  · rfl

private def unitKernel : ProbabilityKernel Unit Unit :=
  CascadeEFE.point ()

def missingTransitionModel : CascadeEFE.Model Nat Unit Unit where
  initial := unitKernel
  observation := unitKernel
  guard := fun _ _ => true
  interpretation := fun _ => none

theorem missing_transition_prevents_full_efe_residual (T : Nat) :
    ¬ Nonempty (EFEResidual
      (projectPolicy onePolicy oneEvidence.orderCertificate oneEvidence.residual)
      missingTransitionModel T) := by
  intro h
  obtain ⟨r⟩ := h
  obtain ⟨transitions, ht⟩ := r.resolved
  simp [CascadeEFE.firing, projectPolicy, oneEvidence, oneCertificate,
    missingTransitionModel, squareNodes, onePolicy, CascadeEFE.resolve] at ht

#print axioms valid_projects_structural_policy
#print axioms one_policy_projects_every_structural_field
#print axioms missing_transition_prevents_full_efe_residual

end
end DarkTower.WarMachine.ThreeHalvesCascadeBridge
