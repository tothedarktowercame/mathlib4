import DarkTower.WarMachine.ThreeHalvesRuntimeCertificate

/-! Generated from
`futon2/test/fixtures/three-halves-square/publication-cadence.edn`.
The Nat codes retain their names in that pinned EDN receipt. -/

namespace DarkTower.WarMachine.ThreeHalvesRuntimeWitness
open DarkTower.WarMachine.ThreeHalvesBlend
open DarkTower.WarMachine.ThreeHalvesRuntimeCertificate

def pin := "24a8a429148b1c6e2b41e482ee539c00285154957022f18b3dab181bbdf4fe12"
def path := "futon3/library/ukrns/publication-cadence.flexiarg"
def obj (text : String) (elems : Finset Nat) : ObjectReceipt :=
  ⟨text, path, pin, ⟨elems, ∅⟩⟩

def publicationCadence : Receipt :=
  { G := obj "one publication address" {0}
    I₁ := obj "living rendering at that address" {10, 11}
    I₂ := obj "frozen citable snapshot at that address" {20, 21}
    B := obj "living rendering and citable snapshot discoverable at one address" {30, 31, 32}
    a₁ := ⟨{(0, 10)}⟩
    a₂ := ⟨{(0, 20)}⟩
    b₁ := ⟨{(10, 30), (11, 31)}⟩
    b₂ := ⟨{(20, 30), (21, 32)}⟩
    aux₁ := false
    aux₂ := false }

theorem publicationCadence_valid : publicationCadence.valid = true := by
  native_decide

theorem publicationCadence_semantic_pushout :
    IsThreeHalvesPushout publicationCadence.square.span publicationCadence.square.cone :=
  valid_projects_semantic_pushout publicationCadence publicationCadence_valid

def uncoveredBlend : Receipt :=
  { publicationCadence with b₂ := ⟨{(20, 30)}⟩ }

theorem uncoveredBlend_invalid : uncoveredBlend.valid = false := by
  native_decide

/-! The flag matrix is intentionally measured, not repaired here.  The
inconsistent square remains jointly covered; each auxiliary flag removes its
route from consistency, while either flag independently discharges the
separate commutation requirement. -/
def inconsistentCovered : Receipt :=
  { publicationCadence with b₂ := ⟨{(20, 32), (21, 30)}⟩ }

def inconsistentAux₁ : Receipt :=
  { inconsistentCovered with aux₁ := true }

def inconsistentAux₂ : Receipt :=
  { inconsistentCovered with aux₂ := true }

def inconsistentBothAux : Receipt :=
  { inconsistentCovered with aux₁ := true, aux₂ := true }

def uncoveredBothAux : Receipt :=
  { uncoveredBlend with aux₁ := true, aux₂ := true }

def noncommutingConsistent : Receipt :=
  { publicationCadence with a₂ := ⟨∅⟩ }

theorem noAux_inconsistent_refuses : inconsistentCovered.valid = false := by
  native_decide

theorem aux1_only_inconsistent_passes : inconsistentAux₁.valid = true := by
  native_decide

theorem aux2_only_inconsistent_passes : inconsistentAux₂.valid = true := by
  native_decide

theorem both_aux_inconsistent_passes :
    inconsistentBothAux.square.commutes = false ∧
    inconsistentBothAux.square.cone.consistent = true ∧
    inconsistentBothAux.square.cone.isPushout = true ∧
    inconsistentBothAux.valid = true := by
  native_decide

theorem both_aux_uncovered_refuses :
    uncoveredBothAux.requiredCommutes = true ∧
    uncoveredBothAux.square.cone.consistent = true ∧
    uncoveredBothAux.square.cone.isPushout = false ∧
    uncoveredBothAux.valid = false := by
  native_decide

theorem noncommuting_consistent_refuses :
    noncommutingConsistent.square.commutes = false ∧
    noncommutingConsistent.square.cone.consistent = true ∧
    noncommutingConsistent.square.cone.isPushout = true ∧
    noncommutingConsistent.valid = false := by
  native_decide

/-! A malformed gluing can connect the raw diagnostic graph, but cannot
produce an admitted cascade verdict.  Its empty graph is not a total
isomorphism between the two nonempty `G` objects. -/
def malformedMerge : Policy :=
  { squares := [publicationCadence.square, publicationCadence.square]
    gluings := [⟨0, .G, 1, .G, ⟨∅⟩⟩]
    applicationOrder := [] }

theorem malformed_gluing_merges_raw_components_only :
    malformedMerge.components = [[0, 1]] ∧
    malformedMerge.wellFormed = false ∧
    malformedMerge.verdict = .bag [[0, 1]] := by
  native_decide

/-! Three individually valid isomorphisms can disagree around a triangle.
Identity followed by identity is identity, while the supplied direct edge is
the transposition of the two-element carrier. -/
def cycleTheory : Theory := ⟨{0, 1}, ∅⟩
def cycleSquare : Square :=
  ⟨cycleTheory, cycleTheory, cycleTheory, cycleTheory,
   ⟨∅⟩, ⟨∅⟩, ⟨∅⟩, ⟨∅⟩, true, true⟩
def identityIso : PMap := ⟨{(0, 0), (1, 1)}⟩
def swapIso : PMap := ⟨{(0, 1), (1, 0)}⟩

def incoherentCyclePolicy : Policy :=
  { squares := [cycleSquare, cycleSquare, cycleSquare]
    gluings := [⟨0, .G, 1, .G, identityIso⟩,
                ⟨1, .G, 2, .G, identityIso⟩,
                ⟨0, .G, 2, .G, swapIso⟩]
    applicationOrder := [] }

def coherentCyclePolicy : Policy :=
  { incoherentCyclePolicy with
    gluings := [⟨0, .G, 1, .G, identityIso⟩,
                ⟨1, .G, 2, .G, identityIso⟩,
                ⟨0, .G, 2, .G, identityIso⟩] }

def cycleTriangle : GluingTriangleCertificate :=
  { first := 0, second := 1, direct := 2 }

theorem incoherent_cycle_is_pairwise_valid_and_connected :
    incoherentCyclePolicy.wellFormed = true ∧
    incoherentCyclePolicy.components = [[0, 1, 2]] ∧
    incoherentCyclePolicy.verdict = .cascade := by
  native_decide

theorem incoherent_cycle_certificate_rejects :
    cycleTriangle.valid incoherentCyclePolicy = false := by
  native_decide

theorem coherent_cycle_certificate_accepts :
    cycleTriangle.valid coherentCyclePolicy = true := by
  native_decide

def treePolicy : Policy :=
  { coherentCyclePolicy with gluings := coherentCyclePolicy.gluings.take 2 }

def coherentCycleBasis : GluingCoherenceCertificate :=
  ⟨[⟨2, [(0, false), (1, false)]⟩]⟩

theorem coherent_tree_needs_no_cycle_obligations :
    treePolicy.gluingForest = [0, 1] ∧
    treePolicy.requiredCycleEdges = [] ∧
    (⟨[]⟩ : GluingCoherenceCertificate).valid treePolicy = true := by
  native_decide

theorem coherent_triangle_complete_basis_accepts :
    coherentCyclePolicy.gluingForest = [0, 1] ∧
    coherentCyclePolicy.requiredCycleEdges = [2] ∧
    coherentCycleBasis.valid coherentCyclePolicy = true := by
  native_decide

theorem incoherent_triangle_complete_basis_refuses :
    coherentCycleBasis.valid incoherentCyclePolicy = false := by
  native_decide

def twoCyclePolicy : Policy :=
  { squares := [cycleSquare, cycleSquare, cycleSquare, cycleSquare]
    gluings := [⟨0, .G, 1, .G, identityIso⟩,
                ⟨1, .G, 2, .G, identityIso⟩,
                ⟨2, .G, 3, .G, identityIso⟩,
                ⟨0, .G, 2, .G, identityIso⟩,
                ⟨1, .G, 3, .G, identityIso⟩]
    applicationOrder := [] }

def twoCycleComplete : GluingCoherenceCertificate :=
  ⟨[⟨3, [(0, false), (1, false)]⟩,
     ⟨4, [(1, false), (2, false)]⟩]⟩

theorem omitted_independent_cycle_refuses :
    twoCyclePolicy.requiredCycleEdges = [3, 4] ∧
    twoCycleComplete.valid twoCyclePolicy = true ∧
    (⟨twoCycleComplete.obligations.take 1⟩ : GluingCoherenceCertificate).valid
      twoCyclePolicy = false := by
  native_decide

def reversedDuplicatePolicy : Policy :=
  { squares := [cycleSquare, cycleSquare]
    gluings := [⟨0, .G, 1, .G, identityIso⟩,
                ⟨1, .G, 0, .G, identityIso⟩]
    applicationOrder := [] }

theorem reversed_duplicate_is_explicit_obligation :
    reversedDuplicatePolicy.gluingForest = [0] ∧
    reversedDuplicatePolicy.requiredCycleEdges = [1] ∧
    (⟨[⟨1, [(0, true)]⟩]⟩ : GluingCoherenceCertificate).valid
      reversedDuplicatePolicy = true := by
  native_decide

theorem malformed_gluing_cannot_enter_admitted_basis :
    malformedMerge.gluingForest = [] ∧
    malformedMerge.requiredCycleEdges = [] ∧
    (⟨[]⟩ : GluingCoherenceCertificate).valid malformedMerge = false := by
  native_decide

#print axioms publicationCadence_valid
#print axioms publicationCadence_semantic_pushout
#print axioms uncoveredBlend_invalid
#print axioms aux1_only_inconsistent_passes
#print axioms aux2_only_inconsistent_passes
#print axioms both_aux_inconsistent_passes
#print axioms both_aux_uncovered_refuses
#print axioms noncommuting_consistent_refuses
#print axioms malformed_gluing_merges_raw_components_only
#print axioms incoherent_cycle_is_pairwise_valid_and_connected
#print axioms incoherent_cycle_certificate_rejects
#print axioms coherent_cycle_certificate_accepts
#print axioms coherent_tree_needs_no_cycle_obligations
#print axioms coherent_triangle_complete_basis_accepts
#print axioms incoherent_triangle_complete_basis_refuses
#print axioms omitted_independent_cycle_refuses
#print axioms reversed_duplicate_is_explicit_obligation
#print axioms malformed_gluing_cannot_enter_admitted_basis
end DarkTower.WarMachine.ThreeHalvesRuntimeWitness
