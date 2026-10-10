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

#print axioms publicationCadence_valid
end DarkTower.WarMachine.ThreeHalvesRuntimeWitness
