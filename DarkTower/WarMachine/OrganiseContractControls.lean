import DarkTower.WarMachine.Holes

/-! Concrete accepting and rejecting controls over the actual organise contract.
The two-node fixture has an authored edge and distinct, validated receipts.
It is a model witness, not a transcription or a production coverage claim. -/
namespace DarkTower.WarMachine.OrganiseContractControls
open Holes
noncomputable section

def edge (a b : Nat) : Prop := a = 0 ∧ b = 1

def cascade : Cascade Nat where
  nodes := {0, 1}
  addedByOrganise := ∅
  edges := edge
  acyclic := acyclic_of_increasing_rank edge id (by
    intro a b h
    rcases h with ⟨rfl, rfl⟩
    decide)
  precedence := [0, 1]

def repo : Repository Nat := ⟨{0, 1}, edge, cascade.acyclic⟩

def declaration : OrganiseDeclaration Nat Nat Nat where
  temperament := cascade
  nodes := {0, 1}
  edges := edge
  precedence := [0, 1]
  nodeEvidence := fun rule p receipt => rule = 0 ∧ receipt = p
  wireEvidence := fun a b receipt => edge a b ∧ receipt = 2

def witness : OrganiseWitness Nat Nat Nat where
  cascade := cascade
  nodeReceipt := fun p => some (0, p)
  wireReceipt := fun _ _ => some 2

theorem accepts_receipted_cascade : organise declaration {0, 1} repo witness where
  selectedRecorded := by intro p h; exact h
  nodesRecorded := by intro p h; exact h
  nodesDeclared := rfl
  edgesDeclared := rfl
  precedenceDeclared := rfl
  precedenceCovers := by intro p; simp [witness, cascade]
  precedenceUnique := by decide
  origins := by simp [witness, cascade]
  authored := by intro a b h; exact Reach.single h
  endpoints := by
    intro a b h
    rcases h with ⟨rfl, rfl⟩
    simp [witness, cascade]
  nodeReceipted := by
    intro p _
    exact ⟨0, p, rfl, by simp [declaration, cascade], rfl, rfl⟩
  wireReceipted := by intro a b h; exact ⟨2, rfl, h, rfl⟩

/-- The same concrete cascade contains node 1 outside this recorded repository. -/
theorem rejects_off_repository_pattern :
    ¬ organise declaration {0} {repo with patterns := {0}} witness := by
  intro h
  have bad := h.nodesRecorded (show 1 ∈ witness.cascade.nodes by simp [witness, cascade])
  norm_num at bad

theorem rejects_unreceipted_element :
    ¬ organise declaration {0, 1} repo {witness with nodeReceipt := fun _ => none} := by
  intro h
  obtain ⟨rule, receipt, bad, _⟩ :=
    h.nodeReceipted 0 (show 0 ∈ witness.cascade.nodes by simp [witness, cascade])
  cases bad

theorem rejects_unevidenced_wire :
    ¬ organise declaration {0, 1} repo {witness with wireReceipt := fun _ _ => none} := by
  intro h
  obtain ⟨receipt, bad, _⟩ := h.wireReceipted 0 1 ⟨rfl, rfl⟩
  cases bad

/-- A present receipt that does not attest this dependency is also rejected. -/
theorem rejects_wrong_wire_receipt :
    ¬ organise declaration {0, 1} repo
      {witness with wireReceipt := fun _ _ => some 99} := by
  intro h
  obtain ⟨receipt, eq, valid⟩ := h.wireReceipted 0 1 ⟨rfl, rfl⟩
  have same : 99 = receipt := Option.some.inj eq
  have expected : receipt = 2 := valid.2
  omega

theorem rejects_ignored_temperament :
    ¬ organise {declaration with precedence := [1, 0]} {0, 1} repo witness := by
  intro h
  have bad : ([0, 1] : List Nat) = [1, 0] := h.precedenceDeclared
  contradiction

/-- Receipt presence does not establish a guard the evidence authority rejects. -/
theorem rejects_unestablished_guards :
    ¬ organise {declaration with nodeEvidence := fun _ _ _ => False}
      {0, 1} repo witness := by
  intro h
  obtain ⟨rule, receipt, _, _, bad⟩ :=
    h.nodeReceipted 0 (by simp [witness, cascade])
  exact bad

#print axioms rejects_unestablished_guards
#print axioms accepts_receipted_cascade
#print axioms rejects_off_repository_pattern
#print axioms rejects_unreceipted_element
#print axioms rejects_unevidenced_wire
#print axioms rejects_wrong_wire_receipt
#print axioms rejects_ignored_temperament
end
end DarkTower.WarMachine.OrganiseContractControls
