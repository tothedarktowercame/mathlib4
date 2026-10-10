import DarkTower.WarMachine.ConstructionReceipt

/-! GENERATED FILE — DO NOT EDIT.
Source SHA-256: 2b80e2f64b70c4e7c1acbf07d786526829ec0f8220caa4ac4e548ea0af6bfd66
Generator: futon2.aif.construction-receipt-lean-adapter
Unit identity map: {:P 0, :Q 1}
Token identity map: {:q 0, :w 1}
-/

namespace DarkTower.WarMachine.ConstructionReceipt.RuntimeWitness
open DarkTower.WarMachine.ConstructionReceipt

def runtimeSemantics : Nat → UnitSemantics
  | 0 => ⟨{0}, ∅⟩
  | 1 => ⟨{1}, {0}⟩
  | _ => ⟨∅, ∅⟩

def runtimeReceipt : Receipt :=
  { order := [0, 1]
    support := [⟨0, 1, {0}⟩]
    meets := [⟨0, 1, 0, [], [⟨0, 1, {0}⟩]⟩]
    precedence := [⟨0, 1, {0}⟩]
    linearExtension := [0, 1]
    precedenceViolations := [] }

theorem decoded_runtime_receipt_valid :
    valid runtimeSemantics runtimeReceipt = true := by
  native_decide

#print axioms decoded_runtime_receipt_valid
end DarkTower.WarMachine.ConstructionReceipt.RuntimeWitness
