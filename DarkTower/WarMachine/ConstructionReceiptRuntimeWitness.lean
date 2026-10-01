import DarkTower.WarMachine.ConstructionReceipt

/-! GENERATED FILE — DO NOT EDIT.
Source SHA-256: 02abb3b41d94ab43600da74da0231985a7100d99901a5a34dc8879fbe26479df
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
    meets := [⟨0, 1, 1, [⟨0, 1, {0}⟩], []⟩]
    precedence := [⟨0, 1, {0}⟩]
    linearExtension := [0, 1]
    precedenceViolations := [] }

theorem decoded_runtime_receipt_valid :
    valid runtimeSemantics runtimeReceipt = true := by
  native_decide

#print axioms decoded_runtime_receipt_valid
end DarkTower.WarMachine.ConstructionReceipt.RuntimeWitness
