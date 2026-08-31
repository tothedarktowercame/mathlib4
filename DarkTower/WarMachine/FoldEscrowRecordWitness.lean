import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.FoldEscrowRecordWitness

open Holes

def matching : FoldEscrowRecord Nat Nat Unit Unit Unit :=
  ⟨7, 14, (), (), ()⟩

/-- A matching reconstructed digest is reconstructible by definition. -/
theorem matching_is_reconstructible :
    matching.reconstructible (fun n => n + 0) (fun n => n * 2) := by
  norm_num [FoldEscrowRecord.reconstructible, matching]

def mismatching : FoldEscrowRecord Nat Nat Unit Unit Unit :=
  ⟨7, 15, (), (), ()⟩

/-- The same prompt inputs with a different stored digest are not reconstructible. -/
theorem mismatch_is_not_reconstructible :
    ¬ mismatching.reconstructible (fun n => n + 0) (fun n => n * 2) := by
  norm_num [FoldEscrowRecord.reconstructible, mismatching]

end DarkTower.WarMachine.FoldEscrowRecordWitness
