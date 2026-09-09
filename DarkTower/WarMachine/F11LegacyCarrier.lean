import DarkTower.WarMachine.Holes

/-! # F11 legacy pricing carrier

These declarations pin the carrier that preceded
`RULINGS-walkthrough-2026-09-09.md` Item 18a and was replaced by commit
`ae9dc5b58e`. The F11 pricing theorems measured this carrier, so their subject
remains this byte-faithful local copy rather than the revised live interface.
-/

namespace DarkTower.WarMachine.Holes

structure LegacyReceipt where
  citesTextOrEdges : Prop
  scoreAlone : Prop

def LegacyReceipt.nonSelfCertifying (receipt : LegacyReceipt) : Prop :=
  receipt.citesTextOrEdges ∧ ¬ receipt.scoreAlone

structure LegacyFindResult (P : Type*) where
  selected : Set P
  receipts : P → Option LegacyReceipt
  absence : Option TypedAbsence

end DarkTower.WarMachine.Holes
