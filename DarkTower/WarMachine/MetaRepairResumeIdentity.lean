import Mathlib

/-!
# Resuming a META repair binds its retained author receipt to the ledger

The coordinator may resume a transaction only when its retained author
receipt is the same receipt and patch the ledger already admitted.  This is a
structural identity law, not authentication of either receipt or patch.
-/

namespace DarkTower.WarMachine

inductive MetaRepairState where
  | claimed | authored | reviewed | enacted
  deriving DecidableEq, Repr

structure AuthorReceiptIdentity where
  receiptPin : String
  patchSha : String
  deriving DecidableEq, Repr

def resumeIdentityOK (state : MetaRepairState)
    (ledgerAuthor : AuthorReceiptIdentity)
    (transactionAuthor : Option AuthorReceiptIdentity) : Prop :=
  match state with
  | .claimed => True
  | .authored | .reviewed | .enacted => transactionAuthor = some ledgerAuthor

theorem matching_enacted_resume_allowed (author : AuthorReceiptIdentity) :
    resumeIdentityOK .enacted author (some author) := rfl

theorem empty_enacted_resume_refused (author : AuthorReceiptIdentity) :
    ¬ resumeIdentityOK .enacted author none := by
  simp [resumeIdentityOK]

end DarkTower.WarMachine
