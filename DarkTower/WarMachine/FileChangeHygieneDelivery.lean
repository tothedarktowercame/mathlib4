/-!
# File-change hygiene delivery admission

VERIFY-time prototype for `M-file-change-hygiene`.  This is the formal half of
the mission's informal/formal pair: the mission ARGUE explains why these checks
prevent the recorded failures; this module makes an admitted handoff imply that
every check succeeded.

The booleans denote checks performed by a future runtime adapter.  This module
does not attest that the adapter exists or that a particular event occurred.
-/

namespace DarkTower.WarMachine.FileChangeHygieneDelivery

/-- Evidence required at a file-change consumer boundary.

`authorityReconstructable` makes the event stream a hint rather than the source
of truth.  `consumerOwned` and `drainWithinBound` separate nominal ownership
from demonstrated capacity.  The remaining fields encode the settlement,
retention, red-to-work, hold, and ended-owner obligations from DERIVE. -/
structure Evidence where
  identityChecked : Bool
  authorityReconstructable : Bool
  consumerOwned : Bool
  drainWithinBound : Bool
  settlementBoundaryChecked : Bool
  retentionOrRebuildChecked : Bool
  redRoutesToWork : Bool
  holdHasDeadline : Bool
  endedOwnerTransfers : Bool
  deriving DecidableEq, Repr

/-- A handoff is admitted only when all hygiene boundary checks hold. -/
def admitted (e : Evidence) : Bool :=
  e.identityChecked && e.authorityReconstructable && e.consumerOwned &&
    e.drainWithinBound && e.settlementBoundaryChecked &&
    e.retentionOrRebuildChecked && e.redRoutesToWork &&
    e.holdHasDeadline && e.endedOwnerTransfers

theorem admitted_iff_checked (e : Evidence) : admitted e = true ↔
    e.identityChecked = true ∧
    e.authorityReconstructable = true ∧
    e.consumerOwned = true ∧
    e.drainWithinBound = true ∧
    e.settlementBoundaryChecked = true ∧
    e.retentionOrRebuildChecked = true ∧
    e.redRoutesToWork = true ∧
    e.holdHasDeadline = true ∧
    e.endedOwnerTransfers = true := by
  simp [admitted, Bool.and_eq_true, and_assoc]

theorem missing_authority_rebuild_refused (e : Evidence)
    (h : e.authorityReconstructable = false) : admitted e = false := by
  simp [admitted, h]

theorem unnamed_consumer_refused (e : Evidence)
    (h : e.consumerOwned = false) : admitted e = false := by
  simp [admitted, h]

theorem unstable_drain_refused (e : Evidence)
    (h : e.drainWithinBound = false) : admitted e = false := by
  simp [admitted, h]

theorem unsettled_handoff_refused (e : Evidence)
    (h : e.settlementBoundaryChecked = false) : admitted e = false := by
  simp [admitted, h]

theorem red_without_work_refused (e : Evidence)
    (h : e.redRoutesToWork = false) : admitted e = false := by
  simp [admitted, h]

theorem dead_owner_without_transfer_refused (e : Evidence)
    (h : e.endedOwnerTransfers = false) : admitted e = false := by
  simp [admitted, h]

end DarkTower.WarMachine.FileChangeHygieneDelivery
