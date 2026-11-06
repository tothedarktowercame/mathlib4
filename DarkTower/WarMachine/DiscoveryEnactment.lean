/-!
# Discovery enactment: a find-out selection obliges a find-out action

DRAFT for Joe's go (claude-6, 2026-11-06). Not yet a contract.

`SelectionArgument` decides which selection argument wins; `R20Step` records
which target it returns.  Neither says what the winning argument obliges the
click to *do*.  The task-selection pattern `find-out-before-building` is
explicit: "Select the discovery as its own task (find out and propose; no
edits), review its answer, and then select the build."  Joe (2026-11-06): the
War Machine was correct to choose undetermined items, but incorrect "to treat
them as an explicit TODO list".

This module states the join.

* Each executable outer cascade declares an enactment mode
  (`futon3/library/task-selection/executable-steps.edn`, `:enactment-mode`).
* The enacted mode must equal the declared mode of the selected cascade.
* A discovery click that did its job is productive work whose artifact is a
  reviewed finding, not a commit.  It is not a refusal, so it is not one of the
  three terminals of `RefusalLegality`.  It is legal exactly when every check
  below succeeded.

As in `RefusalLegality`, the booleans denote checks performed by the runtime
validator; this module does not attest that the validator exists.
-/

namespace DarkTower.WarMachine.DiscoveryEnactment

inductive EnactmentMode where
  | implementation | discovery
  deriving DecidableEq, Repr

/-- The mode the selected outer cascade declares, as retained by the click
(the FOBB-A enactment pin). `none` = the cascade declared no mode. -/
structure EnactmentPin where
  declared : Option EnactmentMode
  enacted : EnactmentMode
  deriving DecidableEq, Repr

/-- The click enacted what the selection declared.  An undeclared mode is never
conforming: there is no default. -/
def pinConforms (p : EnactmentPin) : Bool :=
  match p.declared with
  | some m => decide (m = p.enacted)
  | none => false

theorem undeclared_not_conforming (e : EnactmentMode) :
    pinConforms ⟨none, e⟩ = false := rfl

theorem discovery_selection_forbids_implementation :
    pinConforms ⟨some .discovery, .implementation⟩ = false := by
  decide

/-- A per-item verdict of a discovery answer. -/
inductive Verdict where
  | current | blocked | likelyOutdated
  deriving DecidableEq, Repr

structure DiscoveryEvidence where
  pin : EnactmentPin
  /-- The answer parsed as the discovery result schema, bound to the selected
  target and selection pin. -/
  resultValid : Bool
  /-- Every item has a verdict and file:line evidence; every blocked item
  carries at least one question. -/
  itemsComplete : Bool
  /-- An independent reviewer accepted the answer. -/
  reviewed : Bool
  /-- The target's repository head and source pin are unchanged across the
  discovery turn. -/
  targetUnchanged : Bool
  /-- No implementation author was dispatched in this click. -/
  noImplementationDispatch : Bool
  deriving DecidableEq, Repr

def discoveryComplete (e : DiscoveryEvidence) : Bool :=
  pinConforms e.pin && decide (e.pin.enacted = .discovery) &&
  e.resultValid && e.itemsComplete && e.reviewed &&
  e.targetUnchanged && e.noImplementationDispatch

theorem discoveryComplete_iff (e : DiscoveryEvidence) :
    discoveryComplete e = true ↔
      pinConforms e.pin = true ∧ e.pin.enacted = .discovery ∧
      e.resultValid = true ∧ e.itemsComplete = true ∧ e.reviewed = true ∧
      e.targetUnchanged = true ∧ e.noImplementationDispatch = true := by
  simp [discoveryComplete, Bool.and_eq_true, and_assoc]

/-- A discovery that edited its target is not a completed discovery. -/
theorem mutation_not_complete (e : DiscoveryEvidence)
    (h : e.targetUnchanged = false) : discoveryComplete e = false := by
  simp [discoveryComplete, h]

/-- An unreviewed answer cannot close. -/
theorem unreviewed_not_complete (e : DiscoveryEvidence)
    (h : e.reviewed = false) : discoveryComplete e = false := by
  simp [discoveryComplete, h]

/-- Dispatching an implementation author in a discovery click breaks it. -/
theorem implementation_dispatch_not_complete (e : DiscoveryEvidence)
    (h : e.noImplementationDispatch = false) : discoveryComplete e = false := by
  simp [discoveryComplete, h]

/-- What a completed discovery contributes to the next selection: an
observation, not an action.  `current` admits a later build candidate,
`blocked` supplies blockers (a cited ambiguity among them goes through the C2
wire of `RefusalLegality`, not through this module), `likelyOutdated`
requests the operator's disposition. -/
inductive NextEvidence where
  | buildCandidate | blockers | dispositionRequest
  deriving DecidableEq, Repr

def nextEvidence : Verdict → NextEvidence
  | .current => .buildCandidate
  | .blocked => .blockers
  | .likelyOutdated => .dispositionRequest

/-- A discovery never dispatches the build in the same click: the verdict
`current` yields a candidate for a later selection, nothing more. -/
theorem current_is_candidate_not_action :
    nextEvidence .current = .buildCandidate := rfl

end DarkTower.WarMachine.DiscoveryEnactment
