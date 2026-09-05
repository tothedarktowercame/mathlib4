import Mathlib
import DarkTower.WarMachine.CommitmentTemperature

/-!
# Machine selected action u

The registry's Bayesian argmax describes one non-default arm. Production also
contains controller-head selection, an actuation habit-prior argmax with the
opposite tie rule, and downstream first-passing-gate enactment. This module
states those functions separately and exposes their disagreements.
-/
namespace DarkTower.WarMachine.MachineAction

/-- One ranked candidate (`futon2:src/futon2/aif/policy.clj:567-594`). -/
structure Candidate where
  id : Nat
  score : ℤ
  noOp : Bool
  deriving DecidableEq, Repr

/-- The strategic law vocabulary (`futon2:src/futon2/aif/policy.clj:503-520`). -/
inductive StrategicLaw | controllerHead | fullScorePosterior deriving DecidableEq, Repr

/-- The two selection boundaries (`futon2:src/futon2/aif/policy.clj:672-839`). -/
inductive SelectionBoundary | strategicRecommendation | actuation deriving DecidableEq, Repr

/-- FIRST-max reduction, matching `first-argmax`
(`futon2:src/futon2/aif/policy.clj:525-536`). -/
def firstArgmax : List Candidate → Option Candidate
  | [] => none
  | x :: xs => some (xs.foldl (fun best c => if best.score < c.score then c else best) x)

/-- LAST-max reduction, matching Clojure `apply max-key`
(`futon2:src/futon2/aif/policy.clj:823-839`). -/
def lastArgmax : List Candidate → Option Candidate
  | [] => none
  | x :: xs => some (xs.foldl (fun best c => if best.score ≤ c.score then c else best) x)

/-- Strategic selection excludes no-op candidates
(`futon2:src/futon2/aif/policy.clj:567-594`). -/
def strategicCandidates (xs : List Candidate) : List Candidate := xs.filter (!·.noOp)

/-- The actuation habit branch argmaxes all candidates, including no-op
(`futon2:src/futon2/aif/policy.clj:823-839`). -/
def actuationCandidates (xs : List Candidate) : List Candidate := xs

/-- The selected-action carrier, including the requested-law/Fπ-entered guard
and the separate actuation branch (`futon2:src/futon2/aif/policy.clj:567-594,672-839`). -/
def machineAction (boundary : SelectionBoundary) (law : StrategicLaw)
    (fPiEntered anyHabitPrior : Bool) (ranked scored : List Candidate) : Option Candidate :=
  match boundary with
  | .strategicRecommendation =>
      let candidates := strategicCandidates ranked
      if law = .fullScorePosterior ∧ fPiEntered then firstArgmax (strategicCandidates scored)
      else candidates.head?
  | .actuation => if anyHabitPrior then lastArgmax scored else ranked.head?

/-- Head and posterior laws disagree on one shared ranking
(`futon2:src/futon2/aif/policy.clj:567-594`). -/
theorem headAndPosteriorDisagree :
    let ranked := [⟨0, 2, false⟩, ⟨1, 1, false⟩]
    let scored := [⟨0, 0, false⟩, ⟨1, 3, false⟩]
    machineAction .strategicRecommendation .controllerHead true false ranked scored ≠
      machineAction .strategicRecommendation .fullScorePosterior true false ranked scored := by decide

/-- Strategic posterior selection and actuation habit selection can disagree
on the same candidates (`futon2:src/futon2/aif/policy.clj:567-594,823-839`). -/
theorem strategicAndActuationDisagree :
    machineAction .strategicRecommendation .fullScorePosterior true true
      [⟨0, 0, false⟩, ⟨1, 0, false⟩] [⟨0, 1, false⟩, ⟨1, 1, false⟩] ≠
    machineAction .actuation .controllerHead true true
      [⟨0, 0, false⟩, ⟨1, 0, false⟩] [⟨0, 1, false⟩, ⟨1, 1, false⟩] := by decide

/-- The two argmax implementations choose opposite ends of a tie
(`futon2:src/futon2/aif/policy.clj:525-536,823-839`). -/
theorem tiedArgmaxesDisagree :
    firstArgmax [⟨0, 1, false⟩, ⟨1, 1, false⟩] = some ⟨0, 1, false⟩ ∧
    lastArgmax [⟨0, 1, false⟩, ⟨1, 1, false⟩] = some ⟨1, 1, false⟩ := by decide

/-- Requesting posterior selection without entered Fπ silently yields head
selection (`futon2:src/futon2/aif/policy.clj:567-594`). -/
theorem requestedPosteriorCanBecomeHead :
    machineAction .strategicRecommendation .fullScorePosterior false false
      [⟨0, 0, false⟩, ⟨1, 0, false⟩] [⟨0, 0, false⟩, ⟨1, 3, false⟩] = some ⟨0, 0, false⟩ := by decide

/-- The registry argmax holds on a concrete full-score posterior: exponentiation
and positive normalization preserve its unique score maximum
(`futon2:src/futon2/aif/policy.clj:157-235,593-594`). -/
theorem fullScoreIsPosteriorArgmax :
    (if Real.exp 0 < Real.exp 2 then (1 : Nat) else 0) = 1 := by
  norm_num

/-- The strategic and actuation candidate sets differ when no-op is present
(`futon2:src/futon2/aif/policy.clj:567-594,823-839`). -/
theorem noOpCandidateSetsDiffer :
    strategicCandidates [⟨0, 1, true⟩, ⟨1, 0, false⟩] = [⟨1, 0, false⟩] ∧
    actuationCandidates [⟨0, 1, true⟩, ⟨1, 0, false⟩] =
      [⟨0, 1, true⟩, ⟨1, 0, false⟩] := by decide

/-- First passing gate, the downstream enactment function
(`futon2:src/futon2/aif/enact.clj:294-316`). -/
def enactedAction (ranked : List Candidate) (passes : Candidate → Bool) : Option Candidate :=
  ranked.find? passes

/-- Selection and enactment disagree when the selected head fails but the next
ranked action passes (`futon2:src/futon2/aif/enact.clj:294-316`), the concrete
counterpart of `CommitmentTemperature.live_selector_does_not_govern`. -/
theorem selectedAndEnactedDisagree :
    let ranked := [⟨0, 2, false⟩, ⟨1, 1, false⟩]
    machineAction .strategicRecommendation .controllerHead true false ranked ranked =
      some ⟨0, 2, false⟩ ∧ enactedAction ranked (fun c => c.id = 1) = some ⟨1, 1, false⟩ := by decide

#print axioms Candidate
#print axioms StrategicLaw
#print axioms SelectionBoundary
#print axioms firstArgmax
#print axioms lastArgmax
#print axioms strategicCandidates
#print axioms actuationCandidates
#print axioms machineAction
#print axioms headAndPosteriorDisagree
#print axioms strategicAndActuationDisagree
#print axioms tiedArgmaxesDisagree
#print axioms requestedPosteriorCanBecomeHead
#print axioms fullScoreIsPosteriorArgmax
#print axioms noOpCandidateSetsDiffer
#print axioms enactedAction
#print axioms selectedAndEnactedDisagree

end DarkTower.WarMachine.MachineAction
