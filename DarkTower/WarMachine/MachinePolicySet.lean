import DarkTower.WarMachine.F12RuledCarrier
import DarkTower.WarMachine.MachineAction

/-!
# Machine candidate action space π

`select-action` receives a ranked list on every branch.  The boundary and the
two strategic laws decide how that list is consumed; they do not introduce a
different candidate carrier.  This module exposes the list's extensional
space through the `CandidateActionSpace` already used by F12's ruled organise
signature.
-/

namespace DarkTower.WarMachine.MachinePolicySet

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineAction

/-- The candidate action space represented by the ranked list consumed by
`select-action` (`futon2:src/futon2/aif/policy.clj:672-862`). -/
def machinePolicySet (ranked : List Candidate) : CandidateActionSpace Candidate :=
  {candidate | candidate ∈ ranked}

/-- The three production rules all return the same carrier type while
preserving which ranked representation they actually inspect: controller-head
reads `ranked`, and both posterior argmax branches read `scored`
(`futon2:src/futon2/aif/policy.clj:567-594,809-838`). -/
def selectionPolicySet (boundary : SelectionBoundary) (law : StrategicLaw)
    (fPiEntered anyHabitPrior : Bool) (ranked scored : List Candidate) :
    CandidateActionSpace Candidate :=
  match boundary with
  | .strategicRecommendation =>
      if law = .fullScorePosterior ∧ fPiEntered
      then machinePolicySet (strategicCandidates scored)
      else machinePolicySet (strategicCandidates ranked)
  | .actuation =>
      if anyHabitPrior then machinePolicySet scored else machinePolicySet ranked

/-- The production fixture used by `MachineActionWitness` has exactly its two
ranked candidates in the carrier. -/
theorem productionFixtureReadback :
    machinePolicySet [⟨0, 0, false⟩, ⟨1, 1, false⟩] =
      ({⟨0, 0, false⟩, ⟨1, 1, false⟩} : CandidateActionSpace Candidate) := by
  ext candidate
  simp [machinePolicySet]

/-- Readback of the three selector rules on the production fixture: the
controller-head branch, strategic posterior branch, and actuation habit branch
all range over candidates 0 and 1. -/
theorem productionRulesReadback :
    let ranked := [⟨0, 0, false⟩, ⟨1, 1, false⟩]
    let scored := [⟨0, 0, false⟩, ⟨1, 2, false⟩]
    (selectionPolicySet .strategicRecommendation .controllerHead true false ranked scored).image
        Candidate.id = {0, 1} ∧
    (selectionPolicySet .strategicRecommendation .fullScorePosterior true false ranked scored).image
        Candidate.id = {0, 1} ∧
    (selectionPolicySet .actuation .controllerHead true true ranked scored).image
        Candidate.id = {0, 1} := by
  dsimp
  constructor
  · ext n
    simp [selectionPolicySet, machinePolicySet, strategicCandidates, eq_comm]
  · constructor
    · ext n
      simp [selectionPolicySet, machinePolicySet, strategicCandidates, eq_comm]
    · ext n
      simp [selectionPolicySet, machinePolicySet, eq_comm]

#print axioms CandidateActionSpace
#print axioms machinePolicySet
#print axioms productionFixtureReadback
#print axioms productionRulesReadback

end DarkTower.WarMachine.MachinePolicySet
