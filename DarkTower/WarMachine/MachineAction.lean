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

/-- The strategic law vocabulary (`futon2:src/futon2/aif/policy.clj:503-524`). -/
inductive StrategicLaw | controllerHead | fullScorePosterior deriving DecidableEq, Repr

/-- The two selection boundaries (`futon2:src/futon2/aif/policy.clj:672-862`). -/
inductive SelectionBoundary | strategicRecommendation | actuation deriving DecidableEq, Repr

/-- FIRST-max reduction, matching `first-argmax`
(`futon2:src/futon2/aif/policy.clj:525-536`). -/
def firstArgmax : List Candidate → Option Candidate
  | [] => none
  | x :: xs => some (xs.foldl (fun best c => if best.score < c.score then c else best) x)

/-- LAST-max reduction, matching Clojure `apply max-key`
(`futon2:src/futon2/aif/policy.clj:833-838`). -/
def lastArgmax : List Candidate → Option Candidate
  | [] => none
  | x :: xs => some (xs.foldl (fun best c => if best.score ≤ c.score then c else best) x)

/-- Strategic selection excludes no-op candidates
(`futon2:src/futon2/aif/policy.clj:567-594`). -/
def strategicCandidates (xs : List Candidate) : List Candidate := xs.filter (!·.noOp)

/-- The actuation habit branch argmaxes all candidates, including no-op
(`futon2:src/futon2/aif/policy.clj:833-838`). -/
def actuationCandidates (xs : List Candidate) : List Candidate := xs

/-- The selected-action carrier, including the requested-law/Fπ-entered guard
and the separate actuation branch (`futon2:src/futon2/aif/policy.clj:567-594,672-862`). -/
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
on the same candidates (`futon2:src/futon2/aif/policy.clj:567-594,833-838`). -/
theorem strategicAndActuationDisagree :
    machineAction .strategicRecommendation .fullScorePosterior true true
      [⟨0, 0, false⟩, ⟨1, 0, false⟩] [⟨0, 1, false⟩, ⟨1, 1, false⟩] ≠
    machineAction .actuation .controllerHead true true
      [⟨0, 0, false⟩, ⟨1, 0, false⟩] [⟨0, 1, false⟩, ⟨1, 1, false⟩] := by decide

/-- The two argmax implementations choose opposite ends of a tie
(`futon2:src/futon2/aif/policy.clj:525-536,833-838`). -/
theorem tiedArgmaxesDisagree :
    firstArgmax [⟨0, 1, false⟩, ⟨1, 1, false⟩] = some ⟨0, 1, false⟩ ∧
    lastArgmax [⟨0, 1, false⟩, ⟨1, 1, false⟩] = some ⟨1, 1, false⟩ := by decide

/-- Requesting posterior selection without entered Fπ yields HEAD selection.
It is not concealed: the decision records
`:selection-law {:requested :full-score-posterior :applied :controller-head
:refusal {:reason :no-f-pi-opts :effect :fell-back-to-controller-head}}`.
The statement is the conditional one — the law NAME alone does not determine
the rule; the pair (law, Fπ-entered) does
(`futon2:src/futon2/aif/policy.clj:582,593-594`). -/
theorem requestedPosteriorCanBecomeHead :
    machineAction .strategicRecommendation .fullScorePosterior false false
      [⟨0, 0, false⟩, ⟨1, 0, false⟩] [⟨0, 0, false⟩, ⟨1, 3, false⟩] = some ⟨0, 0, false⟩ := by decide

/-- The production selection score `ln E − G/τ − F_π`, the vector the posterior
normalises (`futon2:src/futon2/aif/policy.clj:157-212`). -/
noncomputable def selectionScore (g lnE fPi tau : ℝ) : ℝ := lnE - g / tau - fPi

/-- One unnormalised posterior weight divided by the partition function; this is
what `softmax-weights` returns (`futon2:src/futon2/aif/policy.clj:215-236`). -/
noncomputable def posteriorWeight (z score : ℝ) : ℝ := Real.exp score / z

/-- THE REGISTRY'S ARGMAX IS THE SCORE ARGMAX. Exponentiation is strictly
monotone and division by a positive partition function preserves order, so
`Q(π)` and `selection-scores` induce the SAME order on the candidates and
therefore have the same argmax. This is what licenses reading the row's
`argmax_u Σ_π δ(u,π) Q(π)` as the `:full-score-posterior` rule
(`futon2:src/futon2/aif/policy.clj:215-236`). -/
theorem posteriorOrderIsScoreOrder {z s t : ℝ} (hz : 0 < z) :
    posteriorWeight z s < posteriorWeight z t ↔ s < t := by
  rw [posteriorWeight, posteriorWeight, div_lt_div_iff_of_pos_right hz, Real.exp_lt_exp]

/-- The same statement on the production fixture the readback measures: with
G = ⟨0, 1⟩, ln E = ⟨0, 3⟩, F_π = 0 and τ = 1 the scores are ⟨0, 2⟩ and the
posterior ranks the two candidates in that same order, so the Bayesian-model
-average argmax and the score argmax name the same action
(`futon2:src/futon2/aif/policy.clj:157-236`). -/
theorem fullScoreIsPosteriorArgmax {z : ℝ} (hz : 0 < z) :
    selectionScore 0 0 0 1 < selectionScore 1 3 0 1 ∧
    posteriorWeight z (selectionScore 0 0 0 1) <
      posteriorWeight z (selectionScore 1 3 0 1) := by
  have h : selectionScore 0 0 0 1 < selectionScore 1 3 0 1 := by
    simp [selectionScore]
  exact ⟨h, (posteriorOrderIsScoreOrder hz).mpr h⟩

/-- The strategic and actuation candidate sets differ when no-op is present
(`futon2:src/futon2/aif/policy.clj:567-594,833-838`). -/
theorem noOpCandidateSetsDiffer :
    strategicCandidates [⟨0, 1, true⟩, ⟨1, 0, false⟩] = [⟨1, 0, false⟩] ∧
    actuationCandidates [⟨0, 1, true⟩, ⟨1, 0, false⟩] =
      [⟨0, 1, true⟩, ⟨1, 0, false⟩] := by decide

/-- First passing gate, the downstream enactment function
(`futon2:src/futon2/aif/enact.clj:294-339`, the rule at `:320`). -/
def enactedAction (ranked : List Candidate) (passes : Candidate → Bool) : Option Candidate :=
  ranked.find? passes

/-- Selection and enactment disagree when the selected head fails but the next
ranked action passes (`futon2:src/futon2/aif/enact.clj:294-339`, the rule at `:320`), the concrete
counterpart of `CommitmentTemperature.live_selector_does_not_govern`. -/
theorem selectedAndEnactedDisagree :
    let ranked := [⟨0, 2, false⟩, ⟨1, 1, false⟩]
    machineAction .strategicRecommendation .controllerHead true false ranked ranked =
      some ⟨0, 2, false⟩ ∧ enactedAction ranked (fun c => c.id = 1) = some ⟨1, 1, false⟩ := by decide

/-- The live default boundary: `select-action`'s own `:or` default is
`:actuation`, the branch on which neither τ nor the posterior enters at all
(`futon2:src/futon2/aif/policy.clj:753`). -/
def productionDefaultBoundary : SelectionBoundary := .actuation

/-- The live default strategic law, off by default and J-gated
(`futon2:src/futon2/aif/policy.clj:520-524`). -/
def productionDefaultLaw : StrategicLaw := .controllerHead

/-- The rule the registry's `:formal` line names — the argmax of the recorded
posterior — is `:full-score-posterior`
(`futon2:holes/labs/wm-contract/aif-equations.edn`, `:id :action`). -/
def registryLaw : StrategicLaw := .fullScorePosterior

/-- THE DEFAULT RULE IS NOT THE REGISTRY'S RULE, at both levels: the default
law is not the posterior law, and the default boundary is not even the one on
which a law can be chosen (`policy.clj:520-524`; `policy.clj:753`). -/
theorem defaultRuleIsNotTheRegistryRule :
    productionDefaultLaw ≠ registryLaw ∧
    productionDefaultBoundary ≠ SelectionBoundary.strategicRecommendation := by decide

/-- Under the production defaults the selected action is the G-ordered head and
nothing else: the posterior the tick records is not read
(`futon2:src/futon2/aif/policy.clj:753,809-813`). -/
theorem defaultSelectionIsTheHead (ranked scored : List Candidate) :
    machineAction productionDefaultBoundary productionDefaultLaw true false ranked scored =
      ranked.head? := by
  simp [machineAction, productionDefaultBoundary]

/-- THE HABIT PRIOR ALONE MOVES THE CHOICE, with no tie anywhere. On the SAME
candidates the actuation branch takes the G-head when every `:habit-prior-bias`
is zero and the argmax of `−G/τ + ln E` when one is not, and those are different
actions (`futon2:src/futon2/aif/policy.clj:809-813,833-838`). -/
theorem habitPriorAloneMovesTheChoice :
    let ranked := [⟨0, 0, false⟩, ⟨1, 1, false⟩]
    let scored := [⟨0, 0, false⟩, ⟨1, 2, false⟩]
    machineAction .actuation productionDefaultLaw true false ranked scored ≠
      machineAction .actuation productionDefaultLaw true true ranked scored := by decide

/-- THE NO-OP EXCLUSION REACHES THE ACTION, not just the candidate list. When
`:no-op` carries the winning score the actuation branch selects it (and the
abstain test then fires) while the strategic boundary, declared non-abstaining,
cannot see it at all and selects the next entry
(`futon2:src/futon2/aif/policy.clj:567-594,833-838`). -/
theorem noOpExclusionMovesTheChoice :
    let ranked := [⟨0, 3, true⟩, ⟨1, 1, false⟩]
    machineAction .actuation productionDefaultLaw true true ranked ranked =
      some ⟨0, 3, true⟩ ∧
    machineAction .strategicRecommendation productionDefaultLaw true false ranked ranked =
      some ⟨1, 1, false⟩ := by decide

/-- The abstain test, applied AFTER the argmax and in G units: `:no-op` present
and its controller-score exceeding the chosen entry's by less than ε
(`futon2:src/futon2/aif/policy.clj:840-846`). -/
def abstains (noOpG chosenG eps : ℚ) : Bool := noOpG - chosenG < eps

/-- THE SELECTED ACTION CAN BE `:abstain`, which is not in the range of the
registry's argmax at all. On the fixture where the habit prior makes `:no-op`
the actuation argmax, the chosen entry IS the no-op, so the G margin is zero and
the test fires at production's ε = 1/100
(`futon2:src/futon2/aif/policy.clj:833-846`). -/
theorem noOpArgmaxAbstains : abstains 1 1 (1/100) = true := by
  norm_num [abstains]

/-- SAME LAW, DIFFERENT RULE. With `:full-score-posterior` requested throughout,
the action depends on whether Fπ entered this tick; the law name alone does not
determine it (`futon2:src/futon2/aif/policy.clj:582,593-594`). -/
theorem requestedPosteriorDependsOnFPiEntered :
    let ranked := [⟨0, 0, false⟩, ⟨1, 0, false⟩]
    let scored := [⟨0, 0, false⟩, ⟨1, 3, false⟩]
    machineAction .strategicRecommendation registryLaw false false ranked scored ≠
      machineAction .strategicRecommendation registryLaw true false ranked scored := by decide

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
#print axioms selectionScore
#print axioms posteriorWeight
#print axioms posteriorOrderIsScoreOrder
#print axioms productionDefaultBoundary
#print axioms productionDefaultLaw
#print axioms registryLaw
#print axioms defaultRuleIsNotTheRegistryRule
#print axioms defaultSelectionIsTheHead
#print axioms habitPriorAloneMovesTheChoice
#print axioms noOpExclusionMovesTheChoice
#print axioms abstains
#print axioms noOpArgmaxAbstains
#print axioms requestedPosteriorDependsOnFPiEntered
#print axioms selectedAndEnactedDisagree

end DarkTower.WarMachine.MachineAction
