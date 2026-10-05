import DarkTower.WarMachine.EvidenceFromTheProcess
import DarkTower.WarMachine.PolicyVariationalFreeEnergy
import Mathlib.Tactic

/-!
# R11: decentralized joint action

When several agents work on the same thing, each carries in its own model a
belief about their shared goal and about what the others are doing. Each
updates that belief by observing what the others actually do, and acts so that
its own intention can be read. Their actions compose when those beliefs agree;
nothing above the agents has to arrange them.

Maisto, Donnarumma and Pezzulo (2022), `refs/maisto2022.txt:14-33`, calls this
interactive inference: agents maintain beliefs about a joint goal, update them
from one another's movements, and select legible movements. Its model includes
the other agent's position and joint-goal context (`:268-285`), and measures
alignment by KL divergence between goal beliefs (`:536-552`). Kaufmann et al.
(2021), `refs/kaufmann2021.txt:10-26`, likewise identifies theory of mind and
goal alignment as complementary sources of collective performance.

No coordinator occurs in the carrier below: `jointAction` is assembled solely
from the goals selected by the agents themselves. The completeness contract
also says “resource conservation”; these sources supply no law for it. If
retained, conservation is an additional system requirement, not a consequence
of this interactive-inference account.

A search of rebuilt `futon2/src/futon2/aif/wm/` and its policy-prefix,
precision-carry, and cascade-model dependencies found Agency seats and shared
repository/task evidence, but no agent's generative model containing beliefs
about another agent's actions or a joint goal shared with another agent.
-/

namespace DarkTower.WarMachine.R11JointAction

open scoped BigOperators
noncomputable section

variable {Agent Part : Type*} [Fintype Agent] [Nonempty Agent]
  [DecidableEq Agent] [DecidableEq Part]

/-- A joint goal assigns every agent the part it is to play. -/
abbrev JointGoal (Agent Part : Type*) := Agent → Part
abbrev GoalBelief (Agent Part : Type*) := JointGoal Agent Part → ℝ

def CertainOf (belief : GoalBelief Agent Part) (goal : JointGoal Agent Part) : Prop :=
  belief goal = 1 ∧ ∀ other, other ≠ goal → belief other = 0

/-- An agent certain of a goal executes its own component of that goal. -/
def playsPart (agent : Agent) (goal : JointGoal Agent Part) : Part := goal agent

/-- The composed action has no coordinator argument: each agent contributes
the component of the goal it selected locally. -/
def jointAction (selected : Agent → JointGoal Agent Part) : JointGoal Agent Part :=
  fun agent => selected agent agent

def CoherentAction (coherent : Set (JointGoal Agent Part))
    (action : JointGoal Agent Part) : Prop := action ∈ coherent

/-- Agreement composes: common certainty about a coherent goal yields exactly
that goal as the joint action. -/
theorem agreement_composes (coherent : Set (JointGoal Agent Part))
    (goal : JointGoal Agent Part) (hg : goal ∈ coherent)
    (belief : Agent → GoalBelief Agent Part)
    (agrees : ∀ a, CertainOf (belief a) goal) :
    jointAction (fun _ => goal) = goal ∧
      CoherentAction coherent (jointAction (fun _ => goal)) := by
  have same : jointAction (fun _ => goal) = goal := by funext a; rfl
  exact ⟨same, same.symm ▸ hg⟩

/-! A concrete conflict control: both uniform-colour goals are coherent, but
locally following different certain goals produces a mixed action. -/

abbrev TwoAgents := Fin 2
inductive Colour | red | blue deriving DecidableEq

def redGoal : JointGoal TwoAgents Colour := fun _ => .red
def blueGoal : JointGoal TwoAgents Colour := fun _ => .blue
def colourCoherent : Set (JointGoal TwoAgents Colour) := {redGoal, blueGoal}
def disagreeingSelection : TwoAgents → JointGoal TwoAgents Colour
  | 0 => redGoal
  | 1 => blueGoal

theorem disagreement_can_conflict :
    redGoal ∈ colourCoherent ∧ blueGoal ∈ colourCoherent ∧
      ¬ CoherentAction colourCoherent (jointAction disagreeingSelection) := by
  constructor
  · exact Set.mem_insert redGoal {blueGoal}
  constructor
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton blueGoal))
  · intro coherent
    change jointAction disagreeingSelection = redGoal ∨
      jointAction disagreeingSelection = blueGoal at coherent
    rcases coherent with red | blue
    · have h := congrFun red (1 : TwoAgents)
      simp [jointAction, disagreeingSelection, redGoal, blueGoal] at h
    · have h := congrFun blue (0 : TwoAgents)
      simp [jointAction, disagreeingSelection, redGoal, blueGoal] at h

/-! ## Watching another agent -/

variable [Fintype (JointGoal Agent Part)] [Nonempty (JointGoal Agent Part)]

def moveLikelihood (other : Agent) :
    EvidenceFromTheProcess.Likelihood (JointGoal Agent Part) Part :=
  fun goal observed => if goal other = observed then 1 else 0

theorem watching_removes_inconsistent_goals
    (prior : GoalBelief Agent Part) (other : Agent) (move : Part)
    (positive : 0 < EvidenceFromTheProcess.evidence prior (moveLikelihood other) move)
    (goal : JointGoal Agent Part) (inconsistent : goal other ≠ move) :
    EvidenceFromTheProcess.posterior prior (moveLikelihood other) move goal = 0 := by
  simp [EvidenceFromTheProcess.posterior, moveLikelihood, inconsistent,
    positive.ne']

/-- After observing both moves through exact-part likelihoods, any goal with
positive posterior support is consistent with both observed components. -/
theorem mutual_observation_supports_jointly_consistent_goals
    (prior : GoalBelief Agent Part) (a b : Agent) (moveA moveB : Part)
    (positiveA : 0 < EvidenceFromTheProcess.evidence prior (moveLikelihood a) moveA)
    (positiveB : 0 < EvidenceFromTheProcess.evidence
      (EvidenceFromTheProcess.posterior prior (moveLikelihood a) moveA)
      (moveLikelihood b) moveB)
    (goal : JointGoal Agent Part)
    (supported : 0 < EvidenceFromTheProcess.posterior
      (EvidenceFromTheProcess.posterior prior (moveLikelihood a) moveA)
      (moveLikelihood b) moveB goal) :
    goal a = moveA ∧ goal b = moveB := by
  constructor
  · by_contra bad
    have hz := watching_removes_inconsistent_goals prior a moveA positiveA goal bad
    have priorZero := hz
    change 0 < EvidenceFromTheProcess.posterior
      (EvidenceFromTheProcess.posterior prior (moveLikelihood a) moveA)
      (moveLikelihood b) moveB goal at supported
    simp only [EvidenceFromTheProcess.posterior] at supported
    simp [moveLikelihood, bad] at supported
  · by_contra bad
    have hz := watching_removes_inconsistent_goals
      (EvidenceFromTheProcess.posterior prior (moveLikelihood a) moveA)
      b moveB positiveB goal bad
    rw [hz] at supported
    exact lt_irrefl 0 supported

/-- A move equally likely under every joint goal is illegible: observing it
leaves the goal belief unchanged. -/
theorem illegible_move_tells_nothing (prior : GoalBelief Agent Part)
    (normal : ∑ g, prior g = 1) (move : Part) (c : ℝ) (hc : 0 < c) :
    EvidenceFromTheProcess.posterior prior (fun _ _ => c) move = prior :=
  EvidenceFromTheProcess.no_evidence_no_change prior _ move normal c hc (fun _ => rfl)

/-! ## Alignment -/

/-- The same finite KL used by the existing variational-free-energy model. -/
def alignmentKL (first second : GoalBelief Agent Part) : ℝ :=
  PolicyVariationalFreeEnergy.klSum first second

theorem alignmentKL_eq_zero_iff (first second : GoalBelief Agent Part)
    (hfirst0 : ∀ g, 0 ≤ first g) (hfirst1 : ∑ g, first g = 1)
    (hsecond0 : ∀ g, 0 ≤ second g) (hsecond1 : ∑ g, second g = 1)
    (support : ∀ g, 0 < first g → 0 < second g) :
    alignmentKL first second = 0 ↔ first = second := by
  rw [alignmentKL,
    PolicyVariationalFreeEnergy.klSum_eq_zero_iff first second
      hfirst0 hfirst1 hsecond0 hsecond1 support]
  exact ⟨fun h => funext h, fun h g => congrFun h g⟩

/-! ## Retained one-step conformance -/

structure AgentStep (Agent Part : Type*) where
  prior : GoalBelief Agent Part
  selectedGoal : JointGoal Agent Part
  played : Part
  observedOther : Agent
  observedMove : Part
  next : GoalBelief Agent Part

structure JointStepRecord (Agent Part : Type*) where
  steps : Agent → AgentStep Agent Part

def StepConforms (agent : Agent) (step : AgentStep Agent Part) : Prop :=
  0 < step.prior step.selectedGoal ∧
  step.played = step.selectedGoal agent ∧
  step.next = EvidenceFromTheProcess.posterior step.prior
    (moveLikelihood step.observedOther) step.observedMove

def JointStepConforms (record : JointStepRecord Agent Part) : Prop :=
  ∀ agent, StepConforms agent (record.steps agent)

theorem unchanged_after_discriminating_move_refused
    (agent other : Agent) (prior : GoalBelief Agent Part)
    (goal : JointGoal Agent Part) (move : Part)
    (selected : JointGoal Agent Part) (hp : 0 < prior selected)
    (positive : 0 < EvidenceFromTheProcess.evidence prior (moveLikelihood other) move)
    (inconsistent : goal other ≠ move) (supported : 0 < prior goal) :
    ¬ StepConforms agent
      ⟨prior, selected, selected agent, other, move, prior⟩ := by
  intro conforms
  have nextEq := congrFun conforms.2.2 goal
  have zero := watching_removes_inconsistent_goals prior other move positive goal inconsistent
  rw [zero] at nextEq
  linarith

theorem false_common_certainty_refused
    (coherent : Set (JointGoal Agent Part)) (goal : JointGoal Agent Part)
    (hg : goal ∈ coherent) (played : JointGoal Agent Part)
    (different : played ≠ goal) :
    ¬ (played = jointAction (fun _ => goal) ∧ CoherentAction coherent played) := by
  rintro ⟨same, _⟩
  apply different
  rw [same]
  funext a
  rfl

end
end DarkTower.WarMachine.R11JointAction
