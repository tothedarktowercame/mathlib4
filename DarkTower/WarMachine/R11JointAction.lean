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

## Sources

The requirement is R11 of the completeness contract
(`ukrn-services-simulation/docs/aif-completeness.md`): "When multiple AIF
agents act on shared state, a coordination layer ensures their actions compose
coherently (resource conservation, no-conflict invariants)."

Maisto, Donnarumma and Pezzulo (2022), `refs/maisto2022.txt:14-33`, call the
theory's account interactive inference: "Each agent maintains probabilistic
beliefs about the joint goal ... and updates them by observing the other
agent's movements, while in turn selecting movements that make his own
intentions legible". Each agent's model includes the other agent's position
and the joint-goal context (`:268-285`), and alignment is measured by the KL
divergence between the agents' goal beliefs (`:536-552`). A move that "is
equally likely if the intended goals are red or blue ... does not provide
diagnostic information" (`:612-624`); an agent that knows the goal takes a
longer route that does. Kaufmann et al. (2021), `refs/kaufmann2021.txt:10-26`,
name theory of mind and goal alignment as the two sources of collective
performance. The model has no coordinator, and none occurs below:
`jointAction` is assembled from the goals the agents select themselves.

The contract's "shared state" and its two invariants are stated in the last
section. Its form comes from Fritz and Liang (2022), Def. 3.6
(`refs/fritzliang2022.txt:505-520`): a diagram of processes composes when it
is acyclic and every wire has exactly one driver ("left monogamy"). Reading a
shared variable as a wire and an agent as a driver is this module's mapping,
first made for pattern gluing in `futon5a/holes/excursions/E-the-dark-tower-3.md`
(Q1); neither paper applies it to agents. Under that reading the contract's
"no-conflict" is at most one writer per variable, and "resource conservation"
is that the variables the agents write add up to the variables there are. Both
follow when the agents agree on who writes what. Maisto et al. state neither.
Acyclicity is not stated here.

## What a record of one joint step must satisfy

`JointStepConforms`: each agent played its own part of a goal to which it gave
positive belief, and its next belief is the posterior given the move it
observed, or its prior when it observed nothing. Silence is not a move: a
belief that changed with no observation does not conform.

As of 2026-10-05 a search of `futon2/src/futon2/aif/wm/` and the namespaces it
requires found no model that holds a belief about another agent's actions or
about a goal shared with another agent, so no record of this form is produced
yet.
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

/-- An agent acts on a goal to which it gives positive belief. -/
def SelectsFrom (belief : GoalBelief Agent Part) (selected : JointGoal Agent Part) : Prop :=
  0 < belief selected

/-- The composed action has no coordinator argument: each agent contributes
the component of the goal it selected locally. -/
def jointAction (selected : Agent → JointGoal Agent Part) : JointGoal Agent Part :=
  fun agent => selected agent agent

def CoherentAction (coherent : Set (JointGoal Agent Part))
    (action : JointGoal Agent Part) : Prop := action ∈ coherent

/-- An agent certain of a goal has no other goal to act on. -/
theorem certain_selects_goal (belief : GoalBelief Agent Part)
    (goal selected : JointGoal Agent Part) (certain : CertainOf belief goal)
    (selects : SelectsFrom belief selected) : selected = goal := by
  by_contra different
  have zero := certain.2 selected different
  unfold SelectsFrom at selects
  linarith

/-- Agreement composes: when every agent is certain of the same coherent goal
and acts on a goal it believes in, the joint action is that goal. -/
theorem agreement_composes (coherent : Set (JointGoal Agent Part))
    (goal : JointGoal Agent Part) (hg : goal ∈ coherent)
    (belief : Agent → GoalBelief Agent Part)
    (selected : Agent → JointGoal Agent Part)
    (agrees : ∀ a, CertainOf (belief a) goal)
    (selects : ∀ a, SelectsFrom (belief a) (selected a)) :
    jointAction selected = goal ∧ CoherentAction coherent (jointAction selected) := by
  have same : jointAction selected = goal := by
    funext a
    show selected a a = goal a
    rw [certain_selects_goal (belief a) goal (selected a) (agrees a) (selects a)]
  refine ⟨same, ?_⟩
  show jointAction selected ∈ coherent
  rw [same]
  exact hg

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
    (goal : JointGoal Agent Part) (inconsistent : goal other ≠ move) :
    EvidenceFromTheProcess.posterior prior (moveLikelihood other) move goal = 0 := by
  simp [EvidenceFromTheProcess.posterior, moveLikelihood, inconsistent]

/-- After observing both moves through exact-part likelihoods, any goal with
positive posterior support is consistent with both observed components. -/
theorem mutual_observation_supports_jointly_consistent_goals
    (prior : GoalBelief Agent Part) (a b : Agent) (moveA moveB : Part)
    (goal : JointGoal Agent Part)
    (supported : 0 < EvidenceFromTheProcess.posterior
      (EvidenceFromTheProcess.posterior prior (moveLikelihood a) moveA)
      (moveLikelihood b) moveB goal) :
    goal a = moveA ∧ goal b = moveB := by
  constructor
  · by_contra bad
    simp only [EvidenceFromTheProcess.posterior] at supported
    simp [moveLikelihood, bad] at supported
  · by_contra bad
    have hz := watching_removes_inconsistent_goals
      (EvidenceFromTheProcess.posterior prior (moveLikelihood a) moveA)
      b moveB goal bad
    rw [hz] at supported
    exact lt_irrefl 0 supported

/-- A move equally likely under every joint goal is illegible: observing it
leaves the goal belief unchanged (`refs/maisto2022.txt:612-624`). -/
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

/-! ## Conformance of one joint step -/

/-- What one agent's record of a joint step carries. `observed` is `none` when
the agent saw no move by another agent during the step. -/
structure AgentStep (Agent Part : Type*) where
  prior : GoalBelief Agent Part
  selectedGoal : JointGoal Agent Part
  played : Part
  observed : Option (Agent × Part)
  next : GoalBelief Agent Part

structure JointStepRecord (Agent Part : Type*) where
  steps : Agent → AgentStep Agent Part

/-- The belief an agent should hold after the step: the posterior given the
move it observed, and the prior unchanged when it observed nothing. -/
def nextBelief (prior : GoalBelief Agent Part) :
    Option (Agent × Part) → GoalBelief Agent Part
  | none => prior
  | some (other, move) =>
      EvidenceFromTheProcess.posterior prior (moveLikelihood other) move

def StepConforms (agent : Agent) (step : AgentStep Agent Part) : Prop :=
  SelectsFrom step.prior step.selectedGoal ∧
  step.played = step.selectedGoal agent ∧
  step.next = nextBelief step.prior step.observed

def JointStepConforms (record : JointStepRecord Agent Part) : Prop :=
  ∀ agent, StepConforms agent (record.steps agent)

/-- The joint action a record reports. -/
def playedAction (record : JointStepRecord Agent Part) : JointGoal Agent Part :=
  fun agent => (record.steps agent).played

/-- In a conforming record whose agents all start certain of one coherent
goal, the parts played are that goal. -/
theorem conforming_common_certainty_plays_goal
    (coherent : Set (JointGoal Agent Part)) (goal : JointGoal Agent Part)
    (hg : goal ∈ coherent) (record : JointStepRecord Agent Part)
    (conforms : JointStepConforms record)
    (certain : ∀ a, CertainOf (record.steps a).prior goal) :
    playedAction record = goal ∧ CoherentAction coherent (playedAction record) := by
  have same : playedAction record = goal := by
    funext a
    obtain ⟨selects, played, _⟩ := conforms a
    show (record.steps a).played = goal a
    rw [played, certain_selects_goal _ goal _ (certain a) selects]
  refine ⟨same, ?_⟩
  show playedAction record ∈ coherent
  rw [same]
  exact hg

/-- Control: every agent reports certainty of the same coherent goal, yet the
parts played are not coherent. Such a record does not conform. -/
theorem incoherent_play_under_common_certainty_refused
    (coherent : Set (JointGoal Agent Part)) (goal : JointGoal Agent Part)
    (hg : goal ∈ coherent) (record : JointStepRecord Agent Part)
    (certain : ∀ a, CertainOf (record.steps a).prior goal)
    (incoherent : ¬ CoherentAction coherent (playedAction record)) :
    ¬ JointStepConforms record := fun conforms =>
  incoherent
    (conforming_common_certainty_plays_goal coherent goal hg record conforms certain).2

/-- Control: the agent observed a move that rules out a goal it believed
possible, and its belief did not change. -/
theorem unchanged_after_discriminating_move_refused
    (agent other : Agent) (prior : GoalBelief Agent Part)
    (goal : JointGoal Agent Part) (move : Part)
    (selected : JointGoal Agent Part)
    (inconsistent : goal other ≠ move) (supported : 0 < prior goal) :
    ¬ StepConforms agent
      ⟨prior, selected, selected agent, some (other, move), prior⟩ := by
  intro conforms
  have nextEq : prior goal =
      EvidenceFromTheProcess.posterior prior (moveLikelihood other) move goal :=
    congrFun conforms.2.2 goal
  have zero := watching_removes_inconsistent_goals prior other move goal inconsistent
  rw [zero] at nextEq
  linarith

/-- Control: the agent observed nothing and its belief moved. Silence is not a
move by another agent. -/
theorem belief_moved_without_observation_refused
    (agent : Agent) (prior next : GoalBelief Agent Part)
    (selected : JointGoal Agent Part) (moved : next ≠ prior) :
    ¬ StepConforms agent ⟨prior, selected, selected agent, none, next⟩ :=
  fun conforms => moved conforms.2.2

end

/-! ## Shared state: one writer per variable

The contract speaks of agents that "act on shared state". Here the shared
state is a finite set of variables, and what the agents must agree on is who
writes each one. Each agent acts on its own belief about that. -/

section SharedState

variable {Who Var : Type*} [Fintype Who] [DecidableEq Who] [Fintype Var]

/-- An ownership map names, for every shared variable, the agent that writes it. -/
abbrev Ownership (Var Who : Type*) := Var → Who

/-- The agents that write `v` when each acts on the ownership map it believes. -/
def writers (believed : Who → Ownership Var Who) (v : Var) : Finset Who :=
  Finset.univ.filter (fun a => believed a v = a)

/-- The variables agent `a` writes when it acts on the ownership map it believes. -/
def writes (believed : Who → Ownership Var Who) (a : Who) : Finset Var :=
  Finset.univ.filter (fun v => believed a v = a)

/-- Every shared variable has exactly one writer (Fritz–Liang Def. 3.6, with a
variable for the wire and an agent for the driver). -/
def OneWriter (believed : Who → Ownership Var Who) : Prop :=
  ∀ v, (writers believed v).card = 1

/-- No-conflict: agents that hold the same ownership map give every variable
exactly one writer. -/
theorem agreed_ownership_one_writer (owner : Ownership Var Who) :
    OneWriter (fun _ : Who => owner) := by
  intro v
  have single : writers (fun _ : Who => owner) v = {owner v} := by
    ext a
    simp [writers, eq_comm]
  rw [single, Finset.card_singleton]

/-- Conservation: agents that hold the same ownership map write, between them,
each variable once, so their shares add up to the whole. -/
theorem agreed_ownership_conserves (owner : Ownership Var Who) :
    ∑ a, (writes (fun _ : Who => owner) a).card = Fintype.card Var := by
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (f := owner)
    (s := Finset.univ) (t := Finset.univ) (by intro x _; simp)).symm

/-! Two controls on one shared variable and two agents. -/

/-- Each agent believes the variable is its own. -/
def bothClaim : Fin 2 → Ownership Unit (Fin 2) := fun a _ => a

/-- Each agent believes the variable is the other's. -/
def neitherClaims : Fin 2 → Ownership Unit (Fin 2) := fun a _ => 1 - a

theorem both_claim_two_writers : (writers bothClaim ()).card = 2 := by decide

theorem neither_claims_no_writer : (writers neitherClaims ()).card = 0 := by decide

/-- Control: two writers for one variable. -/
theorem both_claim_refused : ¬ OneWriter bothClaim := fun one =>
  absurd ((both_claim_two_writers).symm.trans (one ())) (by decide)

/-- Control: a variable nobody writes. -/
theorem neither_claims_refused : ¬ OneWriter neitherClaims := fun one =>
  absurd ((neither_claims_no_writer).symm.trans (one ())) (by decide)

end SharedState

end DarkTower.WarMachine.R11JointAction
