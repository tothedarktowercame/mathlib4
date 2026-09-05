import DarkTower.WarMachine.Holes

/-!
# The machine's predictive outcome kernel, constructed

`futon2:holes/labs/wm-contract/worklist.edn` `:F1`, Lean leg, slice 1. The
object is the one the interface audit keeps finding absent
(`futon2:holes/labs/wm-contract/Q-interface-completeness.edn`, finding
`:lean/Q-machine-construction`): a declaration that COMPOSES the generative
model's transition and observation kernels over a policy and a belief to
produce `Q(o∣π)`, rather than accepting one as a bound parameter.

WHAT WAS MISSING, in the audit's own words: "No declaration composes transition
with observation over a policy to produce a kernel", and the reason it could not
be written was that "THE TYPES DO NOT MEET" -- `GenerativeModel` is indexed by
an abstract `State` (`Holes.lean:6787-6790`) while `BeliefState` is fourteen
channel-indexed moment pairs (`Holes.lean:6806-6808`), and no declaration maps
one to the other.

WHAT THIS MODULE DOES. It names the join as a declared seam (`QReading`) and
composes through it. A `QReading` carries the finite carriers the composition
sums over -- the state list, the outcome alphabet, the policy's controlled step
`plan` -- together with the belief reading `beliefMass : BeliefState → State →
ℝ` and its normalisation obligation. Given a model, a reading and a belief,
`machinePredictiveOutcomeKernel` returns a `PredictiveOutcomeKernel` whose every
row is proved normalised, and `machinePredictedStateKernel` returns the `Q(s∣π)`
that `Holes.ambiguity` has always asked for and never been given.

WHAT THIS MODULE DOES NOT DO. It does not choose the machine's belief reading,
its state space, its outcome alphabet or its policy family. Those are four
separate uninhabited fundamentals
(`futon2:holes/labs/wm-contract/FUNDAMENTALS.edn`
`:fundamental/belief-to-state-distribution`,
`:fundamental/controlled-transition-kernel`,
`:fundamental/machine-policy-carrier`,
`:fundamental/machine-preference-distribution`), and choosing any of them is a
modelling ruling that is Joe's, not this module's. A `QReading` field is
therefore an OBLIGATION MADE VISIBLE, not a gap papered over: the composition
cannot be applied without exhibiting one, and what a caller had to supply is
readable from the call.

The exhibited two-policy instance and its policy-conditioned difference are in
`DarkTower.WarMachine.MachineQWitness`, which supplies a demonstration reading.
Its carriers are declared for the demonstration, so under the
`FUNDAMENTALS.edn` criterion it is a fixture and does not inhabit anything; the
inhabitant claimed here is the constructor below, whose arguments are a
`GenerativeModel` and a `BeliefState`.
-/

namespace DarkTower.WarMachine.MachineQ

open DarkTower.WarMachine.Holes

/-- Swapping the order of a doubly indexed finite sum. Written out because the
composition below sums over states inside outcomes and needs the other
association to reach each kernel's own normalisation. -/
private theorem sum_swap {α β : Type*} (xs : List α) (ys : List β) (f : α → β → ℝ) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum
      = (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih, List.sum_map_add]

variable {Obs : Vertex → Type*} {State Action PolicyIndex : Type*}

/-- THE DECLARED SEAM. What a caller must exhibit before the model's kernels can
be run on the machine's belief over a policy.

Each field is one of the things the audit records as absent, stated as an
obligation rather than assumed:

* `states` / `outcomes` -- the finite carriers the composition sums over. The
  support hypotheses say the model's rows are all stated over these same two
  lists, which is what makes a row sum meaningful: `ProbabilityKernel` fixes no
  mass off its own support, so summing an observation row over any list other
  than its declared support would be summing an unconstrained quantity.
* `plan` -- the controlled step the policy commits to. `Holes.TransitionKernel`
  is conditioned on an `Action` and `Q(o∣π)` on a `PolicyIndex`; `plan` is the
  projection between them, and `rowsEqualOfEqualPlans` below states exactly how
  much of the policy this construction can see.
* `beliefMass` -- the belief reading. This is the join the audit calls missing:
  a map from the fourteen channel moments into a distribution over the model's
  states. -/
structure QReading (model : GenerativeModel Obs State Action PolicyIndex) where
  /-- The finite state carrier every row is summed over. -/
  states : List State
  /-- The declared finite outcome alphabet. -/
  outcomes : List (Outcome Obs)
  /-- The controlled step the policy commits to. -/
  plan : PolicyIndex → Action
  /-- The belief reading: channel moments to a mass on each model state. -/
  beliefMass : BeliefState → State → ℝ
  /-- The reading is a mass function. -/
  beliefNonnegative : ∀ b s, 0 ≤ beliefMass b s
  /-- The reading is normalised, for every belief -- not merely for the one a
  caller happens to hold. -/
  beliefNormalised : ∀ b, (states.map (beliefMass b)).sum = 1
  /-- Every transition row is stated over the declared state carrier. -/
  transitionSupport : ∀ s u, model.transition.support (s, u) = states
  /-- Every observation row is stated over the declared alphabet. -/
  observationSupport : ∀ s, model.observation.support s = outcomes

/-! ## Q(s∣π): the policy-conditioned predicted state -/

/-- The mass the belief, pushed one controlled step through the transition
kernel under `π`'s planned action, puts on `s'`. -/
def predictedStateMass (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) (π : PolicyIndex) (s' : State) : ℝ :=
  (reading.states.map fun s =>
      reading.beliefMass belief s * model.transition.mass (s, reading.plan π) s').sum

theorem predictedStateMass_nonneg (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) (π : PolicyIndex) (s' : State) :
    0 ≤ predictedStateMass model reading belief π s' := by
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨s, _, rfl⟩ := hx
  exact mul_nonneg (reading.beliefNonnegative belief s)
    (model.transition.nonnegative _ _)

theorem predictedStateMass_sum (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) (π : PolicyIndex) :
    (reading.states.map (predictedStateMass model reading belief π)).sum = 1 := by
  have hT : ∀ s : State,
      (reading.states.map (model.transition.mass (s, reading.plan π))).sum = 1 := by
    intro s
    rw [← reading.transitionSupport s (reading.plan π)]
    exact model.transition.normalised (s, reading.plan π)
  unfold predictedStateMass
  rw [sum_swap reading.states reading.states
      (fun s' s => reading.beliefMass belief s * model.transition.mass (s, reading.plan π) s')]
  simp only [List.sum_map_mul_left, hT, mul_one]
  exact reading.beliefNormalised belief

/-- CONSTRUCTED: `Q(s∣π)`, the policy-conditioned predicted state distribution.
This is the argument `Holes.ambiguity` (`Holes.lean:6880-6885`) takes and that
no declaration previously produced. -/
noncomputable def machinePredictedStateKernel
    (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) :
    ProbabilityKernel PolicyIndex State where
  support _ := reading.states
  mass := predictedStateMass model reading belief
  nonnegative := predictedStateMass_nonneg model reading belief
  normalised := predictedStateMass_sum model reading belief

/-! ## Q(o∣π): the predictive outcome kernel -/

/-- The mass `π` predicts on outcome `o`: the predicted state distribution
against the observation kernel's rows. -/
def predictiveOutcomeMass (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) (π : PolicyIndex)
    (o : Outcome Obs) : ℝ :=
  (reading.states.map fun s' =>
      predictedStateMass model reading belief π s' * model.observation.mass s' o).sum

theorem predictiveOutcomeMass_nonneg (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) (π : PolicyIndex) (o : Outcome Obs) :
    0 ≤ predictiveOutcomeMass model reading belief π o := by
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨s', _, rfl⟩ := hx
  exact mul_nonneg (predictedStateMass_nonneg model reading belief π s')
    (model.observation.nonnegative _ _)

theorem predictiveOutcomeMass_sum (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) (π : PolicyIndex) :
    (reading.outcomes.map (predictiveOutcomeMass model reading belief π)).sum = 1 := by
  have hA : ∀ s' : State,
      (reading.outcomes.map (model.observation.mass s')).sum = 1 := by
    intro s'
    rw [← reading.observationSupport s']
    exact model.observation.normalised s'
  unfold predictiveOutcomeMass
  rw [sum_swap reading.outcomes reading.states
      (fun o s' => predictedStateMass model reading belief π s' * model.observation.mass s' o)]
  simp only [List.sum_map_mul_left, hA, mul_one]
  exact predictedStateMass_sum model reading belief π

/-- CONSTRUCTED: `Q(o∣π)`. The declaration whose absence
`Q-interface-completeness.edn` records as `:lean/Q-machine-construction`
`:status :missing`: its arguments are a `GenerativeModel` and a `BeliefState`,
its result is a `PredictiveOutcomeKernel`, and every row is normalised by proof
rather than by construction of a point mass. -/
noncomputable def machinePredictiveOutcomeKernel
    (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) :
    PredictiveOutcomeKernel PolicyIndex Obs where
  support _ := reading.outcomes
  mass := predictiveOutcomeMass model reading belief
  nonnegative := predictiveOutcomeMass_nonneg model reading belief
  normalised := predictiveOutcomeMass_sum model reading belief

/-! ## How much of the policy the construction sees -/

/-- THE LAW OF THIS CONSTRUCTION. `π` reaches `Q(o∣π)` through `plan π` and
nowhere else: two policies that commit to the same controlled step have the same
predicted-outcome row.

This is the falsifiable content of "policy-conditioned" here. It says what a
policy-conditioned difference must come FROM, and it refuses the failure mode
the mission names -- an EIG "whose observation distribution is constant,
fabricated, or copied from the observation that actually occurred"
(`futon2:holes/missions/M-aif-policy-conditioned-eig.md:74`): a kernel that
varied between policies with identical planned steps would not be this
composition, and one that varied not at all is caught by the exhibited
difference in `MachineQWitness`. -/
theorem rowsEqualOfEqualPlans (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) (π ρ : PolicyIndex)
    (h : reading.plan π = reading.plan ρ) :
    (machinePredictiveOutcomeKernel model reading belief).mass π
      = (machinePredictiveOutcomeKernel model reading belief).mass ρ := by
  funext o
  simp only [machinePredictiveOutcomeKernel, predictiveOutcomeMass, predictedStateMass, h]

/-- Contrapositive, stated because it is the direction a reader of a measured
difference needs: two policy rows that differ have different planned steps, so
an exhibited difference is evidence about the plan and not about the belief. -/
theorem plansDifferOfRowsDiffer (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) (π ρ : PolicyIndex)
    (h : (machinePredictiveOutcomeKernel model reading belief).mass π
          ≠ (machinePredictiveOutcomeKernel model reading belief).mass ρ) :
    reading.plan π ≠ reading.plan ρ :=
  fun hplan => h (rowsEqualOfEqualPlans model reading belief π ρ hplan)

/-! ## The joins the constructed kernel opens

`Holes.ambiguity` and `Holes.expectedFreeEnergy` have always taken their inputs
as bound parameters. With `Q(s∣π)` and `Q(o∣π)` constructed, both can be
evaluated for a machine that exhibits a `QReading`. The preference distribution
`C` remains an argument, because it is a separate uninhabited fundamental
(`FUNDAMENTALS.edn` `:fundamental/machine-preference-distribution`) and
choosing it is a ruling, not a composition. -/

/-- Expected observation entropy under the constructed `Q(s∣π)`. -/
noncomputable def machineAmbiguity (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) (π : PolicyIndex) : ℝ :=
  ambiguity (machinePredictedStateKernel model reading belief) model.observation π

/-- `G(π)` in the risk-plus-ambiguity decomposition, with both terms derived from
the model rather than supplied. The positivity hypothesis on `C` is `Holes`'
own, unchanged. -/
noncomputable def machineExpectedFreeEnergy
    (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState)
    (Cdist : PreferenceDistribution Obs)
    (positivePreference : ∀ π o,
      o ∈ (machinePredictiveOutcomeKernel model reading belief).support π →
        0 < Cdist.mass () o) :
    PolicyIndex → ExpectedFreeEnergyValue :=
  expectedFreeEnergy (machinePredictiveOutcomeKernel model reading belief) Cdist
    positivePreference (machineAmbiguity model reading belief)

/-! ## What the construction rests on

`#print axioms`, checked at build time rather than reported once. A `sorry`
introduced into this module or into anything it uses would add `sorryAx` here and
break the build, which is the difference between a kernel that is CONSTRUCTED
and one that is asserted. -/

/--
info: 'DarkTower.WarMachine.MachineQ.machinePredictedStateKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms machinePredictedStateKernel

/--
info: 'DarkTower.WarMachine.MachineQ.machinePredictiveOutcomeKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms machinePredictiveOutcomeKernel

/--
info: 'DarkTower.WarMachine.MachineQ.rowsEqualOfEqualPlans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rowsEqualOfEqualPlans

/--
info: 'DarkTower.WarMachine.MachineQ.machineExpectedFreeEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms machineExpectedFreeEnergy

end DarkTower.WarMachine.MachineQ
