import DarkTower.WarMachine.MachineQ

/-!
# The constructed `Q(o∣π)`, exhibited on two policies

`futon2:holes/labs/wm-contract/worklist.edn` `:F1`, Lean leg, slice 1. This
module supplies a `MachineQ.QReading` and reads off the row masses the
constructor produces, so that "at least two policy rows, normalisation proven, a
policy-conditioned difference exhibited" is a checked statement rather than a
promise.

WHAT IS AND IS NOT CLAIMED. `DemoState`, `DemoAction` and `DemoPolicy` are
declared here, for this demonstration. Under the census criterion
(`futon2:holes/labs/wm-contract/FUNDAMENTALS.edn` `:what-does-not-count`) that
makes them a FIXTURE, and this module therefore inhabits nothing and closes no
fundamental. The machine's own policy carrier
(`:fundamental/machine-policy-carrier`), state space and belief reading
(`:fundamental/belief-to-state-distribution`) remain uninhabited on both sides,
and choosing them is a ruling this lane does not make. What the module shows is
that the constructor in `DarkTower.WarMachine.MachineQ` -- whose arguments are a
`GenerativeModel` and a `BeliefState` -- yields normalised, policy-separated
rows when a reading is supplied.

THE OUTCOME ALPHABET IS NOT INVENTED HERE. Its six rows are the observation
closure the mission declares: ordinary evidence plus no-result, failure,
timeout, conflicting evidence and missing evidence
(`futon2:holes/missions/M-aif-policy-conditioned-eig.md:81`). `alphabetIsClosed`
below decides that the six named rows are all of them, so there is no catch-all
absorbing a seventh outcome silently.

THE POLICY FAMILY IS A CANDIDATE, NOT A RULING. Which policy family goes first
is an open question to Joe
(`futon2:holes/labs/wm-contract/proposals/STRAWMAN-M-aif-policy-conditioned-eig.md`,
question 1); the two rows here are named after the mission's own example, "a
pattern acquisition/review action"
(`futon2:holes/missions/M-aif-policy-conditioned-eig.md:131`), and are used
because a difference needs two rows to be exhibited between, not because the
family has been chosen.

THE BELIEF READING IS DEMONSTRATION-ONLY. `demoBeliefMass` reads one declared
channel through a logistic, which is normalised for every `BeliefState` and so
discharges `QReading`'s obligation; it is not a claim about how the War
Machine's fourteen channel moments should map onto model states. That map is the
fundamental named above.
-/

namespace DarkTower.WarMachine.MachineQWitness

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineQ

/-! ## The declared carriers -/

/-- The mission's observation closure: ordinary evidence and the five typed
absences it names (`M-aif-policy-conditioned-eig.md:81`). -/
inductive EvidenceOutcome where
  | ordinary
  | noResult
  | failure
  | timeout
  | conflict
  | missing
  deriving DecidableEq, Repr

/-- The six rows, in declaration order. -/
def EvidenceOutcome.all : List EvidenceOutcome :=
  [.ordinary, .noResult, .failure, .timeout, .conflict, .missing]

/-- The alphabet is CLOSED: the six declared rows are all of them, so nothing is
absorbed by a catch-all. -/
theorem alphabetIsClosed :
    EvidenceOutcome.all.length = 6 ∧ ∀ e : EvidenceOutcome, e ∈ EvidenceOutcome.all := by
  refine ⟨rfl, ?_⟩
  intro e
  cases e <;> decide

/-- Evidence observations are the demonstration's only vertex-tagged content. -/
def DemoObs : Vertex → Type := fun _ => EvidenceOutcome

/-- One outcome of the declared alphabet, tagged at the evidence vertex. -/
def out (e : EvidenceOutcome) : Outcome DemoObs := ⟨.evidence, e⟩

/-- The declared alphabet as the list every observation row is stated over. -/
def demoAlphabet : List (Outcome DemoObs) :=
  EvidenceOutcome.all.map out

/-- Two latent states: whether the next step lands on interpretable evidence. -/
inductive DemoState where
  | informative
  | opaque
  deriving DecidableEq, Repr

/-- The finite state carrier. -/
def demoStates : List DemoState := [.informative, .opaque]

/-- The controlled step. -/
inductive DemoAction where
  | acquire
  | review
  deriving DecidableEq, Repr

/-- The two candidate policies. -/
inductive DemoPolicy where
  | acquisition
  | review
  deriving DecidableEq, Repr

/-! ## The generative model -/

/-- The observation model: an informative state mostly yields ordinary evidence,
an opaque one mostly yields no result. Both rows put strictly positive mass on
every typed absence, which is what "finite `Q(o∣π)` including no-result,
failure, timeout, conflict and missing" asks for
(`M-aif-policy-conditioned-eig.md:81`). -/
noncomputable def aRow : DemoState → EvidenceOutcome → ℝ
  | .informative, .ordinary => 1/2
  | .informative, .noResult => 1/8
  | .informative, .failure => 1/8
  | .informative, .timeout => 1/8
  | .informative, .conflict => 1/16
  | .informative, .missing => 1/16
  | .opaque, .ordinary => 1/16
  | .opaque, .noResult => 1/2
  | .opaque, .failure => 1/8
  | .opaque, .timeout => 1/8
  | .opaque, .conflict => 1/8
  | .opaque, .missing => 1/16

/-- `A : S ⇝ O`, over the declared alphabet. -/
noncomputable def demoObservation : ProbabilityKernel DemoState (Outcome DemoObs) where
  support _ := demoAlphabet
  mass s o := aRow s o.2
  nonnegative := by
    intro s o
    cases s <;> cases (o.2 : EvidenceOutcome) <;> norm_num [aRow]
  normalised := by
    intro s
    cases s <;> norm_num [demoAlphabet, EvidenceOutcome.all, out, aRow]

/-- The controlled transition: `acquire` lands informative three times in four,
`review` the other way round. Action-conditioned and state-independent, so that
the exhibited difference below can only come from the planned action. -/
noncomputable def bRow : DemoAction → DemoState → ℝ
  | .acquire, .informative => 3/4
  | .acquire, .opaque => 1/4
  | .review, .informative => 1/4
  | .review, .opaque => 3/4

/-- `B : S×U ⇝ S`. -/
noncomputable def demoTransition : TransitionKernel DemoState DemoAction where
  support _ := demoStates
  mass su s' := bRow su.2 s'
  nonnegative := by
    rintro ⟨_, u⟩ s'
    cases u <;> cases s' <;> norm_num [bRow]
  normalised := by
    rintro ⟨_, u⟩
    cases u <;> norm_num [demoStates, bRow]

/-- `E : 1 ⇝ Π`, uniform over the two candidates. -/
noncomputable def demoPolicyPrior : PolicyPriorKernel DemoPolicy where
  support _ := [.acquisition, .review]
  mass _ _ := 1/2
  nonnegative := by intros; norm_num
  normalised := by intro; norm_num

/-- The generative model the kernel is constructed from. -/
noncomputable def demoModel : GenerativeModel DemoObs DemoState DemoAction DemoPolicy where
  observation := demoObservation
  transition := demoTransition
  policyPrior := demoPolicyPrior

/-! ## The reading -/

/-- A logistic read of one declared channel. Strictly between 0 and 1 for every
belief, which is what makes the reading normalised unconditionally. -/
noncomputable def informativeWeight (b : BeliefState) : ℝ :=
  (1 + Real.exp (-(b.mean Channel.supportCoverage)))⁻¹

theorem informativeWeight_nonneg (b : BeliefState) : 0 ≤ informativeWeight b := by
  unfold informativeWeight
  positivity

theorem informativeWeight_le_one (b : BeliefState) : informativeWeight b ≤ 1 := by
  unfold informativeWeight
  rw [inv_le_one_iff₀]
  right
  have := Real.exp_pos (-(b.mean Channel.supportCoverage))
  linarith

/-- The belief reading: the demonstration's map from channel moments onto model
states. DEMONSTRATION ONLY -- see the module docstring. -/
noncomputable def demoBeliefMass (b : BeliefState) : DemoState → ℝ
  | .informative => informativeWeight b
  | .opaque => 1 - informativeWeight b

/-- The `QReading` the constructor is applied through. -/
noncomputable def demoReading : QReading demoModel where
  states := demoStates
  outcomes := demoAlphabet
  plan
    | .acquisition => .acquire
    | .review => .review
  beliefMass := demoBeliefMass
  beliefNonnegative := by
    intro b s
    cases s
    · exact informativeWeight_nonneg b
    · exact sub_nonneg.mpr (informativeWeight_le_one b)
  beliefNormalised := by
    intro b
    simp [demoStates, demoBeliefMass]
  transitionSupport := by intros; rfl
  observationSupport := by intros; rfl

/-- The constructed kernel: `Q(o∣π)` for this model, reading and belief. Nothing
below writes a row by hand. -/
noncomputable def demoQ (b : BeliefState) : PredictiveOutcomeKernel DemoPolicy DemoObs :=
  machinePredictiveOutcomeKernel demoModel demoReading b

/-! ## What the construction yields -/

/-- Every policy row of the constructed kernel is normalised. Carried by the
constructor's own proof, restated here so the demonstration asserts it. -/
theorem demoRowsNormalised (b : BeliefState) (π : DemoPolicy) :
    (((demoQ b).support π).map ((demoQ b).mass π)).sum = 1 :=
  (demoQ b).normalised π

/-- THE POLICY-CONDITIONED DIFFERENCE, at the ordinary-evidence outcome. The two
values are read off the construction, not stipulated: `acquisition` predicts
ordinary evidence at 25/64, `review` at 11/64. Independent of the belief,
because this model's transition rows do not depend on the source state -- which
is the point: the difference is attributable to the planned action alone. -/
theorem demoOrdinaryRowMasses (b : BeliefState) :
    (demoQ b).mass .acquisition (out .ordinary) = 25/64 ∧
      (demoQ b).mass .review (out .ordinary) = 11/64 := by
  constructor <;>
    · simp [demoQ, machinePredictiveOutcomeKernel, predictiveOutcomeMass, predictedStateMass,
        demoReading, demoStates, demoModel, demoObservation, demoTransition, demoBeliefMass,
        out, aRow, bRow]
      ring

/-- `Q(o∣π)` is not constant across the two policies: the mission's C6
(`M-aif-policy-conditioned-eig.md:90`) exhibited on the constructed kernel. -/
theorem demoPolicyConditionedDifference (b : BeliefState) :
    (demoQ b).mass .acquisition ≠ (demoQ b).mass .review := by
  intro h
  have hpoint := congrFun h (out .ordinary)
  obtain ⟨ha, hr⟩ := demoOrdinaryRowMasses b
  rw [ha, hr] at hpoint
  norm_num at hpoint

/-- And the difference is attributable to the planned step, by the construction's
own law. -/
theorem demoPlansDiffer (b : BeliefState) :
    demoReading.plan .acquisition ≠ demoReading.plan .review :=
  plansDifferOfRowsDiffer demoModel demoReading b .acquisition .review
    (demoPolicyConditionedDifference b)

/-! ## Negative control: the difference is not an artefact of the machinery -/

/-- The same model and belief reading, with both policies committing to the SAME
controlled step. -/
noncomputable def flatReading : QReading demoModel :=
  { demoReading with plan := fun _ => .acquire }

/-- NEGATIVE CONTROL. Under `flatReading` the two policy rows COINCIDE. So the
difference exhibited above is produced by the planned action and not by the
construction: a composition that separated policies here would be separating them
on something it has no access to. -/
theorem flatReadingRowsCoincide (b : BeliefState) :
    (machinePredictiveOutcomeKernel demoModel flatReading b).mass .acquisition
      = (machinePredictiveOutcomeKernel demoModel flatReading b).mass .review :=
  rowsEqualOfEqualPlans demoModel flatReading b .acquisition .review rfl

/-! ## What the demonstration rests on -/

/--
info: 'DarkTower.WarMachine.MachineQWitness.demoOrdinaryRowMasses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms demoOrdinaryRowMasses

/--
info: 'DarkTower.WarMachine.MachineQWitness.demoPolicyConditionedDifference' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms demoPolicyConditionedDifference

/--
info: 'DarkTower.WarMachine.MachineQWitness.alphabetIsClosed' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms alphabetIsClosed

/--
info: 'DarkTower.WarMachine.MachineQWitness.flatReadingRowsCoincide' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms flatReadingRowsCoincide

end DarkTower.WarMachine.MachineQWitness
