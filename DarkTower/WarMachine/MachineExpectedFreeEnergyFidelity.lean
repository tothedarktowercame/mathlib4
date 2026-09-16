import DarkTower.WarMachine.MachineQ

/-!
# Fidelity of the machine's expected free energy

Audit `futon2/holes/labs/wm-contract/AUDIT-lean-aif-equations-2026-09-16.md`
section A3 §5 finds `:expected-free-energy` DIVERGES because
`Holes.expectedFreeEnergy` accepts `ambiguity : PolicyIndex → ℝ` as an
arbitrary argument: a deterministic one-state model with `Q = C = δ_o` can be
scored `G = -1` by passing `ambiguity := fun _ => -1`.

`MachineQ.machineExpectedFreeEnergy` already fixes the seam: its ambiguity is
`Holes.ambiguity (machinePredictedStateKernel …) model.observation` and its
risk is taken over `machinePredictiveOutcomeKernel …`, both built from the same
model, reading and belief. This module proves that closure:

* `machineExpectedFreeEnergy_eq` -- both terms of `G` come from the one model;
* `machineAmbiguity_nonneg` -- the audit's `-1` is unreachable, because
  expected observation entropy is nonnegative for every kernel-reading;
* `fixExpectedFreeEnergy_zero` -- the audit's counterexample case compiled as a
  fixture: one state, one action, one policy, one outcome, `C = δ_o`, and the
  machine's own score is exactly `⟨0⟩`.

No existing declaration is edited; `Holes.lean` is untouched.
-/

namespace DarkTower.WarMachine.MachineExpectedFreeEnergyFidelity

open DarkTower.WarMachine.Holes DarkTower.WarMachine.MachineQ

/-! ## The two terms come from the one model -/

/-- `machineExpectedFreeEnergy` is definitionally the kernel-derived risk plus
the kernel-derived ambiguity: risk over `Q(o∣π)` and expected observation
entropy under `Q(s∣π)`, both constructed from the same `model`, `reading` and
`belief`. The supplied-ambiguity seam of `Holes.expectedFreeEnergy` is not
reachable through this definition. -/
theorem machineExpectedFreeEnergy_eq {Obs : Vertex → Type*}
    {State Action PolicyIndex : Type*}
    (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState)
    (Cdist : PreferenceDistribution Obs)
    (positivePreference : ∀ π o,
      o ∈ (machinePredictiveOutcomeKernel model reading belief).support π →
        0 < Cdist.mass () o)
    (π : PolicyIndex) :
    (machineExpectedFreeEnergy model reading belief Cdist positivePreference π).value
      = predictiveOutcomeRisk (machinePredictiveOutcomeKernel model reading belief)
          Cdist positivePreference π
        + ambiguity (machinePredictedStateKernel model reading belief)
            model.observation π :=
  rfl

/-! ## Expected observation entropy is nonnegative -/

/-- A pointwise nonnegative finite sum is nonnegative, and a pointwise
nonpositive finite sum is nonpositive. Written by induction on a pointwise
hypothesis so the list is free to vary. -/
private theorem sum_nonneg_aux {β : Type*} (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ l : List β, 0 ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => simp
  | cons a as ih =>
    simpa only [List.map_cons, List.sum_cons] using add_nonneg (hf a) ih

private theorem sum_nonpos_aux {β : Type*} (f : β → ℝ) (hf : ∀ x, f x ≤ 0) :
    ∀ l : List β, (l.map f).sum ≤ 0 := by
  intro l
  induction l with
  | nil => simp
  | cons a as ih =>
    simpa only [List.map_cons, List.sum_cons] using add_nonpos (hf a) ih

/-- A single nonnegative member of a finite list is at most the list's sum. -/
private theorem single_le_sum_aux {β : Type*} (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ (l : List β) (b : β), b ∈ l → f b ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => intro b hb; simp at hb
  | cons a as ih =>
    intro b hb
    by_cases hba : b = a
    · subst hba
      simpa only [List.map_cons, List.sum_cons] using
        le_add_of_nonneg_right (sum_nonneg_aux f hf as)
    · refine le_trans (ih b ?_) (le_add_of_nonneg_left (hf a))
      rcases List.mem_cons.mp hb with h | h
      · exact absurd h hba
      · exact h

/-- Every kernel mass is at most one: nonnegative, and bounded by its row's
normalised sum when it lies on the support, zero otherwise. -/
private theorem kernel_mass_le_one {S O : Type*} (K : ProbabilityKernel S O)
    (s : S) (o : O) : K.mass s o ≤ 1 := by
  by_cases hm : o ∈ K.support s
  · calc K.mass s o ≤ ((K.support s).map (K.mass s)).sum :=
        single_le_sum_aux (K.mass s) (fun _ => K.nonnegative _ _) (K.support s) o hm
    _ = 1 := K.normalised s
  · rw [K.mass_eq_zero_of_not_mem s o hm]; linarith

/-- Each entropy summand `p * log p` is nonpositive: `Real.mul_log_nonpos`
covers `0 ≤ p ≤ 1`, and `Real.log 0 = 0` makes the zero-mass term zero. -/
private theorem mass_log_mass_nonpos {S O : Type*} (K : ProbabilityKernel S O)
    (s : S) (o : O) : K.mass s o * Real.log (K.mass s o) ≤ 0 := by
  by_cases h0 : K.mass s o = 0
  · simp [h0]
  · exact Real.mul_log_nonpos (K.nonnegative s o) (kernel_mass_le_one K s o)

/-- One observation row's entropy is nonnegative. -/
private theorem observationEntropy_nonneg {State Observation : Type*}
    (A : observationKernel State Observation) (s : State) :
    0 ≤ observationEntropy A s := by
  have h := sum_nonpos_aux (fun o => A.mass s o * Real.log (A.mass s o))
    (mass_log_mass_nonpos A s) (A.support s)
  unfold observationEntropy
  linarith

/-- The audit's `-1` ambiguity is unreachable: the machine's ambiguity is a sum
of nonnegative predicted-state masses times nonnegative row entropies, for
every model, reading and belief. -/
theorem machineAmbiguity_nonneg {Obs : Vertex → Type*}
    {State Action PolicyIndex : Type*}
    (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState) (π : PolicyIndex) :
    0 ≤ machineAmbiguity model reading belief π := by
  unfold machineAmbiguity ambiguity
  apply List.sum_nonneg
  intro x hx
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg ((machinePredictedStateKernel model reading belief).nonnegative π s)
    (observationEntropy_nonneg model.observation s)

/-! ## The audit's counterexample, compiled

One state, one action, one policy, one outcome; deterministic observation and
transition; `C` the point mass on the outcome. These carriers are declared for
this fixture, so under the `FUNDAMENTALS.edn` criterion they inhabit nothing --
they compile the audit's specific counterexample against the machine's real
signature. The audit scored this model `-1` by supplying an arbitrary
ambiguity; the machine scores it `⟨0⟩`.
-/

/-- The fixture's one outcome value. -/
inductive FixOutcome where
  | only
  deriving DecidableEq, Repr

/-- The fixture's only vertex-tagged content. -/
def FixObs : Vertex → Type := fun _ => FixOutcome

/-- Instance search cannot see through the `FixObs` definition, so the
decidable equality on its values is provided here. -/
local instance fixObsDecEq (v : Vertex) : DecidableEq (FixObs v) :=
  inferInstanceAs (DecidableEq FixOutcome)

/-- The fixture's single outcome. -/
def fout : Outcome FixObs := ⟨.evidence, .only⟩

/-- The fixture's single state. -/
inductive FixState where
  | only
  deriving DecidableEq, Repr

/-- The fixture's single action. -/
inductive FixAction where
  | act
  deriving DecidableEq, Repr

/-- The fixture's single policy. -/
inductive FixPolicy where
  | only
  deriving DecidableEq, Repr

/-- `A : S ⇝ O`, deterministic: the only outcome gets all the mass. The two
nested decidable equalities avoid needing a `DecidableEq` instance for the
Sigma-typed outcome. -/
noncomputable def fixObservation : ProbabilityKernel FixState (Outcome FixObs) where
  support _ := [fout]
  mass := fun _ o =>
    if o.1 = Vertex.evidence then (if o.2 = FixOutcome.only then 1 else 0) else 0
  nonnegative := by
    intro s o
    rcases o with ⟨v, x⟩
    cases v <;> cases x <;> simp
  support_nodup := by intro s; simp [fout]
  mass_eq_zero_of_not_mem := by
    intro s o h
    rcases o with ⟨v, x⟩
    cases v <;> cases x <;> simp_all [fout]
  normalised := by
    intro s
    simp [fout]

/-- `B : S×U ⇝ S`, deterministic: the only next state gets all the mass. -/
noncomputable def fixTransition : TransitionKernel FixState FixAction where
  support _ := [.only]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  support_nodup := by intro su; simp
  mass_eq_zero_of_not_mem := by
    intro su o h
    cases o
    simp_all
  normalised := by intro su; simp

/-- `E : 1 ⇝ Π`, the single policy with all mass. -/
noncomputable def fixPolicyPrior : PolicyPriorKernel FixPolicy where
  support _ := [.only]
  mass := fun _ _ => 1
  nonnegative := by intros; norm_num
  support_nodup := by intro s; simp
  mass_eq_zero_of_not_mem := by
    intro s o h
    cases o
    simp_all
  normalised := by intro s; simp

/-- The one-state one-outcome generative model. -/
noncomputable def fixModel : GenerativeModel FixObs FixState FixAction FixPolicy where
  observation := fixObservation
  transition := fixTransition
  policyPrior := fixPolicyPrior

/-- `C` is the point mass on the single outcome: full mass on `fout`, zero on
every other vertex-tagged value. -/
noncomputable def fixC : PreferenceDistribution FixObs where
  support _ := [fout]
  mass := fun _ o =>
    if o.1 = Vertex.evidence then (if o.2 = FixOutcome.only then 1 else 0) else 0
  nonnegative := by
    intro s o
    rcases o with ⟨v, x⟩
    cases v <;> cases x <;> simp
  support_nodup := by intro s; simp [fout]
  mass_eq_zero_of_not_mem := by
    intro s o h
    rcases o with ⟨v, x⟩
    cases v <;> cases x <;> simp_all [fout]
  normalised := by
    intro s
    simp [fout]

/-- Any belief state; its content is irrelevant because the reading is
deterministic. -/
def fixBelief : BeliefState := ⟨fun _ => 0, fun _ => ⟨0, le_refl 0⟩⟩

/-- The reading that puts all belief mass on the single state. -/
noncomputable def fixReading : QReading fixModel where
  states := [.only]
  outcomes := [fout]
  plan := fun _ => .act
  beliefMass := fun _ _ => 1
  beliefNonnegative := by intros; norm_num
  beliefNormalised := by intro b; simp
  transitionSupport := by intros; rfl
  observationSupport := by intros; rfl

/-- `C` is strictly positive on the constructed kernel's support. -/
theorem fixPositivePreference :
    ∀ π o, o ∈ (machinePredictiveOutcomeKernel fixModel fixReading fixBelief).support π →
      0 < fixC.mass () o := by
  intros π o h
  have hof : o = fout := by
    simpa [machinePredictiveOutcomeKernel, fixReading, fout] using h
  subst o
  simp only [fixC, fout]
  norm_num

/-- THE AUDIT'S CASE, COMPILED. `Q(o∣π) = C = δ_o` deterministically, so true
risk is `log 1 = 0` and true ambiguity is `-(1 · log 1) = 0`. The machine's own
score is exactly `⟨0⟩`; an arbitrary supplied ambiguity can no longer move it. -/
theorem fixExpectedFreeEnergy_zero :
    (machineExpectedFreeEnergy fixModel fixReading fixBelief fixC fixPositivePreference
        FixPolicy.only).value = 0 := by
  have hRisk :
      predictiveOutcomeRisk (machinePredictiveOutcomeKernel fixModel fixReading fixBelief)
        fixC fixPositivePreference FixPolicy.only = 0 := by
    unfold predictiveOutcomeRisk
    simp only [machinePredictiveOutcomeKernel, predictiveOutcomeMass, predictedStateMass,
      fixReading, fixModel, fixTransition, fixObservation, fixC, fout]
    norm_num
  have hAmb :
      machineAmbiguity fixModel fixReading fixBelief FixPolicy.only = 0 := by
    unfold machineAmbiguity ambiguity observationEntropy
    simp only [machinePredictedStateKernel, predictedStateMass, fixReading, fixModel,
      fixTransition, fixObservation, fout]
    norm_num
  rw [machineExpectedFreeEnergy_eq fixModel fixReading fixBelief fixC fixPositivePreference
    FixPolicy.only, hRisk]
  show 0 + machineAmbiguity fixModel fixReading fixBelief FixPolicy.only = 0
  rw [hAmb]
  ring

/-! ## What these proofs rest on -/

-- Machine ambiguity is nonnegative for every model, reading and belief.
/-- 
info: 'DarkTower.WarMachine.MachineExpectedFreeEnergyFidelity.machineAmbiguity_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms machineAmbiguity_nonneg

-- Both G terms come from the one model.
/-- 
info: 'DarkTower.WarMachine.MachineExpectedFreeEnergyFidelity.machineExpectedFreeEnergy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms machineExpectedFreeEnergy_eq

-- The audit's counterexample scores zero through the real signature.
/-- 
info: 'DarkTower.WarMachine.MachineExpectedFreeEnergyFidelity.fixExpectedFreeEnergy_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fixExpectedFreeEnergy_zero

end DarkTower.WarMachine.MachineExpectedFreeEnergyFidelity
