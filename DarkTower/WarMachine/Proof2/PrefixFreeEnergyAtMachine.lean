import DarkTower.WarMachine.PolicyVariationalFreeEnergy
import DarkTower.WarMachine.ExactBeliefTrajectory
import DarkTower.WarMachine.Proof2.EnactmentHabit
import DarkTower.WarMachine.Proof2.AdjudicationCounts
import DarkTower.WarMachine.Proof2.TokenLikelihoodRestrict
import DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

/-!
# F over the machine's own executed prefix (W7, registry `:policy-free-energy`, R8)

## What the row says

`:policy-free-energy`: `F(π) := E_Q[ln Q − ln P(o,s|π)] ≥ −ln P(o|π)`, equality at the exact
posterior, `+∞` on a support violation; `:lean` was
`PolicyVariationalFreeEnergy.variationalFreeEnergy`, which takes the likelihood, the prior
and `q` as free arguments (`:enters-through {:o :lik :A :lik}`). SPEC-F §1 defines the
observed-prefix F: for the admitted history of ONE policy,
`Fprefix(π) = Σ_{i<n} fᵢ`, `fᵢ = variationalFreeEnergy (fun x => Aᵢ x oᵢ) (predictedState Bᵢ sPrevᵢ) qᵢ`,
an unweighted sum in nats, `n` the observed history length. `:live-status` is absent: the
live path stamps `:not-supplied` for every entry (`production-ranked`).

## The policy grain the Step carries

The step carries the CASCADE-GRAIN policy key `EnactmentHabit.PolicyKey`
(`[mission, ordered pattern ids, semilattice]`), because that is the `:policy-key` the
flight's `:increment` receipt carries and the key `policy-key-for` builds (F1c-D §1, §4;
C4). It does NOT carry `MachinePolicySet`'s policy type: that module's own header marks it
NON-CONFORMANT (flat `Candidate` actions) and forbids binding any G, EFE or selection
statement to it. The machine's posterior in W10 (`machineWeightsAtHabit`) is over the same
`PolicyKey` menu, so the prefix F and the counted habit prior are over one policy grain.

## The step

Named after F1c-D's `:step`: policy key, occurrence `[flight click]`, the observation `o`
(over the checked tokens: the model's `O`; C5's restriction is how `A` is stated on the
checked universe, `tokenA` below), `A` with its measured provenance (C2's `Supply`: only
`measured` is admitted), `B` the transition row of the policy's step, `sPrev`, and `q`. The
step's `f` is recomputed here (`stepF`), not carried.

## Admission (F1b-admit-I): the prefix ends at the first refusal

In occurrence order: `unmeasured` (A10: a zero-kernel or unsupported class is not a
measurement), `foreignPolicy`, `duplicateOccurrence`, `chainBroken`
(`sPrev_(i+1) ≠ qᵢ`), `contradiction` (`exactUpdate = none`: `P(o) = 0`), `notPosterior`
(the recorded `q` is not the exact update). A refusal ends the prefix: no later step can
chain, because its `sPrev` would be a `q` that was never admitted.

## The absences

`prefixF` is `Except`: `noAdmittedSteps` (a never-executed policy borrows no history, the
code's `:not-supplied`; not `0`), and `contradiction` (`F = ⊤`, the code's `:zero-support`,
only for a contradiction step, never a per-step absence inside a computed total).

## F into the posterior

`machineWeightsAtPrefixF` is `machineWeights` with `F π := prefixF π`, `⊤` at a
contradiction (weight `0`, W1b). A policy with no admitted history has NO `F`, and
`machineWeights`' carrier has no arm for an absent `F`; the code's fallback (omit the term
and record the law that ran, `law-receipt`) is not something that carrier expresses, so the
weights are ABSENT (`notSupplied π`) rather than computed with a stand-in `0`.
-/

set_option linter.unusedSectionVars false

namespace DarkTower.WarMachine.Proof2.PrefixFreeEnergyAtMachine

open DarkTower.WarMachine
open DarkTower.WarMachine.ExactBeliefTrajectory
open DarkTower.WarMachine.PolicyVariationalFreeEnergy
open DarkTower.WarMachine.Proof2.EnactmentHabit (PolicyKey)
open DarkTower.WarMachine.Proof2.AdjudicationCounts (Supply)
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

noncomputable section

variable {M P S O : Type*} [DecidableEq M] [DecidableEq P] [Fintype S] [DecidableEq S]

/-- One executed step of one policy, as F1c-D's `:step` carries it. -/
structure Step (M P S O : Type*) where
  policy : PolicyKey M P
  occurrence : String × String
  supply : Supply
  o : O
  A : S → O → ℝ
  B : S → S → ℝ
  sPrev : S → ℝ
  q : S → ℝ

/-- Why a step is not admitted; the prefix ends there. -/
inductive Refusal where
  | unmeasured
  | foreignPolicy
  | duplicateOccurrence
  | chainBroken
  | contradiction
  | notPosterior
  deriving DecidableEq

/-- `fᵢ`: the step's variational free energy at its own likelihood, prediction and
posterior (SPEC-F §1). -/
def stepF (s : Step M P S O) : EReal :=
  variationalFreeEnergy (fun x => s.A x s.o) (predictedState s.B s.sPrev) s.q

/-- Only a MEASURED kernel is a measurement (C2's `Supply`): `zeroKernelAssumed` records an
assumption and `unsupported` is a refusal. -/
def Step.measured (s : Step M P S O) : Bool :=
  match s.supply with
  | .measured _ _ => true
  | _ => false

open Classical in
/-- The admission check for one step against the prefix so far: the policy, the occurrences
seen, and the previous posterior. `none` is admitted. -/
def checkStep (π : PolicyKey M P) (seen : List (String × String)) (prev : Option (S → ℝ))
    (s : Step M P S O) : Option Refusal :=
  if s.measured = false then some .unmeasured
  else if s.policy ≠ π then some .foreignPolicy
  else if s.occurrence ∈ seen then some .duplicateOccurrence
  else if ∃ p, prev = some p ∧ s.sPrev ≠ p then some .chainBroken
  else
    match exactUpdate s.A s.B s.o s.sPrev with
    | none => some .contradiction
    | some q => if q = s.q then none else some .notPosterior

/-- Admit steps in order until the first refusal, carrying the occurrences seen and the last
posterior. Returns the admitted prefix and the refusal that ended it, if any. -/
def admitFrom (π : PolicyKey M P) :
    List (String × String) → Option (S → ℝ) → List (Step M P S O) →
      List (Step M P S O) × Option Refusal
  | _, _, [] => ([], none)
  | seen, prev, s :: rest =>
    match checkStep π seen prev s with
    | some r => ([], some r)
    | none =>
      let res := admitFrom π (s.occurrence :: seen) (some s.q) rest
      (s :: res.1, res.2)

/-- The admitted prefix of `steps` for policy `π`: occurrence order, unique occurrences,
one policy, chained, each step at the exact posterior; the first break ends it. -/
def admittedPrefix (π : PolicyKey M P) (steps : List (Step M P S O)) :
    List (Step M P S O) × Option Refusal :=
  admitFrom π [] none steps

/-- The unweighted sum of the steps' free energies, in nats (SPEC-F §1). -/
def sumF (l : List (Step M P S O)) : EReal := (l.map stepF).sum

/-- Why there is no prefix F. -/
inductive PrefixAbsence where
  | noAdmittedSteps
  | contradiction

/-- **F over the admitted prefix.** `noAdmittedSteps` when nothing was admitted (a
never-executed policy borrows no history: the code's `:not-supplied`, not `0`);
`contradiction` when the prefix ended at a step with `P(o) = 0` (`F = ⊤`, the code's
`:zero-support`); otherwise the sum. -/
def prefixF (π : PolicyKey M P) (steps : List (Step M P S O)) : Except PrefixAbsence EReal :=
  match admittedPrefix π steps with
  | (_, some .contradiction) => .error .contradiction
  | ([], _) => .error .noAdmittedSteps
  | (p, _) => .ok (sumF p)

/-! ## The step at the exact posterior -/

/-- **`stepF_eq_negLogEvidence`.** At the exact posterior the step's F is `−ln P(o)`
(`vfe_posterior_eq`, in the form `exactUpdate_minimises_vfe`). -/
theorem stepF_eq_negLogEvidence (s : Step M P S O)
    (hA : ∀ x, 0 ≤ s.A x s.o) (hB : ∀ a x, 0 ≤ s.B a x) (hB1 : ∀ a, ∑ x, s.B a x = 1)
    (hp : ∀ a, 0 ≤ s.sPrev a) (hp1 : ∑ a, s.sPrev a = 1)
    (hZ : 0 < observationProbability s.A s.B s.o s.sPrev)
    (hq : exactUpdate s.A s.B s.o s.sPrev = some s.q) :
    stepF s = ↑(-Real.log (observationProbability s.A s.B s.o s.sPrev)) := by
  have hd := exactUpdate_dist s.A s.B s.o s.sPrev hA hB hp hq
  exact (exactUpdate_minimises_vfe s.A s.B s.o s.sPrev hA hB hB1 hp hp1 hZ s.q hd.1 hd.2).mpr hq

/-! ## The prefix -/

/-- **`prefixF_nil`.** No steps: the absence, not `0`. -/
theorem prefixF_nil (π : PolicyKey M P) :
    prefixF π ([] : List (Step M P S O)) = .error .noAdmittedSteps := by
  simp [prefixF, admittedPrefix, admitFrom]

/-- **`prefixF_cons`.** The sum grows by exactly the step's `stepF`. -/
theorem sumF_cons (s : Step M P S O) (l : List (Step M P S O)) :
    sumF (s :: l) = stepF s + sumF l := by
  simp [sumF]

/-- On the ok arm the total is the sum over a nonempty admitted prefix that did not end in
a contradiction. -/
theorem prefixF_ok (π : PolicyKey M P) (steps : List (Step M P S O)) (f : EReal)
    (h : prefixF π steps = .ok f) :
    ∃ p, (admittedPrefix π steps).1 = p ∧ p ≠ [] ∧
      (admittedPrefix π steps).2 ≠ some .contradiction ∧ f = sumF p := by
  unfold prefixF at h
  rcases hpr : admittedPrefix π steps with ⟨p, r⟩
  rw [hpr] at h
  cases r with
  | none =>
    cases p with
    | nil => simp at h
    | cons a l => exact ⟨a :: l, by simp, by simp, by simp, (Except.ok.inj h).symm⟩
  | some r =>
    cases r <;> cases p <;> simp at h ⊢ <;> exact h.symm

/-! ## Admission -/

/-- A step that passes the check is measured, of the policy, and not a repeat. -/
theorem checkStep_none (π : PolicyKey M P) (seen : List (String × String))
    (prev : Option (S → ℝ)) (s : Step M P S O) (h : checkStep π seen prev s = none) :
    s.measured = true ∧ s.policy = π ∧ s.occurrence ∉ seen := by
  unfold checkStep at h
  by_cases h1 : s.measured = false
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : s.policy ≠ π
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : s.occurrence ∈ seen
      · rw [if_pos h3] at h; cases h
      · exact ⟨by simpa using h1, not_not.mp h2, h3⟩

/-- **`foreignStepIsNeverAdmitted`.** Every admitted step is of the policy asked about. -/
theorem admitFrom_policy (π : PolicyKey M P) :
    ∀ (steps : List (Step M P S O)) (seen : List (String × String)) (prev : Option (S → ℝ)),
      ∀ s ∈ (admitFrom π seen prev steps).1, s.policy = π
  | [], seen, prev, s, hs => by simp [admitFrom] at hs
  | t :: rest, seen, prev, s, hs => by
    unfold admitFrom at hs
    cases hc : checkStep π seen prev t with
    | some r => simp [hc] at hs
    | none =>
      simp only [hc] at hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact (checkStep_none π seen prev _ hc).2.1
      · exact admitFrom_policy π rest _ _ s hs'

theorem foreignStepIsNeverAdmitted (π : PolicyKey M P) (steps : List (Step M P S O))
    (s : Step M P S O) (hs : s ∈ (admittedPrefix π steps).1) : s.policy = π :=
  admitFrom_policy π steps [] none s hs

/-- **An unmeasured step is never admitted**: only a measured kernel enters F. -/
theorem admitFrom_measured (π : PolicyKey M P) :
    ∀ (steps : List (Step M P S O)) (seen : List (String × String)) (prev : Option (S → ℝ)),
      ∀ s ∈ (admitFrom π seen prev steps).1, s.measured = true
  | [], seen, prev, s, hs => by simp [admitFrom] at hs
  | t :: rest, seen, prev, s, hs => by
    unfold admitFrom at hs
    cases hc : checkStep π seen prev t with
    | some r => simp [hc] at hs
    | none =>
      simp only [hc] at hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact (checkStep_none π seen prev _ hc).1
      · exact admitFrom_measured π rest _ _ s hs'

/-- Occurrences in the admitted prefix are unique, and none was already seen. -/
theorem admitFrom_nodup (π : PolicyKey M P) :
    ∀ (steps : List (Step M P S O)) (seen : List (String × String)) (prev : Option (S → ℝ)),
      ((admitFrom π seen prev steps).1.map Step.occurrence).Nodup ∧
      ∀ s ∈ (admitFrom π seen prev steps).1, s.occurrence ∉ seen
  | [], seen, prev => by simp [admitFrom]
  | t :: rest, seen, prev => by
    unfold admitFrom
    cases hc : checkStep π seen prev t with
    | some r => simp
    | none =>
      obtain ⟨ih1, ih2⟩ := admitFrom_nodup π rest (t.occurrence :: seen) (some t.q)
      have ht := (checkStep_none π seen prev t hc).2.2
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, ih1⟩
        intro hmem
        obtain ⟨s', hs', heq⟩ := List.mem_map.mp hmem
        exact ih2 s' hs' (by simp [heq])
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs'
        · exact ht
        · intro hin
          exact ih2 s hs' (List.mem_cons_of_mem _ hin)

theorem admittedPrefix_nodup (π : PolicyKey M P) (steps : List (Step M P S O)) :
    ((admittedPrefix π steps).1.map Step.occurrence).Nodup :=
  (admitFrom_nodup π steps [] none).1

/-- **`brokenChainStopsThePrefix`.** A step that passes every check but whose `sPrev` is not
the previous step's `q` ends the prefix there: the prefix is the first step alone. -/
theorem brokenChainStopsThePrefix (π : PolicyKey M P) (s₁ s₂ : Step M P S O)
    (rest : List (Step M P S O))
    (h₁ : checkStep π [] none s₁ = none)
    (hm : s₂.measured = true) (hp : s₂.policy = π) (hd : s₂.occurrence ≠ s₁.occurrence)
    (hbreak : s₂.sPrev ≠ s₁.q) :
    admittedPrefix π (s₁ :: s₂ :: rest) = ([s₁], some .chainBroken) := by
  have h₂ : checkStep π [s₁.occurrence] (some s₁.q) s₂ = some .chainBroken := by
    unfold checkStep
    rw [if_neg (by simpa using hm), if_neg (by simpa using hp),
      if_neg (by simpa using hd), if_pos ⟨s₁.q, rfl, hbreak⟩]
  simp [admittedPrefix, admitFrom, h₁, h₂]

/-- **The two-step total is the sum, and is not its last summand** — the SPEC-F bad case
"a two-step total equated to its last summand". If the first step's `F` is nonzero and the
second's is finite, the total differs from the second. -/
theorem two_step_total_ne_last (s₁ s₂ : Step M P S O) (hb : stepF s₂ ≠ ⊤) (hb' : stepF s₂ ≠ ⊥)
    (ha : stepF s₁ ≠ 0) (ha' : stepF s₁ ≠ ⊤) (ha'' : stepF s₁ ≠ ⊥) :
    sumF [s₁, s₂] = stepF s₁ + stepF s₂ ∧ sumF [s₁, s₂] ≠ stepF s₂ := by
  refine ⟨by simp [sumF], ?_⟩
  intro h
  simp only [sumF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  lift stepF s₁ to ℝ using ⟨ha', ha''⟩ with a
  lift stepF s₂ to ℝ using ⟨hb, hb'⟩ with b
  have : a = 0 := by
    have h' : (↑(a + b) : EReal) = ↑b := by rw [EReal.coe_add]; exact h
    have := EReal.coe_injective h'
    linarith
  exact ha (by rw [this]; rfl)

/-- **The admitted two-step prefix sums its two steps.** -/
theorem prefixF_two (π : PolicyKey M P) (s₁ s₂ : Step M P S O)
    (h₁ : checkStep π [] none s₁ = none)
    (h₂ : checkStep π [s₁.occurrence] (some s₁.q) s₂ = none) :
    prefixF π [s₁, s₂] = .ok (stepF s₁ + stepF s₂) := by
  simp [prefixF, admittedPrefix, admitFrom, h₁, h₂, sumF]

/-! ## Tokens: the kernel as C5 states it -/

section Tokens

open DarkTower.WarMachine.TokenObservation in
open DarkTower.WarMachine.Proof2.TokenLikelihoodRestrict in
/-- The measured token kernel on the checked universe `C` (C5's `restrictedLikelihood`),
as a step's `A`. A step over token states uses this as its `A`; whether the kernel is a
measurement is the step's `supply`, not this definition. -/
def tokenA {V : Type*} [Fintype V] [DecidableEq V] (r : AdjudicationRates V) (C : Finset V) :
    Finset V → Finset V → ℝ :=
  fun s o => restrictedLikelihood r s C o

end Tokens

/-! ## F into the posterior -/

section FPosterior

open Classical

/-- Why there are no posterior weights at the prefix F. -/
inductive PrefixWeightsAbsence (M P : Type*) where
  | notSupplied (π : PolicyKey M P)

/-- **The machine's posterior weights with `F` the observed-prefix free energy.**
`machineWeights` (W1/W1b) with `F π := prefixF π (steps π)`, `⊤` at a contradiction (weight
`0`). A policy on the menu with NO admitted history has no `F` and the weights are absent,
naming it: no `0` is stood in. -/
def machineWeightsAtPrefixF (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) : Except (PrefixWeightsAbsence M P) (List ℝ) :=
  match policies.find? (fun π => decide (prefixF π (steps π) = .error .noAdmittedSteps)) with
  | some π => .error (.notSupplied π)
  | none =>
    .ok (machineWeights habit grade
      (fun π => match prefixF π (steps π) with | .ok f => f | .error _ => ⊤) tau policies)

/-- **The composition.** On the ok arm every menu policy has an admitted history or a
contradiction, and the weights are `machineWeights` at that `F`. -/
theorem machineWeightsAtPrefixF_eq (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) (ws : List ℝ)
    (h : machineWeightsAtPrefixF habit grade steps tau policies = .ok ws) :
    (∀ π ∈ policies, prefixF π (steps π) ≠ .error .noAdmittedSteps) ∧
    ws = machineWeights habit grade
      (fun π => match prefixF π (steps π) with | .ok f => f | .error _ => ⊤) tau policies := by
  unfold machineWeightsAtPrefixF at h
  cases hf : policies.find? (fun π => decide (prefixF π (steps π) = .error .noAdmittedSteps)) with
  | some π => rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    refine ⟨fun π hπ hπ' => ?_, (Except.ok.inj h).symm⟩
    have := List.find?_eq_none.mp hf π hπ
    simp [hπ'] at this

/-- **A policy with no admitted history makes the weights absent**, naming a policy: reachable,
and no `F = 0` is stood in. -/
theorem notSuppliedIsAbsence (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) (π : PolicyKey M P) (hπ : π ∈ policies)
    (hn : prefixF π (steps π) = .error .noAdmittedSteps) :
    ∃ π', machineWeightsAtPrefixF habit grade steps tau policies = .error (.notSupplied π') := by
  unfold machineWeightsAtPrefixF
  cases hf : policies.find? (fun π => decide (prefixF π (steps π) = .error .noAdmittedSteps)) with
  | some π' => exact ⟨π', rfl⟩
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf π hπ
    simp [hn] at this

/-- **A policy whose prefix ended in a contradiction has weight zero.** `F = ⊤`, so W1b's
`infiniteFHasZeroWeight` applies: the code's `:zero-support`. -/
theorem contradictionHasZeroWeight (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) (ws : List ℝ)
    (h : machineWeightsAtPrefixF habit grade steps tau policies = .ok ws) :
    ∀ p ∈ policies.zip ws, prefixF p.1 (steps p.1) = .error .contradiction → p.2 = 0 := by
  obtain ⟨_, rfl⟩ := machineWeightsAtPrefixF_eq habit grade steps tau policies ws h
  intro p hp hc
  refine infiniteFHasZeroWeight habit grade _ tau policies p hp ?_
  intro hfin
  simp [FiniteF, hc] at hfin

end FPosterior

end

#print axioms Step
#print axioms stepF
#print axioms checkStep
#print axioms admitFrom
#print axioms admittedPrefix
#print axioms prefixF
#print axioms stepF_eq_negLogEvidence
#print axioms prefixF_nil
#print axioms sumF_cons
#print axioms prefixF_ok
#print axioms checkStep_none
#print axioms foreignStepIsNeverAdmitted
#print axioms admitFrom_measured
#print axioms admittedPrefix_nodup
#print axioms brokenChainStopsThePrefix
#print axioms two_step_total_ne_last
#print axioms prefixF_two
#print axioms tokenA
#print axioms machineWeightsAtPrefixF
#print axioms machineWeightsAtPrefixF_eq
#print axioms notSuppliedIsAbsence
#print axioms contradictionHasZeroWeight

end DarkTower.WarMachine.Proof2.PrefixFreeEnergyAtMachine
