import DarkTower.WarMachine.Proof2.RolloutAtMachine
import DarkTower.WarMachine.Proof2.PrefixFreeEnergyPosterior

/-!
# The closed loop over observation epochs

Friston 2017 says that hidden-state beliefs are updated after each observation
(`refs/friston2017.txt:714-726`), that the agent keeps a separate past-and-future
state record for every allowable policy (`refs/friston2017.txt:358-372`), and that
after policy free energies are evaluated the subsequent hidden state is predicted,
an action is selected, a new observation is generated, and the cycle begins again
(`refs/friston2017.txt:917-921`). Its per-policy free energy is a sum over epochs,
using each policy's transition and the shared observation
(`refs/friston2017.txt:1598-1607`).

This module models one pass as select, act, observe, update, and records the shared
observation as evidence under every menu policy. The following are explicit model
arguments, not inferred here: `plan`, mapping a policy and epoch to its action;
`key`, mapping the action-selection `PolicyIndex` grain to the cascade `PolicyKey`
grain; occurrence identifiers; and measured supply. Each policy's own state record
`Q(s_τ | π)` is carried in `LoopState.policyBelief`, starting at `q₀` and advanced by
`nextPolicyBelief` (claude-7's review change: the first version took it as an external
argument for every epoch, so the loop did not itself chain it). The main belief is the update
at the selected action. Relating it to a Bayesian model average of the per-policy
beliefs (the source's statement at `refs/friston2017.txt:917-918`) requires weights
and an equality hypothesis; it does not follow from the components alone.

`PrefixFreeEnergyAtMachine.Step.q` is required although admission never reads it on
a contradiction; `encode_q_irrelevant` certifies the bridge; a revision of W7
should make the posterior absent on contradiction.

`loop 1` is one select-act-observe-update epoch. Thus a click with one epoch is
this case, while a click with several epochs is `loop n`; this module does not
choose between them. Action selection remains `machineAction`, the existing
maximiser. Sampling from the posterior is a separate pending change.
-/

namespace DarkTower.WarMachine.Proof2.ClosedLoopAtMachine

open DarkTower.WarMachine
open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.ExactBeliefTrajectory
open DarkTower.WarMachine.Proof2.CascadePolicySet (PolicyKey)
open DarkTower.WarMachine.Proof2.AdjudicationCounts (Supply)
open DarkTower.WarMachine.Proof2.ObservationAtMachine
open DarkTower.WarMachine.Proof2.BeliefStepAtMachine
open DarkTower.WarMachine.Proof2.BeliefAtMachine
open DarkTower.WarMachine.Proof2.RolloutAtMachine
open DarkTower.WarMachine.Proof2.PrefixFreeEnergyAtMachine
open DarkTower.WarMachine.Proof2.PrefixFreeEnergyPosterior

noncomputable section

variable {M P S O U PolicyIndex : Type*}
  [DecidableEq M] [DecidableEq P] [Fintype S] [DecidableEq S]
  [Fintype O] [DecidableEq O]

/-- Policy inputs at epoch `t`, with the action head fixed to `plan π t`. -/
def plannedInputs (base : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (plan : PolicyIndex → ℕ → U) (t : ℕ) (μ : S → ℝ) : PolicyInputs PolicyIndex U :=
  { base t μ with head := fun π => plan π t }

/-- Evidence supplied by one epoch for one policy. A contradiction has no posterior. -/
inductive PolicyEpoch (M P S O : Type*) [Fintype S] [DecidableEq S] where
  | admitted (s : Step M P S O)
  | contradicted (policy : PolicyKey M P) (occurrence : String × String)
      (supply : Supply) (o : O) (A : S → O → ℝ) (B : S → S → ℝ)
      (sPrev : S → ℝ) (refuted : exactUpdate A B o sPrev = none)

/-- Encode epoch evidence for W7. The last argument is read only on the admitted arm. -/
def encode : PolicyEpoch M P S O → (S → ℝ) → Step M P S O
  | .admitted s, _ => s
  | .contradicted policy occurrence supply o A B sPrev _, q =>
      { policy, occurrence, supply, o, A, B, sPrev, q }

/-- On a contradiction, W7 admission and prefix F cannot observe the encoded `q`. -/
theorem encode_q_irrelevant
    (e : PolicyEpoch M P S O)
    (he : ∃ policy occurrence supply o A B sPrev h,
      e = .contradicted policy occurrence supply o A B sPrev h)
    (π : PolicyKey M P) (seen : List (String × String))
    (prev : Option (S → ℝ)) (pre : List (Step M P S O)) (q₁ q₂ : S → ℝ) :
    checkStep π seen prev (encode e q₁) = checkStep π seen prev (encode e q₂) ∧
    admitFrom π seen prev (pre ++ [encode e q₁]) =
      admitFrom π seen prev (pre ++ [encode e q₂]) ∧
    prefixF π (pre ++ [encode e q₁]) = prefixF π (pre ++ [encode e q₂]) := by
  obtain ⟨policy, occurrence, supply, o, A, B, sPrev, h, rfl⟩ := he
  have hc : ∀ seen prev q₁ q₂,
      checkStep π seen prev
        (encode (.contradicted policy occurrence supply o A B sPrev h) q₁) =
      checkStep π seen prev
        (encode (.contradicted policy occurrence supply o A B sPrev h) q₂) := by
    intro seen prev q₁ q₂
    change checkStep π seen prev
        { policy := policy, occurrence := occurrence, supply := supply, o := o,
          A := A, B := B, sPrev := sPrev, q := q₁ } =
      checkStep π seen prev
        { policy := policy, occurrence := occurrence, supply := supply, o := o,
          A := A, B := B, sPrev := sPrev, q := q₂ }
    cases supply <;> simp [checkStep, Step.measured, h]
  have hn : ∀ seen prev q,
      checkStep π seen prev
        (encode (.contradicted policy occurrence supply o A B sPrev h) q) ≠ none := by
    intro seen prev q
    change checkStep π seen prev
        { policy := policy, occurrence := occurrence, supply := supply, o := o,
          A := A, B := B, sPrev := sPrev, q := q } ≠ none
    cases supply <;> simp [checkStep, Step.measured, h]
    by_cases hp : policy = π
    · by_cases ho : occurrence ∈ seen
      · simp [hp, ho]
      · by_cases hb : ∃ p, prev = some p ∧ sPrev ≠ p <;> simp [hp, ho, hb]
    · simp [hp]
  have hadmit : ∀ seen prev,
      admitFrom π seen prev
          (pre ++ [encode (.contradicted policy occurrence supply o A B sPrev h) q₁]) =
        admitFrom π seen prev
          (pre ++ [encode (.contradicted policy occurrence supply o A B sPrev h) q₂]) := by
    induction pre with
    | nil =>
      intro seen prev
      simp only [List.nil_append, admitFrom]
      rw [hc seen prev q₁ q₂]
      cases hx : checkStep π seen prev
          (encode (.contradicted policy occurrence supply o A B sPrev h) q₂) with
      | none => exact absurd hx (hn seen prev q₂)
      | some r => rfl
    | cons s rest ih =>
      intro seen prev
      simp only [List.cons_append, admitFrom]
      split
      · rfl
      · rw [ih]
  refine ⟨hc seen prev q₁ q₂, hadmit seen prev, ?_⟩
  unfold prefixF admittedPrefix
  rw [hadmit [] none]

/-- The call-site encoding used for W7 histories. On contradiction it chooses
`sPrev`; `encode_q_irrelevant` proves that admission and F do not observe it. -/
def encodedEvidence : PolicyEpoch M P S O → Step M P S O
  | e@(.admitted s) => encode e s.sPrev
  | e@(.contradicted _ _ _ _ _ _ sPrev _) => encode e sPrev

/-- If W7 admits the preceding records and classifies the appended encoded record
as their terminal contradiction, its prefix F is the existing typed contradiction. -/
theorem contradicted_record_gives_prefix_contradiction
    (π : PolicyKey M P) (pre : List (Step M P S O)) (e : PolicyEpoch M P S O)
    (q : S → ℝ)
    (h : admittedPrefix π (pre ++ [encode e q]) = (pre, some .contradiction)) :
    prefixF π (pre ++ [encode e q]) = .error .contradiction := by
  simp [prefixF, h]

/-- Build the evidence for policy `π` from its own transition and the shared observation. -/
def policyEpoch (FM : ForwardModel S O U) (key : PolicyIndex → PolicyKey M P)
    (plan : PolicyIndex → ℕ → U) (occurrence : ℕ → String × String)
    (supply : PolicyIndex → ℕ → Supply) (obs : O) (t : ℕ)
    (π : PolicyIndex) (prior : S → ℝ) : PolicyEpoch M P S O :=
  match h : exactUpdate FM.A (FM.B (plan π t)) obs prior with
  | some q => .admitted
      { policy := key π, occurrence := occurrence t, supply := supply π t,
        o := obs, A := FM.A, B := FM.B (plan π t), sPrev := prior, q := q }
  | none => .contradicted (key π) (occurrence t) (supply π t) obs FM.A
      (FM.B (plan π t)) prior h

/-- The result of one successful main-belief epoch. -/
structure EpochResult (M P S O U PolicyIndex : Type*) [Fintype S] [DecidableEq S] where
  belief : S → ℝ
  action : U
  evidence : PolicyIndex → PolicyEpoch M P S O

/-- One select-act-observe-update epoch, plus the shared observation evaluated under
each policy's own transition. -/
def epoch [LinearOrder U] (FM : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (key : PolicyIndex → PolicyKey M P)
    (plan : PolicyIndex → ℕ → U) (occurrence : ℕ → String × String)
    (supply : PolicyIndex → ℕ → Supply)
    (t : ℕ) (μ : S → ℝ) (pb : PolicyIndex → S → ℝ) :
    Except (StepAbsence PolicyIndex) (EpochResult M P S O U PolicyIndex) :=
  match machineObservationLaw FM (plannedInputs inputsAt plan t μ) (world t) with
  | .error a => .error (.noAction a)
  | .ok (u, law) =>
    if law (obs (t + 1)) = 0 then .error .processImpossible
    else match exactUpdate FM.A (FM.B u) (obs (t + 1)) μ with
      | none => .error .updateRefused
      | some μ' => .ok {
          belief := μ', action := u,
          evidence := fun π => policyEpoch FM key plan occurrence supply (obs (t + 1)) t π
            (pb π) }

/-- Each policy's belief after an epoch: the posterior of its admitted record. A
contradicted policy keeps its prior. Its prefix has already ended at that record
(`admitFrom` stops at the first refusal), so no later record of that policy is
admitted, and the value is never read by `prefixF`. -/
def nextPolicyBelief (e : PolicyIndex → PolicyEpoch M P S O) : PolicyIndex → S → ℝ :=
  fun π => match e π with
    | .admitted s => s.q
    | .contradicted _ _ _ _ _ _ sPrev _ => sPrev

/-- The record for `π` at an epoch starts from the belief the loop carried for `π`. -/
theorem policyEpoch_sPrev (FM : ForwardModel S O U) (key : PolicyIndex → PolicyKey M P)
    (plan : PolicyIndex → ℕ → U) (occurrence : ℕ → String × String)
    (supply : PolicyIndex → ℕ → Supply) (o : O) (t : ℕ) (π : PolicyIndex) (prior : S → ℝ) :
    (encodedEvidence (policyEpoch FM key plan occurrence supply o t π prior)).sPrev = prior := by
  unfold policyEpoch
  split <;> rfl

/-- The next prior of `π` is the posterior of its admitted record: consecutive
admitted records of one policy chain (`s_{τ+1}.sPrev = s_τ.q`) by construction, which is
what W7's `chainBroken` check requires. -/
theorem nextPolicyBelief_admitted (e : PolicyIndex → PolicyEpoch M P S O) (π : PolicyIndex)
    (s : Step M P S O) (h : e π = .admitted s) : nextPolicyBelief e π = s.q := by
  simp [nextPolicyBelief, h]

/-- Accumulated successful loop state. -/
structure LoopState (M P S O U PolicyIndex : Type*) [Fintype S] [DecidableEq S] where
  belief : S → ℝ
  /-- Each policy's own record of the current state, `Q(s_τ | π)`
  (`refs/friston2017.txt:368-372`), carried from epoch to epoch. -/
  policyBelief : PolicyIndex → S → ℝ
  actions : List U
  history : List (PolicyIndex → PolicyEpoch M P S O)

/-- `n` closed-loop epochs, stopping at the first typed main-belief refusal. -/
def loop [LinearOrder U] (FM : ForwardModel S O U)
    (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (key : PolicyIndex → PolicyKey M P)
    (plan : PolicyIndex → ℕ → U) (occurrence : ℕ → String × String)
    (supply : PolicyIndex → ℕ → Supply) :
    ℕ → Except (StepAbsence PolicyIndex) (LoopState M P S O U PolicyIndex)
  | 0 => .ok { belief := FM.q₀, policyBelief := fun _ => FM.q₀, actions := [], history := [] }
  | n + 1 => (loop FM inputsAt world obs key plan occurrence supply n).bind fun st =>
      (epoch FM inputsAt world obs key plan occurrence supply n st.belief st.policyBelief).map fun r =>
        { belief := r.belief, policyBelief := nextPolicyBelief r.evidence,
          actions := st.actions ++ [r.action],
          history := st.history ++ [r.evidence] }

/-- `epoch` carries exactly the belief computed by the established machine step. -/
theorem epoch_belief_eq_machineStep [LinearOrder U]
    (FM : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (key : PolicyIndex → PolicyKey M P)
    (plan : PolicyIndex → ℕ → U) (occurrence : ℕ → String × String)
    (supply : PolicyIndex → ℕ → Supply)
    (t : ℕ) (μ : S → ℝ) (pb : PolicyIndex → S → ℝ) (r : EpochResult M P S O U PolicyIndex)
    (h : epoch FM inputsAt world obs key plan occurrence supply t μ pb = .ok r) :
    machineStep FM (plannedInputs inputsAt plan) world obs t μ = .ok r.belief := by
  unfold epoch at h
  cases hl : machineObservationLaw FM (plannedInputs inputsAt plan t μ) (world t) with
  | error a => simp [hl] at h
  | ok val =>
    obtain ⟨u, law⟩ := val
    rw [hl] at h
    unfold machineStep
    rw [hl]
    by_cases hz : law (obs (t + 1)) = 0
    · simp [hz] at h
    · simp only [hz, if_false] at h ⊢
      cases hu : exactUpdate FM.A (FM.B u) (obs (t + 1)) μ with
      | none => simp [hu] at h
      | some μ' =>
        simp only [hu, Except.ok.injEq] at h ⊢
        subst r
        rfl

/-- The loop's main belief is exactly the established machine trajectory. -/
theorem loop_belief_eq_machineTrajectory [LinearOrder U]
    (FM : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (key : PolicyIndex → PolicyKey M P)
    (plan : PolicyIndex → ℕ → U) (occurrence : ℕ → String × String)
    (supply : PolicyIndex → ℕ → Supply) :
    ∀ n st, loop FM inputsAt world obs key plan occurrence supply n = .ok st →
      machineTrajectory FM (plannedInputs inputsAt plan) world obs n = .ok st.belief := by
  intro n
  induction n with
  | zero =>
    intro st h
    have hs := congrArg LoopState.belief (Except.ok.inj h)
    simpa [loop, machineTrajectory] using hs
  | succ n ih =>
    intro st h
    cases hl : loop FM inputsAt world obs key plan occurrence supply n with
    | error a =>
      simp only [loop, hl, Except.bind] at h
      cases h
    | ok prev =>
      cases he : epoch FM inputsAt world obs key plan occurrence supply n prev.belief
          prev.policyBelief with
      | error a =>
        simp only [loop, hl, Except.bind, he, Except.map] at h
        cases h
      | ok r =>
        simp only [loop, hl, Except.bind, he, Except.map, Except.ok.injEq] at h
        have hb := congrArg LoopState.belief h
        have ht := ih prev hl
        have hs := epoch_belief_eq_machineStep FM inputsAt world obs key plan occurrence supply
          n prev.belief prev.policyBelief r he
        simp only at hb
        rw [machineTrajectory, ht, Except.bind, hs]
        exact congrArg Except.ok hb

/-- The next rollout starts at the belief left by the preceding loop. -/
theorem next_rollout_starts_at_loop_belief [LinearOrder U] [DecidableEq PolicyIndex]
    (FM : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (key : PolicyIndex → PolicyKey M P)
    (plan : PolicyIndex → ℕ → U) (occurrence : ℕ → String × String)
    (supply : PolicyIndex → ℕ → Supply)
    (n T : ℕ) (π : PolicyIndex) (st : LoopState M P S O U PolicyIndex)
    (f : Fin (T + 1) → O → ℝ)
    (hl : loop FM inputsAt world obs key plan occurrence supply n = .ok st)
    (hr : machineRollout FM (plannedInputs inputsAt plan) world obs n T π plan = .ok f) :
    ∀ o, f 0 o = ∑ s, FM.A s o * st.belief s := by
  obtain ⟨μ, hm, hf⟩ := machineRollout_startsAtCurrentBelief FM
    (plannedInputs inputsAt plan) world obs n T π plan f hr
  have hs := loop_belief_eq_machineTrajectory FM inputsAt world obs key plan occurrence supply
    n st hl
  rw [hs] at hm
  cases Except.ok.inj hm
  exact hf

/-- Every admitted policy record has F equal to negative log evidence under that
policy's prediction. -/
theorem admitted_stepF_eq_negLogEvidence (s : Step M P S O)
    (hA : ∀ x, 0 ≤ s.A x s.o) (hB : ∀ a x, 0 ≤ s.B a x)
    (hB1 : ∀ a, ∑ x, s.B a x = 1) (hp : ∀ a, 0 ≤ s.sPrev a)
    (hp1 : ∑ a, s.sPrev a = 1)
    (hZ : 0 < observationProbability s.A s.B s.o s.sPrev)
    (hq : exactUpdate s.A s.B s.o s.sPrev = some s.q) :
    stepF s = ↑(-Real.log (observationProbability s.A s.B s.o s.sPrev)) :=
  stepF_eq_negLogEvidence s hA hB hB1 hp hp1 hZ hq

/-- A contradicted policy has zero weight at the next selection, independently of
which action was executed. -/
theorem contradicted_policy_has_zero_weight
    (habit : PolicyKey M P → ℝ) (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) (ws : List ℝ)
    (h : machineWeightsAtPrefixF habit grade steps tau policies = .ok ws)
    (p : PolicyKey M P × ℝ) (hp : p ∈ policies.zip ws)
    (hc : prefixF p.1 (steps p.1) = .error .contradiction) : p.2 = 0 :=
  contradictionHasZeroWeight habit grade steps tau policies ws h p hp hc

/-- The encoded contradictory epoch record supplies the premise of the next
selection's zero-weight theorem. The selected action does not occur in the statement. -/
theorem encoded_epoch_contradiction_has_zero_weight
    (habit : PolicyKey M P → ℝ) (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) (ws : List ℝ)
    (hweights : machineWeightsAtPrefixF habit grade steps tau policies = .ok ws)
    (π : PolicyKey M P) (pre : List (Step M P S O)) (e : PolicyEpoch M P S O)
    (q : S → ℝ) (hadmit : admittedPrefix π (pre ++ [encode e q]) =
      (pre, some .contradiction))
    (hsteps : steps π = pre ++ [encode e q]) (p : PolicyKey M P × ℝ)
    (hp : p ∈ policies.zip ws) (hπ : p.1 = π) : p.2 = 0 := by
  apply contradicted_policy_has_zero_weight habit grade steps tau policies ws hweights p hp
  rw [hπ, hsteps]
  exact contradicted_record_gives_prefix_contradiction π pre e q hadmit

/-- One loop epoch is exactly one invocation of `epoch` from the initial belief. -/
theorem loop_one [LinearOrder U]
    (FM : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (key : PolicyIndex → PolicyKey M P)
    (plan : PolicyIndex → ℕ → U) (occurrence : ℕ → String × String)
    (supply : PolicyIndex → ℕ → Supply) :
    loop FM inputsAt world obs key plan occurrence supply 1 =
      (epoch FM inputsAt world obs key plan occurrence supply 0 FM.q₀ (fun _ => FM.q₀)).map fun r =>
        { belief := r.belief, policyBelief := nextPolicyBelief r.evidence,
          actions := [r.action], history := [r.evidence] } := by
  rfl

#print axioms encode_q_irrelevant
#print axioms contradicted_record_gives_prefix_contradiction
#print axioms loop_belief_eq_machineTrajectory
#print axioms next_rollout_starts_at_loop_belief
#print axioms admitted_stepF_eq_negLogEvidence
#print axioms contradicted_policy_has_zero_weight
#print axioms encoded_epoch_contradiction_has_zero_weight
#print axioms loop_one
#print axioms policyEpoch_sPrev
#print axioms nextPolicyBelief_admitted

end

end DarkTower.WarMachine.Proof2.ClosedLoopAtMachine
