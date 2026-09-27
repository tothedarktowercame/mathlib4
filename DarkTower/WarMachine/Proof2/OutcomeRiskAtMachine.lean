import DarkTower.WarMachine.OutcomeRiskKL
import DarkTower.WarMachine.Proof2.RolloutAtMachine

/-!
# Outcome risk at the machine's rollout (P-inst-Q, registry `:risk` ← `:forward-model`)

The [R4→R5] `:Q-o-pi` edge. The consumer `:risk` is `OutcomeRiskKL.outcomeRisk`,
which takes `Q : PredictiveOutcomeKernel PolicyIndex Obs` as a **free** argument;
the consumer `:ambiguity` (`Holes.ambiguity`) likewise. The source row
`:forward-model` owns `machineRollout` (`Proof2/RolloutAtMachine.lean`), the
predicted outcome distribution `Q(o|π)` from the machine's CURRENT belief. No R5
module imported `RolloutAtMachine`, so the edge was term-present-not-imported.

This module supplies the consumer's free `Q` from the machine's source term:

* `machineOutcomeKernel M μ _ _ plan v τ` is a `PredictiveOutcomeKernel` whose row
  at `π` is the step-`τ` predicted outcome distribution of the model started at the
  machine's belief `μ` (`withBelief`), vertex-tagged at the PARAMETER vertex `v`
  (no vertex default: the machine's `O` is untagged, so the tag is an argument).
* `machineOutcomeRisk` is `outcomeRisk` applied to that kernel, at the belief
  `machineTrajectory … t` computes, with the rollout's refusals carried as typed
  absences (`OutcomeRiskAbsence.rollout`) — no default belief, policy, horizon, or
  preference: an absent rollout gives an absent risk carrying the rollout's own
  absence; the preference distribution `C` remains an argument (a separate
  uninhabited fundamental, per `MachineQ`'s note on the same choice).
* `machineOutcomeRisk_eq_outcomeRisk` is the instantiation theorem: on the rollout's
  ok arm the value is `outcomeRisk` of the machine kernel;
  `machineOutcomeKernel_row_eq_rollout` says the kernel's row at `π` IS the rollout's
  returned family `f` at step `τ`.
* The bad case `machineOutcomeRisk_changes_with_the_source` exhibits two source
  values (the rollout from `q₀` and the rollout from a different belief) giving
  different consumer values (`≠ ⊤` vs `⊤`) against the same preference.

The vertex type is finite; the instance is declared here because `Holes.Vertex`
carries none and the kernel's support is the full (finite) outcome space.
-/

namespace DarkTower.WarMachine.Proof2.OutcomeRiskAtMachine

open DarkTower.WarMachine
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.OutcomeRiskKL
open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
open DarkTower.WarMachine.Proof2.ObservationAtMachine
open DarkTower.WarMachine.Proof2.BeliefAtMachine
open DarkTower.WarMachine.Proof2.BeliefStepAtMachine
open DarkTower.WarMachine.Proof2.RolloutAtMachine

noncomputable section

/-- The four vertices are a finite type. Declared here (not in `Holes`) so the
kernel below can list the whole outcome space as its support. -/
instance : Fintype Vertex where
  elems := {Vertex.nouns, Vertex.verbs, Vertex.organization, Vertex.evidence}
  complete := fun v => by cases v <;> decide

variable {S O U PolicyIndex : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- The step-`τ` predicted outcome mass of the model started at the machine's
belief, vertex-tagged at `v`: outcomes at other vertices carry zero. -/
def machineOutcomeMass (M : ForwardModel S O U) (μ : S → ℝ)
    (h0 : ∀ s, 0 ≤ μ s) (h1 : ∑ s, μ s = 1) (plan : PolicyIndex → ℕ → U)
    (v : Vertex) (τ : ℕ) (π : PolicyIndex) (x : Outcome (fun _ : Vertex => O)) : ℝ :=
  if x.1 = v then predictedOutcome (withBelief M μ h0 h1) (plan π) τ x.2 else 0

theorem machineOutcomeMass_nonneg (M : ForwardModel S O U) (μ : S → ℝ)
    (h0 : ∀ s, 0 ≤ μ s) (h1 : ∑ s, μ s = 1) (plan : PolicyIndex → ℕ → U)
    (v : Vertex) (τ : ℕ) (π : PolicyIndex) (x : Outcome (fun _ : Vertex => O)) :
    0 ≤ machineOutcomeMass M μ h0 h1 plan v τ π x := by
  unfold machineOutcomeMass
  split_ifs
  · exact predictedOutcome_nonneg _ _ _ _
  · exact le_refl 0

/-- Each row is normalised: the tagged mass sums the `v`-fibre, which is
`predictedOutcome`'s own normalisation, and every other fibre is zero. -/
theorem machineOutcomeMass_sum (M : ForwardModel S O U) (μ : S → ℝ)
    (h0 : ∀ s, 0 ≤ μ s) (h1 : ∑ s, μ s = 1) (plan : PolicyIndex → ℕ → U)
    (v : Vertex) (τ : ℕ) (π : PolicyIndex) :
    ((Finset.univ : Finset (Outcome (fun _ : Vertex => O))).toList.map
      (machineOutcomeMass M μ h0 h1 plan v τ π)).sum = 1 := by
  rw [Finset.sum_map_toList, Fintype.sum_sigma]
  have hrw : ∀ v' : Vertex, ∀ o : O,
      machineOutcomeMass M μ h0 h1 plan v τ π ⟨v', o⟩
        = if v' = v then predictedOutcome (withBelief M μ h0 h1) (plan π) τ o else 0 :=
    fun _ _ => rfl
  simp only [hrw]
  have h : ∀ v' : Vertex,
      (∑ o : O, if v' = v then predictedOutcome (withBelief M μ h0 h1) (plan π) τ o else 0)
        = if v' = v then 1 else 0 := by
    intro v'
    by_cases hv : v' = v
    · simp [hv, predictedOutcome_sum]
    · simp [hv]
  rw [Finset.sum_congr rfl (fun v' _ => h v'), Finset.sum_ite_eq', if_pos (Finset.mem_univ v)]

/-- **The consumer's `Q` from the machine's source term.** `Q(o|π)` as a
`PredictiveOutcomeKernel` whose mass is the step-`τ` predicted outcome of the
model started at the machine's belief — the value `machineRollout` returns — with
the whole outcome space as support and normalisation by proof. -/
def machineOutcomeKernel (M : ForwardModel S O U) (μ : S → ℝ)
    (h0 : ∀ s, 0 ≤ μ s) (h1 : ∑ s, μ s = 1) (plan : PolicyIndex → ℕ → U)
    (v : Vertex) (τ : ℕ) : PredictiveOutcomeKernel PolicyIndex (fun _ : Vertex => O) where
  support _ := Finset.univ.toList
  mass := machineOutcomeMass M μ h0 h1 plan v τ
  nonnegative := machineOutcomeMass_nonneg M μ h0 h1 plan v τ
  support_nodup := fun _ => Finset.nodup_toList _
  mass_eq_zero_of_not_mem := fun _ x hx =>
    absurd (Finset.mem_toList.mpr (Finset.mem_univ x)) hx
  normalised := machineOutcomeMass_sum M μ h0 h1 plan v τ

/-- Why there is no machine outcome risk: the rollout that supplies `Q` refused.
Each arm carries the rollout's own absence, unchanged. -/
inductive OutcomeRiskAbsence (PolicyIndex : Type*) where
  | rollout (a : RolloutAbsence PolicyIndex)

/-- **`machineOutcomeRisk`.** `outcomeRisk` (Da Costa et al. 2020 eq. (44), the R5
consumer `:risk`) with `Q` supplied from the machine's rollout at time `t`: the
belief is `machineTrajectory … t`, the policy must be one of the machine's own
list, `T = 0` is a refusal, and `C` stays an argument. Refusals are the rollout's,
carried. -/
def machineOutcomeRisk [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t : ℕ) (T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (v : Vertex) (τ : Fin (T + 1))
    (C : PreferenceDistribution (fun _ : Vertex => O)) :
    Except (OutcomeRiskAbsence PolicyIndex) EReal :=
  match h : machineTrajectory M inputsAt world obs t with
  | .error a => .error (.rollout (.belief a))
  | .ok μ =>
    if T = 0 then .error (.rollout .zeroDepth)
    else if π ∈ (inputsAt t μ).policies then
      .ok (outcomeRisk
        (machineOutcomeKernel M μ
          (machineTrajectory_isDistribution M inputsAt world obs t μ h).1
          (machineTrajectory_isDistribution M inputsAt world obs t μ h).2
          plan v τ) C π)
    else .error (.rollout .notInPolicySet)

/-- **The instantiation.** On the rollout's ok arm, the machine outcome risk IS
`outcomeRisk` of the machine kernel at the machine's belief — the parametric R5
declaration applied to the machine's own `Q`. -/
theorem machineOutcomeRisk_eq_outcomeRisk [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t : ℕ) (T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (v : Vertex) (τ : Fin (T + 1))
    (C : PreferenceDistribution (fun _ : Vertex => O)) (f : Fin (T + 1) → O → ℝ)
    (hrun : machineRollout M inputsAt world obs t T π plan = .ok f) :
    ∃ μ, ∃ hd : (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1,
      machineTrajectory M inputsAt world obs t = .ok μ ∧
      machineOutcomeRisk M inputsAt world obs t T π plan v τ C
        = .ok (outcomeRisk (machineOutcomeKernel M μ hd.1 hd.2 plan v τ) C π) := by
  obtain ⟨μ, hd, hμ, hT, hπ, _⟩ :=
    machineRollout_eq_predictedOutcome M inputsAt world obs t T π plan f hrun
  refine ⟨μ, hd, hμ, ?_⟩
  unfold machineOutcomeRisk
  split
  · rename_i a ha; rw [hμ] at ha; cases ha
  · rename_i μ' hμ'; rw [hμ] at hμ'; cases hμ'
    rw [if_neg hT, if_pos hπ]

/-- **The kernel's row at `π` is the rollout's returned family.** The `Q` the
consumer sees at `π`, step `τ`, outcome `o` is the value `machineRollout`
returned — the source term's value, not a parallel construction. -/
theorem machineOutcomeKernel_row_eq_rollout [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t : ℕ) (T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (v : Vertex) (τ : Fin (T + 1))
    (f : Fin (T + 1) → O → ℝ)
    (hrun : machineRollout M inputsAt world obs t T π plan = .ok f) :
    ∃ μ, ∃ hd : (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1,
      ∀ o : O, (machineOutcomeKernel M μ hd.1 hd.2 plan v τ).mass π ⟨v, o⟩ = f τ o := by
  obtain ⟨μ, hd, _, _, _, hf⟩ :=
    machineRollout_eq_predictedOutcome M inputsAt world obs t T π plan f hrun
  refine ⟨μ, hd, fun o => ?_⟩
  have hmass : (machineOutcomeKernel M μ hd.1 hd.2 plan v τ).mass π ⟨v, o⟩
      = predictedOutcome (withBelief M μ hd.1 hd.2) (plan π) τ o := by
    simp [machineOutcomeKernel, machineOutcomeMass]
  exact hmass.trans (hf τ o).symm

/-! ## The absences, carried and reachable -/

theorem machineOutcomeRisk_absentBelief [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t : ℕ) (T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (v : Vertex) (τ : Fin (T + 1))
    (C : PreferenceDistribution (fun _ : Vertex => O)) (a : StepAbsence PolicyIndex)
    (h : machineTrajectory M inputsAt world obs t = .error a) :
    machineOutcomeRisk M inputsAt world obs t T π plan v τ C
      = .error (.rollout (.belief a)) := by
  unfold machineOutcomeRisk
  split
  · rename_i a' ha'; rw [h] at ha'; cases ha'; rfl
  · rename_i μ hμ; rw [h] at hμ; cases hμ

theorem machineOutcomeRisk_zeroDepth [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (v : Vertex) (τ : Fin 1)
    (C : PreferenceDistribution (fun _ : Vertex => O)) (μ : S → ℝ)
    (h : machineTrajectory M inputsAt world obs t = .ok μ) :
    machineOutcomeRisk M inputsAt world obs t 0 π plan v τ C
      = .error (.rollout .zeroDepth) := by
  unfold machineOutcomeRisk
  split
  · rename_i a ha; rw [h] at ha; cases ha
  · simp

theorem machineOutcomeRisk_notInPolicySet [LinearOrder U] [DecidableEq PolicyIndex]
    (M : ForwardModel S O U) (inputsAt : ℕ → (S → ℝ) → PolicyInputs PolicyIndex U)
    (world : ℕ → S) (obs : ℕ → O) (t : ℕ) (T : ℕ) (π : PolicyIndex)
    (plan : PolicyIndex → ℕ → U) (v : Vertex) (τ : Fin (T + 1))
    (C : PreferenceDistribution (fun _ : Vertex => O)) (μ : S → ℝ) (hT : T ≠ 0)
    (h : machineTrajectory M inputsAt world obs t = .ok μ)
    (hπ : π ∉ (inputsAt t μ).policies) :
    machineOutcomeRisk M inputsAt world obs t T π plan v τ C
      = .error (.rollout .notInPolicySet) := by
  unfold machineOutcomeRisk
  split
  · rename_i a ha; rw [h] at ha; cases ha
  · rename_i μ' hμ'
    rw [h] at hμ'; cases hμ'
    simp [hT, hπ]

/-! ## The bad case: a different source value changes the consumer's value

On the two-state identity-likelihood model of `RolloutAtMachine`'s bad case, the
rollout from the model's `q₀` (a point mass at `false`) predicts outcome `true` at
step 1 with probability `0`, and the rollout from the belief that is a point mass
at `true` predicts it with probability `1`. Against a preference distribution with
all mass on `false`, the first source value gives a finite risk and the second
gives `⊤`. A consumer that read any other `Q` than the machine's rollout could not
produce this difference. -/

/-- The fixture model: identity likelihood, keeping action, `q₀` a point mass at
`false`. (The concrete witness of `RolloutAtMachine.rolloutFromBelief_changes_the_outcome`,
rebuilt here so the consumer's value computes.) -/
def badModel : ForwardModel Bool Bool Bool where
  B := fun _ s s' => if s' = s then 1 else 0
  B_nonneg := by intro u s s'; split_ifs <;> norm_num
  B_rowsum := by intro u s; cases s <;> simp
  A := fun s o => if s = o then 1 else 0
  A_nonneg := by intro s o; split_ifs <;> norm_num
  A_colsum := by intro s; cases s <;> simp
  q₀ := fun s => if s = false then 1 else 0
  q₀_nonneg := by intro s; split_ifs <;> norm_num
  q₀_sum := by simp

/-- The fixture belief: a point mass at `true`. -/
def badBelief : Bool → ℝ := fun s => if s = true then 1 else 0

theorem badBelief_nonneg : ∀ s, 0 ≤ badBelief s := by
  intro s; dsimp only [badBelief]; split_ifs <;> norm_num

theorem badBelief_sum : ∑ s, badBelief s = 1 := by simp [badBelief]

/-- The fixture preference: all mass on `false` (tagged at the nouns vertex, the
vertex the bad-case kernels below tag at). -/
def badPrefNouns : PreferenceDistribution (fun _ : Vertex => Bool) where
  support := fun _ => [⟨Vertex.nouns, false⟩]
  mass := fun _ o => match o with
    | ⟨.nouns, false⟩ => 1
    | _ => 0
  nonnegative := by
    intro _ o; rcases o with ⟨v', b⟩; cases v' <;> cases b <;> norm_num
  support_nodup := by intro; simp
  mass_eq_zero_of_not_mem := by
    intro _ o h
    rcases o with ⟨v', b⟩; cases v' <;> cases b <;> simp_all
  normalised := by intro; norm_num

/-- From `q₀`, outcome `true` at step 1 has probability `0`. -/
theorem badModel_q0_predict_true :
    predictedOutcome (withBelief badModel badModel.q₀ badModel.q₀_nonneg badModel.q₀_sum)
      (fun _ => true) 1 true = 0 := by
  simp [predictedOutcome, rolloutState, withBelief, badModel]

/-- From `q₀`, outcome `false` at step 1 has probability `1`. -/
theorem badModel_q0_predict_false :
    predictedOutcome (withBelief badModel badModel.q₀ badModel.q₀_nonneg badModel.q₀_sum)
      (fun _ => true) 1 false = 1 := by
  simp [predictedOutcome, rolloutState, withBelief, badModel]

/-- From the belief that is a point mass at `true`, outcome `true` at step 1 has
probability `1`. -/
theorem badModel_belief_predict_true :
    predictedOutcome (withBelief badModel badBelief badBelief_nonneg badBelief_sum)
      (fun _ => true) 1 true = 1 := by
  simp [predictedOutcome, rolloutState, withBelief, badModel, badBelief]

/-- The machine kernel at the belief `badBelief`, step 1, against `badPrefNouns`. -/
def badKernelBelief : PredictiveOutcomeKernel Unit (fun _ : Vertex => Bool) :=
  machineOutcomeKernel badModel badBelief badBelief_nonneg badBelief_sum
    (fun _ _ => true) Vertex.nouns 1

/-- The kernel from the model's own `q₀` — a different source value for the same
consumer. -/
def badKernelQ0 : PredictiveOutcomeKernel Unit (fun _ : Vertex => Bool) :=
  machineOutcomeKernel badModel badModel.q₀ badModel.q₀_nonneg badModel.q₀_sum
    (fun _ _ => true) Vertex.nouns 1

/-- **The bad case.** The rollout from the machine's belief predicts `true` (a
zero-preference outcome) with probability `1`, so the consumer's risk is `⊤`; the
rollout from `q₀` predicts it with probability `0`, so the risk is finite. The
consumer's value changes with the source value. -/
theorem machineOutcomeRisk_changes_with_the_source :
    outcomeRisk badKernelBelief badPrefNouns () = ⊤ ∧
    outcomeRisk badKernelQ0 badPrefNouns () ≠ ⊤ := by
  constructor
  · rw [outcomeRisk_eq_top_iff]
    refine ⟨⟨Vertex.nouns, true⟩, Finset.mem_toList.mpr (Finset.mem_univ _), ?_, ?_⟩
    · show (0:ℝ) < if (⟨Vertex.nouns, true⟩ : Outcome (fun _ : Vertex => Bool)).1
          = Vertex.nouns then
          predictedOutcome (withBelief badModel badBelief badBelief_nonneg badBelief_sum)
            (fun _ => true) 1 true
        else 0
      rw [if_pos rfl, badModel_belief_predict_true]; norm_num
    · rfl
  · rw [outcomeRisk]
    split_ifs with hany
    · exfalso
      obtain ⟨o, _, htrue⟩ := List.any_eq_true.mp hany
      simp only [decide_eq_true_eq] at htrue
      obtain ⟨hpos, hc0⟩ := htrue
      rcases o with ⟨v', b⟩
      change (0:ℝ) < (if v' = Vertex.nouns then
          predictedOutcome (withBelief badModel badModel.q₀ badModel.q₀_nonneg
            badModel.q₀_sum) (fun _ => true) 1 b
        else 0) at hpos
      by_cases hv : v' = Vertex.nouns
      · rw [if_pos hv] at hpos
        cases b with
        | true =>
          rw [badModel_q0_predict_true] at hpos; exact absurd hpos (lt_irrefl 0)
        | false =>
          subst hv
          have h1 : badPrefNouns.mass () ⟨Vertex.nouns, false⟩ = 1 := rfl
          rw [h1] at hc0; norm_num at hc0
      · rw [if_neg hv] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact EReal.coe_ne_top _

end

#print axioms machineOutcomeMass
#print axioms machineOutcomeKernel
#print axioms machineOutcomeRisk
#print axioms machineOutcomeRisk_eq_outcomeRisk
#print axioms machineOutcomeKernel_row_eq_rollout
#print axioms machineOutcomeRisk_absentBelief
#print axioms machineOutcomeRisk_zeroDepth
#print axioms machineOutcomeRisk_notInPolicySet
#print axioms machineOutcomeRisk_changes_with_the_source
