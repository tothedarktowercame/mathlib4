import DarkTower.WarMachine.PolicyExpectedFreeEnergy
import DarkTower.WarMachine.Proof2.OuterSelectionCanonicalG

/-!+# Mission choice before inner plan construction

Sources read: refs/friston2017.txt:596-625 (eq. 2.6, outcome risk and
conditional observation entropy); refs/dacosta2020.txt:1397-1445
(eqs. 42-46: parameter novelty, outcome preferences, averaged likelihood).
These sources give the decomposition, not a mission-feature regression rule.

Modelling choices: `advance m` is one bounded attempt at mission m. `S` is
its latent progress/feasibility state at the explicitly declared horizon;
`Θ` is the uncertain likelihood parameter; `O` is the terminal outer outcome
(including resource use when resource use is to be preferred). This is a
terminal-horizon model, not a sum that counts the same information repeatedly.
State prediction is conditioned on mission observations. A nonnegative normalized
parameter posterior and a stochastic likelihood give the averaged likelihood.
Novelty is I(Θ; O | S), the expected parameter gain after hypothetical state /
outcome feedback in eq. 42, NOT an additional subtraction of state information.
This does not claim that a live click observes S or supplies these inputs.

Cost has exactly one interpretation: negative log declared outcome preference.
There is no additional resource penalty or engineering score. Preferences are
strictly positive in this finite-score model; zero-preference outcomes need
the separate extended-real treatment, not smoothing. Need/enable edges are
observations, never probabilities or automatic eligibility exclusions.
The observation-to-state kernel is an explicit model input: no feature weights,
prior or learning/admission rule is invented here. Eligibility is separately
declared. Inner families are carried in `World` but never read by scoring.

This file neither changes Q2/Q4/Q8 nor claims a Clojure implementation.
-/

namespace DarkTower.WarMachine.OuterMissionModel
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Mission := Nat
inductive Action where
  | advance (mission : Mission)
  deriving DecidableEq

structure Observations where
  offer : ℝ
  readinessSignal : Bool
  needEnable : List (Nat × Bool)
  resourceHistory : List ℝ

def Probability {X : Type*} [Fintype X] (p : X → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

structure Model (S Θ O : Type*) [Fintype S] [Fintype Θ] [Fintype O] where
  horizon : Nat
  horizon_pos : 0 < horizon
  statePrediction : Observations → Mission → S → ℝ
  state_valid : ∀ e m, Probability (statePrediction e m)
  parameterPosterior : Θ → ℝ
  parameter_valid : Probability parameterPosterior
  likelihood : Mission → O → S → Θ → ℝ
  likelihood_valid : ∀ m s θ, Probability (fun o => likelihood m o s θ)

structure Inputs (S Θ O : Type*) [Fintype S] [Fintype Θ] [Fintype O] where
  observations : Mission → Observations
  model : Model S Θ O
  preference : O → ℝ
  preference_valid : Probability preference
  preference_pos : ∀ o, 0 < preference o
  eligible : List Mission
  gamma : ℝ
  gamma_pos : 0 < gamma

structure World (S Θ O Family : Type*) [Fintype S] [Fintype Θ] [Fintype O] where
  outer : Inputs S Θ O
  innerFamilies : Mission → Family

variable {S Θ O Family : Type*} [Fintype S] [Fintype Θ] [Fintype O]

def averagedLikelihood (i : Inputs S Θ O) (m : Mission) (o : O) (s : S) : ℝ :=
  ∑ θ, i.model.parameterPosterior θ * i.model.likelihood m o s θ

def prediction (i : Inputs S Θ O) (m : Mission) : O → ℝ :=
  PolicyExpectedFreeEnergy.predictedOutcome (averagedLikelihood i m)
    (i.model.statePrediction (i.observations m) m)

/-- If this failed, a valid parameter posterior could produce a malformed
likelihood before mission scoring even starts. -/
theorem averaged_likelihood_valid (i : Inputs S Θ O) (m : Mission) (s : S) :
    Probability (fun o => averagedLikelihood i m o s) := by
  constructor
  · intro o
    exact Finset.sum_nonneg fun θ _ => mul_nonneg (i.model.parameter_valid.1 θ)
      ((i.model.likelihood_valid m s θ).1 o)
  · unfold averagedLikelihood
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (i.model.likelihood_valid m s _).2, mul_one]
    exact i.model.parameter_valid.2

/-- If this failed, an outer score could be based on unnormalized predicted
outcomes rather than a distribution. -/
theorem prediction_valid (i : Inputs S Θ O) (m : Mission) :
    Probability (prediction i m) := by
  constructor
  · intro o
    exact Finset.sum_nonneg fun s _ => mul_nonneg
      ((averaged_likelihood_valid i m s).1 o)
      ((i.model.state_valid (i.observations m) m).1 s)
  · unfold prediction PolicyExpectedFreeEnergy.predictedOutcome
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, (averaged_likelihood_valid i m _).2, one_mul]
    exact (i.model.state_valid (i.observations m) m).2

def risk (i : Inputs S Θ O) (m : Mission) : ℝ :=
  PolicyExpectedFreeEnergy.finiteRisk (prediction i m) i.preference

def ambiguity (i : Inputs S Θ O) (m : Mission) : ℝ :=
  PolicyExpectedFreeEnergy.ambiguity (averagedLikelihood i m)
    (i.model.statePrediction (i.observations m) m)

/-- Conditional mutual information about the likelihood parameter. Zero
joint mass contributes zero; no logarithm-zero substitute scores a refusal. -/
def informationGain (i : Inputs S Θ O) (m : Mission) : ℝ :=
  ∑ s, i.model.statePrediction (i.observations m) m s *
    ∑ θ, i.model.parameterPosterior θ *
      ∑ o, i.model.likelihood m o s θ *
        (Real.log (i.model.likelihood m o s θ) -
          Real.log (averagedLikelihood i m o s))

def outcomeCost (i : Inputs S Θ O) (o : O) : ℝ := -Real.log (i.preference o)

/-- If this failed, the cost interpretation would not agree with risk and
could conceal a second, independently added resource penalty. -/
theorem risk_uses_declared_cost (i : Inputs S Θ O) (m : Mission) :
    risk i m = ∑ o, if 0 < prediction i m o then
      prediction i m o * Real.log (prediction i m o) +
        prediction i m o * outcomeCost i o else 0 := by
  unfold risk PolicyExpectedFreeEnergy.finiteRisk
  apply Finset.sum_congr rfl
  intro o _
  split_ifs
  · unfold outcomeCost
    ring
  · rfl

def G (i : Inputs S Θ O) (m : Mission) : ℝ :=
  risk i m + ambiguity i m - informationGain i m

def policy (i : Inputs S Θ O) (m : Mission) :
    Proof2.OuterSelectionCanonicalG.OuterPolicy :=
  ⟨m, risk i m, ambiguity i m, informationGain i m, 0⟩

def frontier (w : World S Θ O Family) : List Mission :=
  w.outer.eligible.filter fun m =>
    w.outer.eligible.all fun n => decide (G w.outer m ≤ G w.outer n)

/-- If this failed, the reused objective algebra would not justify the
mission G ordering even with common positive precision and constant prior. -/
theorem objective_order (i : Inputs S Θ O) (m n : Mission) :
    Proof2.OuterSelectionCanonicalG.outerObjective i.gamma (policy i m) ≤
      Proof2.OuterSelectionCanonicalG.outerObjective i.gamma (policy i n) ↔
    G i m ≤ G i n :=
  Proof2.OuterSelectionCanonicalG.objective_order_iff_G_order i.gamma 0
    i.gamma_pos (policy i m) (policy i n) rfl rfl

/-- If this failed, changing inner plans could change an outer comparison
despite identical observations, parameters, preferences and selection inputs. -/
theorem outer_invariance (a b : World S Θ O Family) (h : a.outer = b.outer) :
    (∀ m, G a.outer m = G b.outer m) ∧ frontier a = frontier b := by
  constructor
  · intro m; rw [h]
  · simp only [frontier, h]

def selected (w : World S Θ O Family) (slot : Nat) : Option Mission :=
  (frontier w)[slot]?

/-- If this failed, equal frontiers could choose different missions using
the same recorded draw. Out-of-range draws remain explicit absence. -/
theorem same_draw_same_selection (a b : World S Θ O Family)
    (h : a.outer = b.outer) (slot : Nat) : selected a slot = selected b slot := by
  simp only [selected, (outer_invariance a b h).2]

/-- If this failed, even an unselected family's contents could secretly be
an input to mission prediction or choice. In fact *all* families are irrelevant. -/
theorem replace_families (w : World S Θ O Family) (f : Mission → Family) :
    (∀ m, G w.outer m = G ({w with innerFamilies := f}).outer m) ∧
      frontier w = frontier {w with innerFamilies := f} :=
  outer_invariance _ _ rfl

inductive ConstructionOutcome (Plan : Type*) where
  | noSelection
  | missing (mission : Mission)
  | constructed (mission : Mission) (plan : Plan)
  deriving DecidableEq

def constructSelected {Plan : Type*} (w : World S Θ O Family) (slot : Nat)
    (build : Mission → Family → Option Plan) : ConstructionOutcome Plan :=
  match selected w slot with
  | none => .noSelection
  | some m => match build m (w.innerFamilies m) with
    | none => .missing m
    | some p => .constructed m p

/-- If this failed, construction could name an unselected mission. This is
a pure dispatch contract, not a theorem that an external builder terminates. -/
theorem construction_only_selected {Plan : Type*} (w : World S Θ O Family)
    (slot : Nat) (build : Mission → Family → Option Plan) (m : Mission) (p : Plan)
    (h : constructSelected w slot build = .constructed m p) : selected w slot = some m := by
  unfold constructSelected at h
  split at h <;> simp_all
  split at h <;> simp_all

/-- If this failed, missing construction could silently choose a fallback
mission rather than record the selected mission's missing construction. -/
theorem missing_is_recorded {Plan : Type*} (w : World S Θ O Family) (slot : Nat)
    (build : Mission → Family → Option Plan) (m : Mission)
    (hs : selected w slot = some m) (hb : build m (w.innerFamilies m) = none) :
    constructSelected w slot build = .missing m := by
  simp [constructSelected, hs, hb]

/-! A fully normalized sensitivity witness: two latent states and outcomes,
one known parameter, deterministic likelihood, one-step horizon. A readiness
measurement switches mission 0's state belief; mission 1 stays uncertain.
Preferences put 7/8 on progress (true), 1/8 on no progress (false).
These are illustrative model inputs, not fitted mission probabilities. -/

def witnessModel : Model Bool Unit Bool where
  horizon := 1
  horizon_pos := by decide
  statePrediction := fun e m s =>
    if m = 0 then (if s = e.readinessSignal then 1 else 0) else 1/2
  state_valid := by
    intro e m
    by_cases hm : m = 0
    · cases e.readinessSignal <;> simp [Probability, hm]
    · norm_num [Probability, hm]
  parameterPosterior := fun _ => 1
  parameter_valid := by simp [Probability]
  likelihood := fun _ o s _ => if o = s then 1 else 0
  likelihood_valid := by
    intro m s θ
    cases s <;> simp [Probability]

def witnessInputs (ready : Bool) : Inputs Bool Unit Bool where
  observations := fun _ => ⟨0, ready, [], []⟩
  model := witnessModel
  preference := fun o => if o then 7/8 else 1/8
  preference_valid := by
    constructor
    · intro o; cases o <;> norm_num
    · simp; norm_num
  preference_pos := by intro o; cases o <;> norm_num
  eligible := [0, 1]
  gamma := 1
  gamma_pos := by norm_num

def witnessWorld (ready : Bool) (families : Mission → List Nat) :
    World Bool Unit Bool (List Nat) := ⟨witnessInputs ready, families⟩

/-- Failure would invalidate the witness's deterministic, known-parameter
interpretation: its ambiguity and parameter novelty must both vanish. -/
private theorem witness_terms (ready : Bool) (m : Mission) :
    ambiguity (witnessInputs ready) m = 0 ∧ informationGain (witnessInputs ready) m = 0 := by
  constructor
  · apply PolicyExpectedFreeEnergy.ambiguity_point_mass
    intro s
    refine ⟨s, ?_⟩
    intro o
    simp [averagedLikelihood, witnessInputs, witnessModel]
  · simp [informationGain, averagedLikelihood, witnessInputs, witnessModel]

/-- Failure would mean the numerical witness was not scored by the actual
model definitions; the ranking proof must not use hand-assigned scores. -/
private theorem witness_scores :
    G (witnessInputs true) 0 = -Real.log (7/8) ∧
    G (witnessInputs false) 0 = -Real.log (1/8) ∧
    (∀ ready, G (witnessInputs ready) 1 =
      Real.log (1/2) - (Real.log (1/8) + Real.log (7/8))/2) := by
  simp only [G, (witness_terms _ _).1, (witness_terms _ _).2, add_zero, sub_zero]
  norm_num [risk, PolicyExpectedFreeEnergy.finiteRisk, prediction,
    PolicyExpectedFreeEnergy.predictedOutcome, averagedLikelihood, witnessInputs, witnessModel]
  ring

/-- If this failed, the purported mission model could ignore relevant
evidence: here an observed readiness change reverses a strict comparison. -/
theorem evidence_changes_prediction_and_ranking :
    prediction (witnessInputs false) 0 true = 0 ∧
    prediction (witnessInputs true) 0 true = 1 ∧
    G (witnessInputs true) 0 < G (witnessInputs true) 1 ∧
    G (witnessInputs false) 1 < G (witnessInputs false) 0 := by
  have hlog : 0 < Real.log (7 : ℝ) := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)
    norm_num at this
    convert this using 1; ring
  have h74 : 2 * Real.log 2 < Real.log (7 : ℝ) := by
    rw [← h4]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  rcases witness_scores with ⟨ha, hb, hc⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [prediction, PolicyExpectedFreeEnergy.predictedOutcome,
      averagedLikelihood, witnessInputs, witnessModel]
  · norm_num [prediction, PolicyExpectedFreeEnergy.predictedOutcome,
      averagedLikelihood, witnessInputs, witnessModel]
  · rw [ha, hc]
    rw [Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
    norm_num at *
    linarith
  · rw [hb, hc]
    rw [Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
    norm_num at *
    linarith

/-- If this failed, the strict score reversal would not actually change the
selected mission. Families may differ arbitrarily across the two worlds. -/
theorem evidence_changes_selection (f g : Mission → List Nat) :
    frontier (witnessWorld true f) = [0] ∧
    frontier (witnessWorld false g) = [1] ∧
    selected (witnessWorld true f) 0 = some 0 ∧
    selected (witnessWorld false g) 0 = some 1 := by
  have ht := evidence_changes_prediction_and_ranking.2.2.1
  have hf := evidence_changes_prediction_and_ranking.2.2.2
  have ft : frontier (witnessWorld true f) = [0] := by
    dsimp only [frontier, witnessWorld]
    have he : (witnessInputs true).eligible = [0, 1] := rfl
    rw [he]
    simp [le_of_lt ht, not_le_of_gt ht]
  have ff : frontier (witnessWorld false g) = [1] := by
    dsimp only [frontier, witnessWorld]
    have he : (witnessInputs false).eligible = [0, 1] := rfl
    rw [he]
    simp [le_of_lt hf, not_le_of_gt hf]
  exact ⟨ft, ff, by simp [selected, ft], by simp [selected, ff]⟩

#print axioms averaged_likelihood_valid
#print axioms prediction_valid
#print axioms risk_uses_declared_cost
#print axioms objective_order
#print axioms outer_invariance
#print axioms same_draw_same_selection
#print axioms replace_families
#print axioms construction_only_selected
#print axioms missing_is_recorded
#print axioms evidence_changes_prediction_and_ranking
#print axioms evidence_changes_selection
#print axioms witness_terms
#print axioms witness_scores

end
end DarkTower.WarMachine.OuterMissionModel
