import DarkTower.WarMachine.CascadeCoApplyG
import DarkTower.WarMachine.PolicyVariationalFreeEnergy
import DarkTower.WarMachine.PrecisionFromObservation

/-!
# Class-channel free energy from retained reading-policy outcomes

The history identity is the runtime Q6 reading-policy key.  A tick belongs to a
policy exactly when its retained key equals that policy's key.  The likelihood
is the candidate's existing class observation kernel; no smoothing is added.
Consequently a retained class with zero evidence is a typed impossibility, not
a finite penalty and not a skipped observation.
-/

namespace DarkTower.WarMachine.ReadingPolicyClassFreeEnergy

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.CascadeEFE
open DarkTower.WarMachine.CTauClassPreference
open DarkTower.WarMachine.PolicyVariationalFreeEnergy

noncomputable section

structure Makeup where
  historyWindow : Nat

structure RetainedTick (Key : Type*) where
  key : Key
  pin : String
  observed : EndingClass
  deriving DecidableEq

structure Model (Key S : Type*) where
  key : Key
  prior : ProbabilityKernel Unit S
  observation : ProbabilityKernel S EndingClass

def selectedHistory {Key : Type*} [DecidableEq Key] (makeup : Makeup) (key : Key)
    (history : List (RetainedTick Key)) : List (RetainedTick Key) :=
  ((history.filter fun tick => tick.key = key).reverse.take makeup.historyWindow).reverse

theorem mem_selectedHistory_key {Key : Type*} [DecidableEq Key] (makeup : Makeup)
    (key : Key) (history : List (RetainedTick Key)) (tick : RetainedTick Key)
    (member : tick ∈ selectedHistory makeup key history) : tick.key = key := by
  have taken : tick ∈ (history.filter fun item => item.key = key).reverse.take makeup.historyWindow := by
    simpa [selectedHistory] using member
  have filtered : tick ∈ history.filter fun item => item.key = key := by
    simpa using List.mem_of_mem_take taken
  exact of_decide_eq_true (List.mem_filter.mp filtered).2

def likelihood {Key S : Type*} (model : Model Key S) (observed : EndingClass) : S → ℝ :=
  fun state => model.observation.mass state observed

def tickEvidence {Key S : Type*} [Fintype S] (model : Model Key S)
    (tick : RetainedTick Key) : ℝ :=
  evidence (likelihood model tick.observed) (model.prior.mass ())

structure ImpossibleObservation (Key : Type*) where
  tick : RetainedTick Key
  evidence : ℝ
  evidence_zero : evidence = 0

inductive Result (Key : Type*) where
  | computed (value : ℝ) (history : List (RetainedTick Key)) (window : Nat)
  | observationImpossible (failure : ImpossibleObservation Key)

def evaluateTicks {Key S : Type*} [Fintype S] (model : Model Key S) :
    List (RetainedTick Key) → Result Key
  | [] => .computed 0 [] 0
  | tick :: rest =>
      let z := tickEvidence model tick
      if hz : z = 0 then .observationImpossible ⟨tick, z, hz⟩
      else match evaluateTicks model rest with
        | .computed value history window =>
            .computed (-Real.log z + value) (tick :: history) (window + 1)
        | .observationImpossible failure => .observationImpossible failure

def evaluate {Key S : Type*} [DecidableEq Key] [Fintype S] (makeup : Makeup)
    (model : Model Key S) (history : List (RetainedTick Key)) : Result Key :=
  let selected := selectedHistory makeup model.key history
  match evaluateTicks model selected with
  | .computed value _ _ => .computed value selected makeup.historyWindow
  | .observationImpossible failure => .observationImpossible failure

theorem evaluate_empty {Key S : Type*} [DecidableEq Key] [Fintype S]
    (makeup : Makeup) (model : Model Key S) :
    evaluate makeup model [] = .computed 0 [] makeup.historyWindow := by
  simp [evaluate, selectedHistory, evaluateTicks]

theorem zero_evidence_tick_impossible {Key S : Type*} [Fintype S]
    (model : Model Key S) (tick : RetainedTick Key) (rest : List (RetainedTick Key))
    (hz : tickEvidence model tick = 0) :
    evaluateTicks model (tick :: rest) =
      .observationImpossible ⟨tick, tickEvidence model tick, hz⟩ := by
  simp [evaluateTicks, hz]

/-- A policy whose retained observation has zero evidence receives zero
posterior mass.  This is the typed-impossibility branch's posterior meaning;
it is not represented by choosing an arbitrary large finite free energy. -/
theorem impossible_policy_posterior_zero {wa wb eb : ℝ}
    (_hwb : 0 < wb) (_heb : 0 < eb) :
    PrecisionFromObservation.binaryPosterior wa wb 0 eb = 0 := by
  simp [PrecisionFromObservation.binaryPosterior]

/-- On every finite tick, the exact posterior VFE is its surprisal.  This is
the existing B.2 equality theorem, instantiated with the retained class and
the unchanged class observation kernel. -/
theorem exact_tick_vfe_eq_surprisal {Key S : Type*} [Fintype S]
    (model : Model Key S) (tick : RetainedTick Key)
    (positive : 0 < tickEvidence model tick) :
    variationalFreeEnergy (likelihood model tick.observed) (model.prior.mass ())
        (posterior (likelihood model tick.observed) (model.prior.mass ())) =
      ↑(-Real.log (tickEvidence model tick)) := by
  apply vfe_posterior_eq
  · exact fun state => model.observation.nonnegative state tick.observed
  · exact model.prior.nonnegative ()
  · exact kernel_sum model.prior ()
  · exact positive

theorem evaluateTicks_computed_eq_sum_surprisal {Key S : Type*} [Fintype S]
    (model : Model Key S) (history : List (RetainedTick Key)) (value : ℝ)
    (carried : List (RetainedTick Key)) (window : Nat)
    (computed : evaluateTicks model history = .computed value carried window) :
    value = (history.map fun tick => -Real.log (tickEvidence model tick)).sum := by
  induction history generalizing value carried window with
  | nil =>
      simp [evaluateTicks] at computed
      exact computed.1.symm
  | cons tick rest ih =>
      simp only [evaluateTicks] at computed
      split at computed
      · contradiction
      · rename_i hpositive
        split at computed
        · rename_i restValue restHistory restWindow hrest
          obtain ⟨rfl, rfl, rfl⟩ := computed
          simp [ih restValue restHistory restWindow hrest]
        · contradiction

/-! A deterministic two-policy example.  Policy `false` has one retained
class observation with evidence `1/2`; policy `true` has no matching history.
The first therefore has F = log 2 while the second has computed empty-history
F = 0. -/

def exampleObservation : ProbabilityKernel Bool EndingClass :=
  finiteKernel (fun state ending =>
    if ending = (if state then .focused else .related) then 1 else 0)
    (by intros; split_ifs <;> norm_num)
    (by
      intro state
      cases state <;>
        rw [show (Finset.univ : Finset EndingClass) =
          {.focused, .related, .unrelated, .stopTheLine, .notYetEvaluated} by decide] <;>
        simp)

def examplePrior : ProbabilityKernel Unit Bool :=
  finiteKernel (fun _ _ => 1 / 2) (by intros; norm_num)
    (by intro; rw [show (Finset.univ : Finset Bool) = {false, true} by decide]; norm_num)

def exampleModel (key : Bool) : Model Bool Bool :=
  ⟨key, examplePrior, exampleObservation⟩

def exampleTick : RetainedTick Bool := ⟨false, "run-surprising", .focused⟩

theorem example_tick_evidence : tickEvidence (exampleModel false) exampleTick = 1 / 2 := by
  norm_num [tickEvidence, evidence, likelihood, exampleModel, examplePrior,
    exampleObservation, exampleTick, finiteKernel,
    show EndingClass.focused ≠ EndingClass.related by decide]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem two_policy_example :
    evaluate ⟨1⟩ (exampleModel false) [exampleTick] =
        .computed (Real.log 2) [exampleTick] 1 ∧
      evaluate ⟨1⟩ (exampleModel true) [exampleTick] = .computed 0 [] 1 ∧
      (Real.log 1 - Real.log 2 - 0 / 1) < (Real.log 1 - 0 - 0 / 1) := by
  constructor
  · unfold evaluate
    norm_num [selectedHistory, exampleTick, exampleModel, evaluateTicks, tickEvidence,
      evidence, likelihood, examplePrior, exampleObservation, finiteKernel,
      show EndingClass.focused ≠ EndingClass.related by decide,
      Real.log_div, Real.log_one]
  · constructor
    · norm_num [evaluate, selectedHistory, evaluateTicks, exampleModel, exampleTick]
    · simp only [Real.log_one, zero_sub, zero_div, sub_zero]
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

#print axioms mem_selectedHistory_key
#print axioms evaluate_empty
#print axioms zero_evidence_tick_impossible
#print axioms exact_tick_vfe_eq_surprisal
#print axioms evaluateTicks_computed_eq_sum_surprisal
#print axioms two_policy_example

end
end DarkTower.WarMachine.ReadingPolicyClassFreeEnergy
