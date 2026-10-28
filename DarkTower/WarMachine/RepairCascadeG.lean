import DarkTower.WarMachine.CascadeEFE
import DarkTower.WarMachine.PatternThetaNovelty
import Mathlib.Tactic

/-!
# G for repair cascades

Criterion S3 of `E-self-heal-cascade.md`: repair cascades use the same
finite-cascade expected-free-energy expression as other policies.  This file
adds only the repair patterns, the META outcome vocabulary, and a small model;
the score below is always written as `CascadeEFE.stepG ... -
PatternThetaNovelty.novelty ...`.
-/

namespace DarkTower.WarMachine.RepairCascadeG

open scoped BigOperators
open CascadeEFE
open Holes
noncomputable section

/-- The fourteen pattern ids in `futon3/library/self-heal/*.flexiarg`. -/
inductive RepairPattern
  | correctRefusalIsNotDefect
  | differentSeatReviews
  | noOpIsObservation
  | redBeforeRepair
  | introducePattern
  | locateProducer
  | matchFinding
  | recordFinding
  | repairProducer
  | reproduceRetained
  | retireLedger
  | retryRepairedPhase
  | takeInUnpredicted
  | witnessPath
  deriving DecidableEq, Repr

/-- Exact file-stem identity of each self-heal library pattern. -/
def RepairPattern.id : RepairPattern → String
  | .correctRefusalIsNotDefect => "a-correct-refusal-is-not-the-defect"
  | .differentSeatReviews => "a-different-seat-reviews"
  | .noOpIsObservation => "a-step-that-did-nothing-is-an-observation"
  | .redBeforeRepair => "fix-the-red-before-the-repair"
  | .introducePattern => "introduce-the-pattern-from-the-repair"
  | .locateProducer => "locate-the-producer-first"
  | .matchFinding => "match-the-finding-against-the-library"
  | .recordFinding => "record-the-finding-with-its-target"
  | .repairProducer => "repair-the-producer-not-the-checker"
  | .reproduceRetained => "reproduce-on-retained-inputs"
  | .retireLedger => "retire-by-appending-to-the-ledger"
  | .retryRepairedPhase => "retry-only-the-repaired-phase"
  | .takeInUnpredicted => "take-in-what-no-step-predicted"
  | .witnessPath => "witness-the-path-not-the-helper"

/-- A repair policy is a cascade of the admitted self-heal pattern ids. -/
abbrev RepairCascade := List RepairPattern

/-- Cascade 1, the genuine-repair route in the self-heal library record. -/
def genuineRepair : RepairCascade :=
  [.recordFinding, .locateProducer, .reproduceRetained,
   .correctRefusalIsNotDefect, .redBeforeRepair, .repairProducer,
   .witnessPath, .differentSeatReviews, .retireLedger]

/-- Cascade 3, the historical-misclassification correction route. -/
def historicalMisclassification : RepairCascade :=
  [.reproduceRetained, .correctRefusalIsNotDefect, .retireLedger]

/-- Exactly the outcome vocabulary of META's `meta-outer-policy-cascade.edn`. -/
inductive MetaOutcome
  | closure
  | groundedProgress
  | usefulBlockerDiscovery
  | downstreamUnblocking
  | informationGain
  | elapsedMs
  | tokenUse
  | repeatedTarget
  | abstention
  | unreviewableOutput
  | injuryPersistence
  deriving DecidableEq, Fintype, Repr

/-- The META preferred outcomes; epistemic outcomes remain distinct. -/
def preferred : MetaOutcome → Bool
  | .closure | .groundedProgress | .downstreamUnblocking => true
  | _ => false

/-- The META explicitly dispreferred outcomes. -/
def dispreferred : MetaOutcome → Bool
  | .elapsedMs | .tokenUse | .repeatedTarget | .abstention
  | .unreviewableOutput | .injuryPersistence => true
  | _ => false

/-- Whether the refusing check reports a real defect or a historical non-defect. -/
inductive InjuryState | realDefect | neverDefect
  deriving DecidableEq, Fintype, Repr

/-- The one reproduction observation on which the example updates its belief. -/
inductive ReproductionResult | checkCorrect | historicalMisclassification
  deriving DecidableEq, Repr

/-- Reproduction resolves the example's two-state hypothesis. -/
def reproductionBelief : ReproductionResult → ProbabilityKernel Unit InjuryState
  | .checkCorrect => point .realDefect
  | .historicalMisclassification => point .neverDefect

/-- The two repair cascades offered to the ordinary argmin. -/
inductive RepairPolicy | genuine | historical
  deriving DecidableEq, Repr

/-- Cascades are data attached to the two policies, not a fixed execution pipeline. -/
def RepairPolicy.cascade : RepairPolicy → RepairCascade
  | .genuine => genuineRepair
  | .historical => historicalMisclassification

/-- Predicted META outcome for each policy and hidden injury state. -/
def predictedOutcome : RepairPolicy → InjuryState → MetaOutcome
  | .genuine, .realDefect => .closure
  | .genuine, .neverDefect => .injuryPersistence
  | .historical, .realDefect => .injuryPersistence
  | .historical, .neverDefect => .closure

/-- Deterministic predicted outcome kernel for the example repair model. -/
def predictedKernel (p : RepairPolicy) : ProbabilityKernel InjuryState MetaOutcome :=
  finiteKernel (fun s o => if o = predictedOutcome p s then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro; simp)

/-- META preference weights: preferred outcomes get four units, explicitly
dispreferred outcomes one, and the two epistemic outcomes two. -/
def preferenceWeight (o : MetaOutcome) : ℚ :=
  if preferred o then 4 else if dispreferred o then 1 else 2

theorem preferenceWeight_sum_rat : ∑ o, preferenceWeight o = 22 := by
  rw [show (Finset.univ : Finset MetaOutcome) =
      {.closure, .groundedProgress, .usefulBlockerDiscovery, .downstreamUnblocking,
       .informationGain, .elapsedMs, .tokenUse, .repeatedTarget, .abstention,
       .unreviewableOutput, .injuryPersistence} by
        ext o
        fin_cases o <;> simp]
  repeat' rw [Finset.sum_insert (by decide)]
  norm_num [preferenceWeight, preferred, dispreferred]

theorem preferenceWeight_sum : ∑ o, (preferenceWeight o : ℝ) = 22 := by
  exact_mod_cast preferenceWeight_sum_rat

/-- Normalised META preference kernel used by the repair example. -/
def metaPreference : ProbabilityKernel Unit MetaOutcome :=
  finiteKernel (fun _ o => (preferenceWeight o : ℝ) / 22)
    (by intro _ o; fin_cases o <;> norm_num [preferenceWeight, preferred, dispreferred])
    (by intro; rw [← Finset.sum_div, preferenceWeight_sum]; norm_num)

theorem metaPreference_positive (o : MetaOutcome) : 0 < metaPreference.mass () o := by
  fin_cases o <;> norm_num [metaPreference, preferenceWeight, preferred, dispreferred,
    finiteKernel]

theorem repairRiskAdmissible (r : ReproductionResult) (p : RepairPolicy) :
    PreferenceRiskSeparation.riskAdmissible
      (push (reproductionBelief r) (predictedKernel p)) metaPreference := by
  intro _ o _ _
  exact metaPreference_positive o

/-- The epistemic subtraction is genuinely present for the example counts. -/
theorem genuineRepair_novelty_nonzero : PatternThetaNovelty.novelty 1 1 ≠ 0 := by
  rw [PatternThetaNovelty.novelty_eq 1 1 (by norm_num) (by norm_num)]
  norm_num

theorem stepG_point_repair (s : InjuryState) (p : RepairPolicy)
    (h : PreferenceRiskSeparation.riskAdmissible
      (push (point s) (predictedKernel p)) metaPreference) :
    stepG (point s) (predictedKernel p) metaPreference h =
      -Real.log (metaPreference.mass () (predictedOutcome p s)) := by
  have hpush : ∀ o, (push (point s) (predictedKernel p)).mass () o =
      if o = predictedOutcome p s then 1 else 0 := by
    intro o
    simp only [CascadeEFE.push, CascadeEFE.point, CascadeEFE.finiteKernel,
      predictedKernel, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single s]
    · simp
    · intro x _ hx; simp [hx]
    · simp
  have hamb : CascadeEFE.ambiguity (point s) (predictedKernel p) = 0 := by
    simp only [CascadeEFE.ambiguity, CascadeEFE.point, CascadeEFE.finiteKernel,
      ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single s]
    · simp only [CascadeEFE.entropy, predictedKernel, CascadeEFE.finiteKernel]
      simp [Finset.sum_ite_eq']
    · intro x _ hx; simp [hx]
    · simp
  simp only [CascadeEFE.stepG, CascadeEFE.risk, hamb, add_zero, hpush]
  rw [Finset.sum_eq_single (predictedOutcome p s)]
  · simp [CascadeEFE.klTerm]
  · intro o _ ho; simp [ho, CascadeEFE.klTerm]
  · simp

/-- Reproduction that confirms a defect makes the genuine repair cascade cheaper. -/
theorem checkCorrect_prefers_genuine :
    stepG (reproductionBelief .checkCorrect) (predictedKernel .genuine) metaPreference
        (repairRiskAdmissible .checkCorrect .genuine) - PatternThetaNovelty.novelty 1 1 <
    stepG (reproductionBelief .checkCorrect) (predictedKernel .historical) metaPreference
        (repairRiskAdmissible .checkCorrect .historical) - PatternThetaNovelty.novelty 1 1 := by
  change stepG (point .realDefect) (predictedKernel .genuine) metaPreference _ - _ <
    stepG (point .realDefect) (predictedKernel .historical) metaPreference _ - _
  rw [stepG_point_repair, stepG_point_repair]
  norm_num [predictedOutcome, metaPreference, preferenceWeight, preferred, dispreferred,
    CascadeEFE.finiteKernel]
  exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

/-- Reproduction that identifies a historical non-defect reverses the ordering. -/
theorem historicalMisclassification_prefers_historical :
    stepG (reproductionBelief .historicalMisclassification) (predictedKernel .historical)
        metaPreference (repairRiskAdmissible .historicalMisclassification .historical) -
        PatternThetaNovelty.novelty 1 1 <
    stepG (reproductionBelief .historicalMisclassification) (predictedKernel .genuine)
        metaPreference (repairRiskAdmissible .historicalMisclassification .genuine) -
        PatternThetaNovelty.novelty 1 1 := by
  change stepG (point .neverDefect) (predictedKernel .historical) metaPreference _ - _ <
    stepG (point .neverDefect) (predictedKernel .genuine) metaPreference _ - _
  rw [stepG_point_repair, stepG_point_repair]
  norm_num [predictedOutcome, metaPreference, preferenceWeight, preferred, dispreferred,
    CascadeEFE.finiteKernel]
  exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

/-- The ordinary argmin flips after the reproduction result; no special repair
selector or fixed repair pipeline is introduced. -/
theorem reproduction_flips_argmin :
    ([RepairPolicy.genuine, .historical].argmin (fun p =>
      stepG (reproductionBelief .checkCorrect) (predictedKernel p) metaPreference
        (repairRiskAdmissible .checkCorrect p) - PatternThetaNovelty.novelty 1 1) =
        some .genuine) ∧
    ([RepairPolicy.genuine, .historical].argmin (fun p =>
      stepG (reproductionBelief .historicalMisclassification) (predictedKernel p)
        metaPreference (repairRiskAdmissible .historicalMisclassification p) -
        PatternThetaNovelty.novelty 1 1) = some .historical) := by
  constructor
  · have h := checkCorrect_prefers_genuine
    simp [List.argmin, List.argAux, not_lt_of_ge (le_of_lt h)]
  · have h := historicalMisclassification_prefers_historical
    simp [List.argmin, List.argAux, h]

end
end DarkTower.WarMachine.RepairCascadeG
