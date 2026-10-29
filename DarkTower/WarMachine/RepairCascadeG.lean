import DarkTower.WarMachine.CascadeEFE
import DarkTower.WarMachine.PatternThetaNovelty
import Mathlib.Tactic

/-! Repair cascades use the existing finite-cascade G. Patterns are interpreted
in precedence order; `CascadeEFE.stepG` is used directly and admitted pattern
novelty is subtracted at selection sites. There is no repair-specific scorer.

The summed per-pattern novelty grows with the number of admitted patterns. It
can therefore reward a full repair cascade even after reproduction establishes
that the injury was never a defect. The exact threshold below records this
property of applying the existing novelty term here; S4 must account for it.
-/

namespace DarkTower.WarMachine.RepairCascadeG
open scoped BigOperators
open DarkTower.WarMachine.Holes DarkTower.WarMachine.CascadeEFE
noncomputable section
set_option maxHeartbeats 800000

/-- The fourteen ids in `futon3/library/self-heal/*.flexiarg`. -/
inductive RepairPattern
  | correctRefusalIsNotDefect | differentSeatReviews | noOpIsObservation
  | redBeforeRepair | introducePattern | locateProducer | matchFinding
  | recordFinding | repairProducer | reproduceRetained | retireLedger
  | retryRepairedPhase | takeInUnpredicted | witnessPath
  deriving DecidableEq, Repr

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

abbrev RepairCascade := List RepairPattern

def genuineRepair : RepairCascade :=
  [.recordFinding, .locateProducer, .reproduceRetained,
   .correctRefusalIsNotDefect, .redBeforeRepair, .repairProducer,
   .witnessPath, .differentSeatReviews, .retireLedger]

def historicalMisclassification : RepairCascade :=
  [.reproduceRetained, .correctRefusalIsNotDefect, .retireLedger]

/-- Exactly META's outcome vocabulary. -/
inductive MetaOutcome
  | closure | groundedProgress | usefulBlockerDiscovery | downstreamUnblocking
  | informationGain | elapsedMs | tokenUse | repeatedTarget | abstention
  | unreviewableOutput | injuryPersistence
  deriving DecidableEq, Fintype, Repr

def preferred : MetaOutcome → Bool
  | .closure | .groundedProgress | .downstreamUnblocking => true
  | _ => false

def dispreferred : MetaOutcome → Bool
  | .elapsedMs | .tokenUse | .repeatedTarget | .abstention
  | .unreviewableOutput | .injuryPersistence => true
  | _ => false

inductive InjuryState | realDefect | neverDefect
  deriving DecidableEq, Fintype, Repr

/-- State read and changed by the library patterns' guards and effects. -/
structure RepairState where
  injury : InjuryState
  recorded : Bool := false
  producerLocated : Bool := false
  reproduced : Bool := false
  decisionMade : Bool := false
  redBoundary : Bool := false
  producerFixed : Bool := false
  pathWitnessed : Bool := false
  reviewed : Bool := false
  retired : Bool := false
  deriving DecidableEq, Repr

/-- A scored repair begins from an already-recorded injury entry. -/
def initialRepairState (i : InjuryState) : RepairState := { injury := i, recorded := true }

/-- Guards are the represented portion of each library pattern's `@guard`. -/
def guard : RepairPattern → RepairState → Bool
  | .recordFinding, _ => true
  | .locateProducer, s => s.recorded
  | .reproduceRetained, s => s.recorded
  | .correctRefusalIsNotDefect, s => s.producerLocated && s.reproduced
  | .redBeforeRepair, s => s.reproduced && s.decisionMade
  | .repairProducer, s => s.producerLocated && s.decisionMade && s.redBoundary
  | .witnessPath, s => s.producerFixed
  | .differentSeatReviews, s => s.redBoundary && s.pathWitnessed
  | .retireLedger, s => s.reviewed || (s.reproduced && s.injury == .neverDefect)
  | .noOpIsObservation, _ => true
  | .introducePattern, s => s.reviewed
  | .matchFinding, s => s.recorded
  | .retryRepairedPhase, s => s.reviewed && s.producerFixed
  | .takeInUnpredicted, s => s.recorded

/-- Effects are the represented portion of each library pattern's `@effect`. -/
def effect : RepairPattern → RepairState → RepairState
  | .recordFinding, s => { s with recorded := true }
  | .locateProducer, s => { s with producerLocated := true }
  | .reproduceRetained, s => { s with reproduced := true }
  | .correctRefusalIsNotDefect, s => { s with decisionMade := true }
  | .redBeforeRepair, s => { s with redBoundary := true }
  | .repairProducer, s => { s with producerFixed := true }
  | .witnessPath, s => { s with pathWitnessed := true }
  | .differentSeatReviews, s => { s with reviewed := true }
  | .retireLedger, s => { s with retired := true }
  | _, s => s

def applyPattern (s : RepairState) (p : RepairPattern) : RepairState :=
  if guard p s then effect p s else s

/-- Apply the cascade's guards and effects in list order. -/
def applyCascade (c : RepairCascade) (s : RepairState) : RepairState :=
  c.foldl applyPattern s

def predictedOutcome (s : RepairState) : MetaOutcome :=
  if s.retired && s.injury == .neverDefect && s.producerLocated then .tokenUse
  else if s.retired || (s.producerFixed && s.pathWitnessed) then .closure
  else if s.reproduced && s.decisionMade then .usefulBlockerDiscovery
  else .injuryPersistence

/-- The outcome kernel is computed from the cascade's composition. -/
def predictedKernel (c : RepairCascade) : ProbabilityKernel InjuryState MetaOutcome :=
  finiteKernel (fun i o =>
      if o = predictedOutcome (applyCascade c (initialRepairState i)) then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro; simp)

/-- Learned preference parameter with only META's stated ordering. -/
structure AdmittedPreference where
  kernel : ProbabilityKernel Unit MetaOutcome
  positive : ∀ o, 0 < kernel.mass () o
  preferred_gt_dispreferred : ∀ p d,
    preferred p = true → dispreferred d = true → kernel.mass () d < kernel.mass () p

theorem riskAdmissible (C : AdmittedPreference) (q : ProbabilityKernel Unit InjuryState)
    (c : RepairCascade) :
    PreferenceRiskSeparation.riskAdmissible (push q (predictedKernel c)) C.kernel := by
  intro _ o _ _
  exact C.positive o

abbrev PatternCounts := RepairPattern → ℝ × ℝ

/-- Only admitted (guard-true) patterns contribute their existing novelty term. -/
def cascadeNoveltyFrom (counts : PatternCounts) : RepairState → RepairCascade → ℝ
  | _, [] => 0
  | s, p :: ps =>
      if guard p s then
        PatternThetaNovelty.novelty (counts p).1 (counts p).2 +
          cascadeNoveltyFrom counts (effect p s) ps
      else cascadeNoveltyFrom counts s ps

def cascadeNovelty (counts : PatternCounts) (i : InjuryState) (c : RepairCascade) : ℝ :=
  cascadeNoveltyFrom counts (initialRepairState i) c

/-- Existing `stepG` at the cascade-computed point outcome. -/
theorem stepG_point_repair (C : AdmittedPreference) (i : InjuryState)
    (c : RepairCascade) :
    stepG (point i) (predictedKernel c) C.kernel (riskAdmissible C (point i) c) =
      -Real.log (C.kernel.mass ()
        (predictedOutcome (applyCascade c (initialRepairState i)))) := by
  let out := predictedOutcome (applyCascade c (initialRepairState i))
  have hpush : ∀ o, (push (point i) (predictedKernel c)).mass () o =
      if o = out then 1 else 0 := by
    intro o
    simp only [push, point, finiteKernel, predictedKernel, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp [out]
    · intro x _ hx; simp [hx]
    · simp
  have hamb : CascadeEFE.ambiguity (point i) (predictedKernel c) = 0 := by
    simp only [CascadeEFE.ambiguity, point, finiteKernel, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single i]
    · simp only [entropy, predictedKernel, finiteKernel]
      simp [Finset.sum_ite_eq']
    · intro x _ hx; simp [hx]
    · simp
  simp only [stepG, risk, hamb, add_zero, hpush]
  rw [Finset.sum_eq_single out]
  · simp [klTerm, out]
  · intro o _ ho; simp [ho, klTerm]
  · simp

/-- Same patterns, but repair is attempted before reproduction enables the
decision and red-boundary guards. -/
def fixThenReproduce : RepairCascade :=
  [.recordFinding, .locateProducer, .correctRefusalIsNotDefect, .redBeforeRepair,
   .repairProducer, .reproduceRetained, .witnessPath]

/-- The same bag in the order required by its guards. -/
def reproduceThenFix : RepairCascade :=
  [.recordFinding, .locateProducer, .reproduceRetained, .correctRefusalIsNotDefect,
   .redBeforeRepair, .repairProducer, .witnessPath]

set_option maxHeartbeats 800000 in
theorem order_changes_prediction :
    predictedOutcome (applyCascade reproduceThenFix (initialRepairState .realDefect)) = .closure ∧
    predictedOutcome (applyCascade fixThenReproduce (initialRepairState .realDefect)) =
      .injuryPersistence := by decide

/-- The two recorded cascades predict opposite preferred/dispreferred outcomes
after the reproduction result. -/
theorem recorded_cascade_predictions :
    predictedOutcome (applyCascade genuineRepair (initialRepairState .realDefect)) = .closure ∧
    predictedOutcome (applyCascade historicalMisclassification
      (initialRepairState .realDefect)) = .injuryPersistence ∧
    predictedOutcome (applyCascade genuineRepair (initialRepairState .neverDefect)) = .tokenUse ∧
    predictedOutcome (applyCascade historicalMisclassification
      (initialRepairState .neverDefect)) = .closure := by decide

/-- G is not composition-blind: the same two patterns in a different order
produce different G whenever learned C prefers closure to injury persistence. -/
theorem G_reads_composition (C : AdmittedPreference) :
    stepG (point .realDefect) (predictedKernel reproduceThenFix) C.kernel
        (riskAdmissible C (point .realDefect) reproduceThenFix) <
    stepG (point .realDefect) (predictedKernel fixThenReproduce) C.kernel
        (riskAdmissible C (point .realDefect) fixThenReproduce) := by
  rw [stepG_point_repair, stepG_point_repair]
  simp only [order_changes_prediction]
  have h := C.preferred_gt_dispreferred .closure .injuryPersistence (by rfl) (by rfl)
  exact neg_lt_neg (Real.strictMonoOn_log (C.positive _) (C.positive _) h)

/-- Reproduction-first enables the repair pattern and therefore contributes
its per-pattern novelty; repair-first does not. -/
theorem reproduce_first_larger_novelty (counts : PatternCounts) (i : InjuryState)
    (hpos : ∀ p, 0 < (counts p).1 ∧ 0 < (counts p).2) :
    cascadeNovelty counts i fixThenReproduce <
      cascadeNovelty counts i reproduceThenFix := by
  simp [cascadeNovelty, cascadeNoveltyFrom, fixThenReproduce, reproduceThenFix,
    initialRepairState,
    guard, effect]
  rw [PatternThetaNovelty.novelty_eq _ _ (hpos .repairProducer).1
    (hpos .repairProducer).2]
  have hdecision := PatternThetaNovelty.novelty_nonneg
    (counts .correctRefusalIsNotDefect).1 (counts .correctRefusalIsNotDefect).2
    (hpos _).1 (hpos _).2
  have hred := PatternThetaNovelty.novelty_nonneg
    (counts .redBeforeRepair).1 (counts .redBeforeRepair).2 (hpos _).1 (hpos _).2
  have hwitness := PatternThetaNovelty.novelty_nonneg
    (counts .witnessPath).1 (counts .witnessPath).2 (hpos _).1 (hpos _).2
  have ha := (hpos .repairProducer).1
  have hb := (hpos .repairProducer).2
  have hden : 0 < 2 * ((counts .repairProducer).1 + (counts .repairProducer).2) := by
    nlinarith
  positivity

/-- Before reproduction, belief remains non-point over the injury state. -/
def beforeReproduction : ProbabilityKernel Unit InjuryState :=
  finiteKernel (fun _ _ => 1 / 2) (by intros; norm_num)
    (by intro
        rw [show (Finset.univ : Finset InjuryState) = {.realDefect, .neverDefect} by
          ext i; fin_cases i <;> simp]
        rw [Finset.sum_insert (by decide)]
        norm_num)

/-- Expected existing pattern novelty under a hidden-state belief. -/
def expectedCascadeNovelty (q : ProbabilityKernel Unit InjuryState)
    (counts : PatternCounts) (c : RepairCascade) : ℝ :=
  ∑ i, q.mass () i * cascadeNovelty counts i c

/-- With the non-point pre-reproduction belief, putting reproduction first
admits strictly more epistemic value. -/
theorem before_reproduction_prefers_epistemic_order (counts : PatternCounts)
    (hpos : ∀ p, 0 < (counts p).1 ∧ 0 < (counts p).2) :
    expectedCascadeNovelty beforeReproduction counts fixThenReproduce <
      expectedCascadeNovelty beforeReproduction counts reproduceThenFix := by
  have hr := reproduce_first_larger_novelty counts .realDefect hpos
  have hn := reproduce_first_larger_novelty counts .neverDefect hpos
  unfold expectedCascadeNovelty beforeReproduction
  simp only [finiteKernel]
  rw [show (Finset.univ : Finset InjuryState) = {.realDefect, .neverDefect} by
    ext i; fin_cases i <;> simp]
  repeat' rw [Finset.sum_insert (by decide)]
  simp
  linarith

/-- The complete existing G expression (`stepG - novelty`) distinguishes the
same pattern bag in different orders. -/
theorem existing_G_reads_composition (C : AdmittedPreference) (counts : PatternCounts)
    (hpos : ∀ p, 0 < (counts p).1 ∧ 0 < (counts p).2) :
    stepG (point .realDefect) (predictedKernel reproduceThenFix) C.kernel
        (riskAdmissible C (point .realDefect) reproduceThenFix) -
        cascadeNovelty counts .realDefect reproduceThenFix <
    stepG (point .realDefect) (predictedKernel fixThenReproduce) C.kernel
        (riskAdmissible C (point .realDefect) fixThenReproduce) -
        cascadeNovelty counts .realDefect fixThenReproduce := by
  have hG := G_reads_composition C
  have hn := reproduce_first_larger_novelty counts .realDefect hpos
  linarith

/-- The pragmatic `stepG` part alone prefers genuine repair for a real defect. -/
theorem realDefect_risk_prefers_genuine (C : AdmittedPreference) :
    stepG (point .realDefect) (predictedKernel genuineRepair) C.kernel
        (riskAdmissible C (point .realDefect) genuineRepair) <
    stepG (point .realDefect) (predictedKernel historicalMisclassification) C.kernel
        (riskAdmissible C (point .realDefect) historicalMisclassification) := by
  rw [stepG_point_repair, stepG_point_repair]
  simp only [recorded_cascade_predictions]
  have h := C.preferred_gt_dispreferred .closure .injuryPersistence (by rfl) (by rfl)
  exact neg_lt_neg (Real.strictMonoOn_log (C.positive _) (C.positive _) h)

/-- The pragmatic `stepG` part alone prefers historical correction when the
injury was never a defect. -/
theorem neverDefect_risk_prefers_historical (C : AdmittedPreference) :
    stepG (point .neverDefect) (predictedKernel historicalMisclassification) C.kernel
        (riskAdmissible C (point .neverDefect) historicalMisclassification) <
    stepG (point .neverDefect) (predictedKernel genuineRepair) C.kernel
        (riskAdmissible C (point .neverDefect) genuineRepair) := by
  rw [stepG_point_repair, stepG_point_repair]
  simp only [recorded_cascade_predictions]
  have h := C.preferred_gt_dispreferred .closure .tokenUse (by rfl) (by rfl)
  exact neg_lt_neg (Real.strictMonoOn_log (C.positive _) (C.positive _) h)

/-- Exact condition under which novelty does not reverse the never-defect risk
ordering. -/
theorem neverDefect_flip_survives_iff (C : AdmittedPreference) (counts : PatternCounts) :
    (stepG (point .neverDefect) (predictedKernel historicalMisclassification) C.kernel
          (riskAdmissible C (point .neverDefect) historicalMisclassification) -
          cascadeNovelty counts .neverDefect historicalMisclassification <
      stepG (point .neverDefect) (predictedKernel genuineRepair) C.kernel
          (riskAdmissible C (point .neverDefect) genuineRepair) -
          cascadeNovelty counts .neverDefect genuineRepair) ↔
    cascadeNovelty counts .neverDefect genuineRepair -
        cascadeNovelty counts .neverDefect historicalMisclassification <
      stepG (point .neverDefect) (predictedKernel genuineRepair) C.kernel
          (riskAdmissible C (point .neverDefect) genuineRepair) -
        stepG (point .neverDefect) (predictedKernel historicalMisclassification) C.kernel
          (riskAdmissible C (point .neverDefect) historicalMisclassification) := by
  constructor <;> intro h <;> linarith

/-- If novelty exceeds that risk gap, the full genuine-repair cascade wins on
a never-defect injury. -/
theorem excessive_novelty_prefers_genuine (C : AdmittedPreference) (counts : PatternCounts)
    (h :
      stepG (point .neverDefect) (predictedKernel genuineRepair) C.kernel
          (riskAdmissible C (point .neverDefect) genuineRepair) -
        stepG (point .neverDefect) (predictedKernel historicalMisclassification) C.kernel
          (riskAdmissible C (point .neverDefect) historicalMisclassification) <
      cascadeNovelty counts .neverDefect genuineRepair -
        cascadeNovelty counts .neverDefect historicalMisclassification) :
    stepG (point .neverDefect) (predictedKernel genuineRepair) C.kernel
          (riskAdmissible C (point .neverDefect) genuineRepair) -
          cascadeNovelty counts .neverDefect genuineRepair <
      stepG (point .neverDefect) (predictedKernel historicalMisclassification) C.kernel
          (riskAdmissible C (point .neverDefect) historicalMisclassification) -
          cascadeNovelty counts .neverDefect historicalMisclassification := by
  linarith

/-- A concrete learned C used only to witness that the threshold is inhabited. -/
def exampleWeight (o : MetaOutcome) : ℚ :=
  if preferred o then 4 else if dispreferred o then 1 else 2

theorem exampleWeight_sum_rat : ∑ o, exampleWeight o = 22 := by
  rw [show (Finset.univ : Finset MetaOutcome) =
      {.closure, .groundedProgress, .usefulBlockerDiscovery, .downstreamUnblocking,
       .informationGain, .elapsedMs, .tokenUse, .repeatedTarget, .abstention,
       .unreviewableOutput, .injuryPersistence} by
        ext o; fin_cases o <;> simp]
  repeat' rw [Finset.sum_insert (by decide)]
  norm_num [exampleWeight, preferred, dispreferred]

def examplePreferenceKernel : ProbabilityKernel Unit MetaOutcome :=
  finiteKernel (fun _ o => (exampleWeight o : ℝ) / 22)
    (by intro _ o; fin_cases o <;> norm_num [exampleWeight, preferred, dispreferred])
    (by intro
        rw [← Finset.sum_div]
        norm_num [show ∑ o, (exampleWeight o : ℝ) = 22 by exact_mod_cast exampleWeight_sum_rat])

def examplePreference : AdmittedPreference where
  kernel := examplePreferenceKernel
  positive := by
    intro o; fin_cases o <;>
      norm_num [examplePreferenceKernel, finiteKernel, exampleWeight, preferred, dispreferred]
  preferred_gt_dispreferred := by
    intro p d hp hd
    fin_cases p <;> fin_cases d <;>
      simp_all [examplePreferenceKernel, finiteKernel, exampleWeight, preferred, dispreferred]
    all_goals norm_num

def exampleRiskGap : ℝ :=
  stepG (point .neverDefect) (predictedKernel genuineRepair) examplePreference.kernel
      (riskAdmissible examplePreference (point .neverDefect) genuineRepair) -
    stepG (point .neverDefect) (predictedKernel historicalMisclassification)
      examplePreference.kernel
      (riskAdmissible examplePreference (point .neverDefect) historicalMisclassification)

theorem exampleRiskGap_pos : 0 < exampleRiskGap := by
  unfold exampleRiskGap
  exact sub_pos.mpr (neverDefect_risk_prefers_historical examplePreference)

/-- Concrete positive counts, scaled by the actual learned-C risk gap. -/
def exampleCounts : PatternCounts := fun _ => (100 / exampleRiskGap, 100 / exampleRiskGap)

theorem exampleCounts_pos (p : RepairPattern) :
    0 < (exampleCounts p).1 ∧ 0 < (exampleCounts p).2 := by
  constructor <;> exact div_pos (by norm_num) exampleRiskGap_pos

/-- The concrete C and counts lie strictly below the novelty threshold. -/
theorem example_flip_survives :
    cascadeNovelty exampleCounts .neverDefect genuineRepair -
        cascadeNovelty exampleCounts .neverDefect historicalMisclassification < exampleRiskGap := by
  simp [cascadeNovelty, cascadeNoveltyFrom, genuineRepair, historicalMisclassification,
    initialRepairState, guard, effect, exampleCounts]
  have hg := exampleRiskGap_pos
  have hn := PatternThetaNovelty.novelty_eq (100 / exampleRiskGap)
    (100 / exampleRiskGap) (div_pos (by norm_num) hg) (div_pos (by norm_num) hg)
  rw [hn]
  field_simp
  nlinarith

theorem realDefect_genuine_has_more_novelty (counts : PatternCounts)
    (hpos : ∀ p, 0 < (counts p).1 ∧ 0 < (counts p).2) :
    cascadeNovelty counts .realDefect historicalMisclassification <
      cascadeNovelty counts .realDefect genuineRepair := by
  simp [cascadeNovelty, cascadeNoveltyFrom, genuineRepair, historicalMisclassification,
    initialRepairState, guard, effect]
  have hn (p) := PatternThetaNovelty.novelty_nonneg (counts p).1 (counts p).2
    (hpos p).1 (hpos p).2
  rw [PatternThetaNovelty.novelty_eq _ _ (hpos .recordFinding).1
    (hpos .recordFinding).2]
  have hden : 0 < 2 * ((counts .recordFinding).1 + (counts .recordFinding).2) := by
    nlinarith [(hpos .recordFinding).1, (hpos .recordFinding).2]
  have hrecord : 0 < 1 / (2 * ((counts .recordFinding).1 +
      (counts .recordFinding).2)) := one_div_pos.mpr hden
  nlinarith [hn .locateProducer, hn .correctRefusalIsNotDefect,
    hn .redBeforeRepair, hn .repairProducer, hn .witnessPath,
    hn .differentSeatReviews, hn .retireLedger]

/-- After either reproduction result, the ordinary argmin flips exactly while
the never-defect novelty difference remains below its pragmatic risk gap. -/
theorem reproduction_flips_argmin (C : AdmittedPreference) (counts : PatternCounts)
    (hpos : ∀ p, 0 < (counts p).1 ∧ 0 < (counts p).2)
    (hthreshold :
      cascadeNovelty counts .neverDefect genuineRepair -
          cascadeNovelty counts .neverDefect historicalMisclassification <
        stepG (point .neverDefect) (predictedKernel genuineRepair) C.kernel
            (riskAdmissible C (point .neverDefect) genuineRepair) -
          stepG (point .neverDefect) (predictedKernel historicalMisclassification) C.kernel
            (riskAdmissible C (point .neverDefect) historicalMisclassification)) :
    ([genuineRepair, historicalMisclassification].argmin (fun c =>
      stepG (point .realDefect) (predictedKernel c) C.kernel
        (riskAdmissible C (point .realDefect) c) - cascadeNovelty counts .realDefect c) =
        some genuineRepair) ∧
    ([genuineRepair, historicalMisclassification].argmin (fun c =>
      stepG (point .neverDefect) (predictedKernel c) C.kernel
        (riskAdmissible C (point .neverDefect) c) - cascadeNovelty counts .neverDefect c) =
        some historicalMisclassification) := by
  have hrisk := realDefect_risk_prefers_genuine C
  have hnovelty := realDefect_genuine_has_more_novelty counts hpos
  have hreal :
      stepG (point .realDefect) (predictedKernel genuineRepair) C.kernel
          (riskAdmissible C (point .realDefect) genuineRepair) -
          cascadeNovelty counts .realDefect genuineRepair <
      stepG (point .realDefect) (predictedKernel historicalMisclassification) C.kernel
          (riskAdmissible C (point .realDefect) historicalMisclassification) -
          cascadeNovelty counts .realDefect historicalMisclassification := by linarith
  have hhistorical := (neverDefect_flip_survives_iff C counts).2 hthreshold
  constructor
  · simp [List.argmin, List.argAux, not_lt_of_ge (le_of_lt hreal)]
  · simp [List.argmin, List.argAux, hhistorical]

end
end DarkTower.WarMachine.RepairCascadeG
