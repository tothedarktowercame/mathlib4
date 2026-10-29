import DarkTower.WarMachine.CascadeEFE
import DarkTower.WarMachine.PatternThetaNovelty
import Mathlib.Tactic

/-! Repair cascades use the existing finite-cascade G. Patterns are interpreted
in precedence order and admitted pattern novelty is subtracted at selection
sites. A bounded cost model now assigns `w` token-use mass per admitted step
and the remaining mass to the cascade's terminal outcome. This removes the old
terminal token-use special case and makes the length bias an explicit part of
the predictive model rather than an outcome-label workaround.
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
  | .redBeforeRepair, s => s.reproduced && s.decisionMade && s.injury == .realDefect
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
  if s.retired || (s.producerFixed && s.pathWitnessed) then .closure
  else if s.reproduced && s.decisionMade then .usefulBlockerDiscovery
  else .injuryPersistence

def admittedCountFrom : RepairState → RepairCascade → ℕ
  | _, [] => 0
  | s, p :: ps =>
      if guard p s then 1 + admittedCountFrom (effect p s) ps
      else admittedCountFrom s ps

def admittedCount (i : InjuryState) (c : RepairCascade) : ℕ :=
  admittedCountFrom (initialRepairState i) c

/-- The guard facts used below. The historical cascade has only two admitted
steps: its decision guard requires a producer location that it does not contain. -/
theorem recorded_cascade_guard_check :
    admittedCount .neverDefect genuineRepair = 5 ∧
    admittedCount .neverDefect historicalMisclassification = 2 ∧
    predictedOutcome (applyCascade genuineRepair (initialRepairState .neverDefect)) = .closure ∧
    predictedOutcome (applyCascade historicalMisclassification
      (initialRepairState .neverDefect)) = .closure ∧
    predictedOutcome (applyCascade genuineRepair (initialRepairState .realDefect)) = .closure ∧
    predictedOutcome (applyCascade historicalMisclassification
      (initialRepairState .realDefect)) = .injuryPersistence := by decide

/-- Cost parameters are bounded so every permitted cascade leaves nonnegative
mass for its terminal outcome. -/
structure CostModel where
  maxLength : ℕ
  w : ℝ
  w_nonneg : 0 ≤ w
  total_le_one : w * maxLength ≤ 1

structure BoundedCascade (m : CostModel) where
  patterns : RepairCascade
  length_le : patterns.length ≤ m.maxLength

theorem admittedCount_le_length (s : RepairState) (c : RepairCascade) :
    admittedCountFrom s c ≤ c.length := by
  induction c generalizing s with
  | nil => simp [admittedCountFrom]
  | cons p ps ih =>
      simp only [admittedCountFrom, List.length_cons]
      split
      · have h := ih (effect p s); omega
      · have h := ih s; omega

theorem predictedOutcome_ne_tokenUse (s : RepairState) :
    predictedOutcome s ≠ .tokenUse := by
  unfold predictedOutcome
  split_ifs <;> decide

def costMass (m : CostModel) (c : BoundedCascade m) (i : InjuryState)
    (o : MetaOutcome) : ℝ :=
  if o = .tokenUse then m.w * admittedCount i c.patterns
  else if o = predictedOutcome (applyCascade c.patterns (initialRepairState i)) then
    1 - m.w * admittedCount i c.patterns
  else 0

theorem costMass_nonnegative (m : CostModel) (c : BoundedCascade m)
    (i : InjuryState) (o : MetaOutcome) : 0 ≤ costMass m c i o := by
  have hn : (admittedCount i c.patterns : ℝ) ≤ m.maxLength := by
    exact_mod_cast (le_trans (admittedCount_le_length _ _) c.length_le)
  have hw : m.w * admittedCount i c.patterns ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hn m.w_nonneg) m.total_le_one
  unfold costMass
  split_ifs
  · exact mul_nonneg m.w_nonneg (by positivity)
  · linarith
  · norm_num

/-- Per-step token cost plus the residual terminal mass is a probability kernel. -/
def costKernel (m : CostModel) (c : BoundedCascade m) :
    ProbabilityKernel InjuryState MetaOutcome :=
  finiteKernel (costMass m c) (costMass_nonnegative m c) (by
    intro i
    unfold costMass
    unfold predictedOutcome
    split_ifs <;>
      rw [show (Finset.univ : Finset MetaOutcome) =
        {.closure, .groundedProgress, .usefulBlockerDiscovery, .downstreamUnblocking,
         .informationGain, .elapsedMs, .tokenUse, .repeatedTarget, .abstention,
         .unreviewableOutput, .injuryPersistence} by
          ext o; fin_cases o <;> simp] <;>
      repeat' rw [Finset.sum_insert (by decide)] <;> simp_all <;> ring)

/-! The remaining theorems are stated below after the kernel API. -/

/-- Learned preference parameter with only META's stated ordering. -/
structure AdmittedPreference where
  kernel : ProbabilityKernel Unit MetaOutcome
  positive : ∀ o, 0 < kernel.mass () o
  preferred_gt_dispreferred : ∀ p d,
    preferred p = true → dispreferred d = true → kernel.mass () d < kernel.mass () p

theorem costRiskAdmissible (C : AdmittedPreference) (q : ProbabilityKernel Unit InjuryState)
    (m : CostModel) (c : BoundedCascade m) :
    PreferenceRiskSeparation.riskAdmissible (push q (costKernel m c)) C.kernel := by
  intro _ o _ _
  exact C.positive o

def cascadeG (C : AdmittedPreference) (m : CostModel) (c : BoundedCascade m)
    (i : InjuryState) : ℝ :=
  stepG (point i) (costKernel m c) C.kernel
    (costRiskAdmissible C (point i) m c)

theorem point_information_zero (i : InjuryState) (a : ProbabilityKernel InjuryState MetaOutcome) :
    information (point i) a = 0 := by
  rw [information_entropy_identity]
  have hpush : (push (point i) a).mass () = a.mass i := by
    funext o
    simp [push, point, finiteKernel]
  rw [hpush]
  unfold CascadeEFE.ambiguity
  simp only [point, finiteKernel, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro x _ hx; simp [hx]
  · simp

theorem cascadeG_eq (C : AdmittedPreference) (m : CostModel) (c : BoundedCascade m)
    (i : InjuryState) :
    cascadeG C m c i =
      -(1 - m.w * admittedCount i c.patterns) *
          Real.log (C.kernel.mass ()
            (predictedOutcome (applyCascade c.patterns (initialRepairState i)))) -
        (m.w * admittedCount i c.patterns) * Real.log (C.kernel.mass () .tokenUse) := by
  rw [cascadeG, step_decomposition, point_information_zero, sub_zero]
  have hpush (o : MetaOutcome) :
      (push (point i) (costKernel m c)).mass () o = costMass m c i o := by
    simp [push, point, costKernel, finiteKernel]
  unfold pragmaticCost
  simp_rw [hpush]
  let t := predictedOutcome (applyCascade c.patterns (initialRepairState i))
  let f := fun o : MetaOutcome =>
    if costMass m c i o = 0 then 0
    else costMass m c i o * Real.log (C.kernel.mass () o)
  have hne : t ≠ .tokenUse := predictedOutcome_ne_tokenUse _
  have ht : t ∈ (Finset.univ.erase (.tokenUse : MetaOutcome)) := by simp [hne]
  have ht' : t ∈ (Finset.univ \ {(.tokenUse : MetaOutcome)}) := by simp [hne]
  rw [Finset.sum_eq_add_sum_diff_singleton .tokenUse f (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht' f]
  have hz : ∑ o ∈ (Finset.univ \ {(.tokenUse : MetaOutcome)}) \ {t}, f o = 0 := by
    apply Finset.sum_eq_zero
    intro o ho
    have ho' := Finset.mem_sdiff.mp ho
    have hot : o ≠ .tokenUse := by
      simpa using (Finset.mem_sdiff.mp ho'.1).2
    have hoterm : o ≠ t := by simpa using ho'.2
    simp [f, costMass, hot, hoterm, t]
  rw [hz]
  simp only [add_zero]
  have hzero (p q : ℝ) : (if p = 0 then 0 else p * Real.log q) = p * Real.log q := by
    by_cases hp : p = 0 <;> simp [hp]
  simp only [f, hzero]
  simp [costMass, t, hne]
  ring

def boundedGenuine (m : CostModel) (h : genuineRepair.length ≤ m.maxLength) :
    BoundedCascade m := ⟨genuineRepair, h⟩

def boundedHistorical (m : CostModel) (h : historicalMisclassification.length ≤ m.maxLength) :
    BoundedCascade m := ⟨historicalMisclassification, h⟩

theorem neverDefect_stepG_equal_at_zero (C : AdmittedPreference) (m : CostModel)
    (hg : genuineRepair.length ≤ m.maxLength)
    (hh : historicalMisclassification.length ≤ m.maxLength) (hw : m.w = 0) :
    cascadeG C m (boundedGenuine m hg) .neverDefect =
      cascadeG C m (boundedHistorical m hh) .neverDefect := by
  rw [cascadeG_eq, cascadeG_eq]
  simp [boundedGenuine, boundedHistorical, hw, recorded_cascade_guard_check]

def neverDefectCostGap (C : AdmittedPreference) (m : CostModel)
    (hg : genuineRepair.length ≤ m.maxLength)
    (hh : historicalMisclassification.length ≤ m.maxLength) : ℝ :=
  cascadeG C m (boundedGenuine m hg) .neverDefect -
    cascadeG C m (boundedHistorical m hh) .neverDefect

theorem neverDefect_cost_gap_eq (C : AdmittedPreference) (m : CostModel)
    (hg : genuineRepair.length ≤ m.maxLength)
    (hh : historicalMisclassification.length ≤ m.maxLength) :
    neverDefectCostGap C m hg hh =
      3 * m.w * (Real.log (C.kernel.mass () .closure) -
        Real.log (C.kernel.mass () .tokenUse)) := by
  unfold neverDefectCostGap
  rw [cascadeG_eq, cascadeG_eq]
  simp [boundedGenuine, boundedHistorical, recorded_cascade_guard_check]
  ring

theorem neverDefect_cost_gap_positive (C : AdmittedPreference) (m : CostModel)
    (hg : genuineRepair.length ≤ m.maxLength)
    (hh : historicalMisclassification.length ≤ m.maxLength) (hw : 0 < m.w) :
    0 < neverDefectCostGap C m hg hh := by
  rw [neverDefect_cost_gap_eq]
  have hp := C.preferred_gt_dispreferred .closure .tokenUse (by rfl) (by rfl)
  have hl := Real.strictMonoOn_log (C.positive _) (C.positive _) hp
  positivity

theorem neverDefect_cost_gap_strictMono (C : AdmittedPreference) :
    StrictMono (fun w : ℝ => 3 * w * (Real.log (C.kernel.mass () .closure) -
      Real.log (C.kernel.mass () .tokenUse))) := by
  have hp := C.preferred_gt_dispreferred .closure .tokenUse (by rfl) (by rfl)
  have hl := Real.strictMonoOn_log (C.positive _) (C.positive _) hp
  intro a b hab
  nlinarith

abbrev PatternCounts := RepairPattern → ℝ × ℝ

def cascadeNoveltyFrom (counts : PatternCounts) : RepairState → RepairCascade → ℝ
  | _, [] => 0
  | s, p :: ps =>
      if guard p s then PatternThetaNovelty.novelty (counts p).1 (counts p).2 +
        cascadeNoveltyFrom counts (effect p s) ps
      else cascadeNoveltyFrom counts s ps

def cascadeNovelty (counts : PatternCounts) (i : InjuryState) (c : RepairCascade) : ℝ :=
  cascadeNoveltyFrom counts (initialRepairState i) c

theorem neverDefect_flip_iff (C : AdmittedPreference) (m : CostModel)
    (hg : genuineRepair.length ≤ m.maxLength)
    (hh : historicalMisclassification.length ≤ m.maxLength) (counts : PatternCounts) :
    (cascadeG C m (boundedHistorical m hh) .neverDefect -
          cascadeNovelty counts .neverDefect historicalMisclassification <
        cascadeG C m (boundedGenuine m hg) .neverDefect -
          cascadeNovelty counts .neverDefect genuineRepair) ↔
      cascadeNovelty counts .neverDefect genuineRepair -
          cascadeNovelty counts .neverDefect historicalMisclassification <
        neverDefectCostGap C m hg hh := by
  unfold neverDefectCostGap
  constructor <;> intro h <;> linarith

def fixThenReproduce : RepairCascade :=
  [.recordFinding, .locateProducer, .correctRefusalIsNotDefect, .redBeforeRepair,
   .repairProducer, .reproduceRetained, .witnessPath]

def reproduceThenFix : RepairCascade :=
  [.recordFinding, .locateProducer, .reproduceRetained, .correctRefusalIsNotDefect,
   .redBeforeRepair, .repairProducer, .witnessPath]

theorem order_changes_prediction :
    predictedOutcome (applyCascade reproduceThenFix (initialRepairState .realDefect)) = .closure ∧
    predictedOutcome (applyCascade fixThenReproduce (initialRepairState .realDefect)) =
      .injuryPersistence := by decide

theorem order_changes_G (C : AdmittedPreference) (m : CostModel)
    (hfix : fixThenReproduce.length ≤ m.maxLength)
    (hreproduce : reproduceThenFix.length ≤ m.maxLength) (hw : m.w = 0) :
    cascadeG C m ⟨reproduceThenFix, hreproduce⟩ .realDefect <
      cascadeG C m ⟨fixThenReproduce, hfix⟩ .realDefect := by
  rw [cascadeG_eq, cascadeG_eq]
  simp [hw, order_changes_prediction]
  have hp := C.preferred_gt_dispreferred .closure .injuryPersistence (by rfl) (by rfl)
  have hl := Real.strictMonoOn_log (C.positive _) (C.positive _) hp
  linarith

theorem realDefect_flip_from_preference (C : AdmittedPreference) (m : CostModel)
    (hg : genuineRepair.length ≤ m.maxLength)
    (hh : historicalMisclassification.length ≤ m.maxLength)
    (hw : m.w = 0) :
    cascadeG C m (boundedGenuine m hg) .realDefect <
      cascadeG C m (boundedHistorical m hh) .realDefect := by
  rw [cascadeG_eq, cascadeG_eq]
  simp only [boundedGenuine, boundedHistorical, recorded_cascade_guard_check]
  simp [hw]
  have hp := C.preferred_gt_dispreferred .closure .injuryPersistence (by rfl) (by rfl)
  have hl := Real.strictMonoOn_log (C.positive _) (C.positive _) hp
  linarith

/-- Concrete parameters occur only in this example. -/
def exampleCost : CostModel where
  maxLength := 9
  w := 1 / 10
  w_nonneg := by norm_num
  total_le_one := by norm_num

def exampleWeight (o : MetaOutcome) : ℚ :=
  if preferred o then 4 else if dispreferred o then 1 else 2

theorem exampleWeight_sum : ∑ o, exampleWeight o = 22 := by
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
        norm_num [show ∑ o, (exampleWeight o : ℝ) = 22 by
          exact_mod_cast exampleWeight_sum])

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

def exampleCostGap : ℝ :=
  neverDefectCostGap examplePreference exampleCost (by decide) (by decide)

theorem exampleCostGap_pos : 0 < exampleCostGap := by
  exact neverDefect_cost_gap_positive examplePreference exampleCost
    (by decide) (by decide) (by norm_num [exampleCost])

def exampleCounts : PatternCounts := fun _ =>
  (100 / exampleCostGap, 100 / exampleCostGap)

theorem example_flip_instance (C : AdmittedPreference) :
    neverDefectCostGap C exampleCost (by decide) (by decide) =
      3 / 10 * (Real.log (C.kernel.mass () .closure) -
        Real.log (C.kernel.mass () .tokenUse)) := by
  rw [neverDefect_cost_gap_eq]
  norm_num [exampleCost]

theorem example_novelty_below_cost_gap :
    cascadeNovelty exampleCounts .neverDefect genuineRepair -
        cascadeNovelty exampleCounts .neverDefect historicalMisclassification <
      exampleCostGap := by
  simp [cascadeNovelty, cascadeNoveltyFrom, genuineRepair, historicalMisclassification,
    initialRepairState, guard, effect, exampleCounts]
  have hg := exampleCostGap_pos
  have hn := PatternThetaNovelty.novelty_eq (100 / exampleCostGap)
    (100 / exampleCostGap) (div_pos (by norm_num) hg) (div_pos (by norm_num) hg)
  rw [hn]
  field_simp
  nlinarith

theorem example_flip :
    cascadeG examplePreference exampleCost
          (boundedHistorical exampleCost (by decide)) .neverDefect -
          cascadeNovelty exampleCounts .neverDefect historicalMisclassification <
      cascadeG examplePreference exampleCost
          (boundedGenuine exampleCost (by decide)) .neverDefect -
          cascadeNovelty exampleCounts .neverDefect genuineRepair := by
  apply (neverDefect_flip_iff examplePreference exampleCost
    (by decide) (by decide) exampleCounts).2
  exact example_novelty_below_cost_gap

#print axioms recorded_cascade_guard_check
#print axioms costKernel
#print axioms neverDefect_stepG_equal_at_zero
#print axioms neverDefect_cost_gap_positive
#print axioms neverDefect_cost_gap_strictMono
#print axioms neverDefect_flip_iff
#print axioms realDefect_flip_from_preference
#print axioms order_changes_prediction
#print axioms order_changes_G
#print axioms example_flip

end
end DarkTower.WarMachine.RepairCascadeG
