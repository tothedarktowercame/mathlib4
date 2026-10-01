import Mathlib

/-!
# A pinned want for the peripheral sensitivity witness

The semantic want is fixed before either policy is scored.  It prefers repair
completion, live-state preservation, typed/auditable observations, low elapsed
time, and low model-token use.  All five preferences are soft in this fixture:
every operational outcome has positive preference mass.

The coarse carrier retains completion alone.  It therefore identifies a
state-preserving REPL repair with a completed restart-and-replay, while the
operational preference distribution distinguishes them.  This file pins the
want and proves that loss before any numerical expected-free-energy comparison.

Source: `futon2/resources/wm/peripheral-recognition-sensitivity-sample-v1.edn`.
-/

namespace DarkTower.WarMachine.PinnedRepairWant

open scoped BigOperators

inductive CostBand
  | low
  | high
  deriving DecidableEq, Fintype, Repr

structure OperationalOutcome where
  completed : Bool
  statePreserved : Bool
  typedAndAuditable : Bool
  elapsed : CostBand
  modelTokens : CostBand
  deriving DecidableEq, Fintype, Repr

instance : Nonempty OperationalOutcome :=
  ⟨⟨false, false, false, .high, .high⟩⟩

/-- The semantic preference parameters are data pinned independently of the
policies to be compared. -/
structure RepairWant where
  completionWeight : ℝ
  preservationWeight : ℝ
  typedAuditWeight : ℝ
  lowTimeWeight : ℝ
  lowTokenWeight : ℝ
  completionWeight_pos : 0 < completionWeight
  preservationWeight_pos : 0 < preservationWeight
  typedAuditWeight_pos : 0 < typedAuditWeight
  lowTimeWeight_pos : 0 < lowTimeWeight
  lowTokenWeight_pos : 0 < lowTokenWeight

def pinnedWant : RepairWant where
  completionWeight := 4
  preservationWeight := 3
  typedAuditWeight := 2
  lowTimeWeight := 1
  lowTokenWeight := 1
  completionWeight_pos := by norm_num
  preservationWeight_pos := by norm_num
  typedAuditWeight_pos := by norm_num
  lowTimeWeight_pos := by norm_num
  lowTokenWeight_pos := by norm_num

def boolReward (weight : ℝ) (present : Bool) : ℝ :=
  if present then weight else 0

def lowCostReward (weight : ℝ) (cost : CostBand) : ℝ :=
  match cost with
  | .low => weight
  | .high => 0

def utility (want : RepairWant) (o : OperationalOutcome) : ℝ :=
  boolReward want.completionWeight o.completed +
  boolReward want.preservationWeight o.statePreserved +
  boolReward want.typedAuditWeight o.typedAndAuditable +
  lowCostReward want.lowTimeWeight o.elapsed +
  lowCostReward want.lowTokenWeight o.modelTokens

noncomputable def normalizer (want : RepairWant) : ℝ :=
  ∑ o : OperationalOutcome, Real.exp (utility want o)

theorem normalizer_pos (want : RepairWant) : 0 < normalizer want := by
  unfold normalizer
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- A normalized prior preference over operational outcomes.  It has no policy
argument: candidate policies predict outcomes, but do not choose the want. -/
noncomputable def preference (want : RepairWant) (o : OperationalOutcome) : ℝ :=
  Real.exp (utility want o) / normalizer want

/-- This fixture has no hard-zero outcomes. -/
theorem preference_pos (want : RepairWant) (o : OperationalOutcome) :
    0 < preference want o :=
  div_pos (Real.exp_pos _) (normalizer_pos want)

theorem preference_normalized (want : RepairWant) :
    ∑ o : OperationalOutcome, preference want o = 1 := by
  simp only [preference]
  rw [← Finset.sum_div]
  change normalizer want / normalizer want = 1
  exact div_self (ne_of_gt (normalizer_pos want))

def replRepair : OperationalOutcome where
  completed := true
  statePreserved := true
  typedAndAuditable := true
  elapsed := .low
  modelTokens := .low

def restartAndReplay : OperationalOutcome where
  completed := true
  statePreserved := false
  typedAndAuditable := false
  elapsed := .high
  modelTokens := .high

theorem replRepair_utility : utility pinnedWant replRepair = 11 := by
  norm_num [utility, pinnedWant, replRepair, boolReward, lowCostReward]

theorem restartAndReplay_utility : utility pinnedWant restartAndReplay = 4 := by
  norm_num [utility, pinnedWant, restartAndReplay, boolReward, lowCostReward]

theorem operational_preference_distinguishes :
    preference pinnedWant restartAndReplay < preference pinnedWant replRepair := by
  unfold preference
  apply (div_lt_div_iff_of_pos_right (normalizer_pos pinnedWant)).2
  apply Real.exp_lt_exp.mpr
  rw [restartAndReplay_utility, replRepair_utility]
  norm_num

structure CoarseOutcome where
  completed : Bool
  deriving DecidableEq, Fintype, Repr

def coarseEncode (o : OperationalOutcome) : CoarseOutcome :=
  ⟨o.completed⟩

/-- Completion-only state cannot see how completion was obtained. -/
theorem coarse_completed_collision :
    coarseEncode replRepair = coarseEncode restartAndReplay := by
  rfl

/-- Consequently no score that factors only through the coarse outcome can
rank the two repairs differently. -/
theorem no_coarse_score_separation (score : CoarseOutcome → ℝ) :
    score (coarseEncode replRepair) = score (coarseEncode restartAndReplay) := by
  rw [coarse_completed_collision]

#print axioms preference_pos
#print axioms preference_normalized
#print axioms operational_preference_distinguishes
#print axioms coarse_completed_collision
#print axioms no_coarse_score_separation

end DarkTower.WarMachine.PinnedRepairWant
