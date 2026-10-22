import DarkTower.WarMachine.CascadeCoApplyG
import DarkTower.WarMachine.PatternThetaNovelty

/-!
# Co-application expected free energy with pattern novelty

Da Costa et al. write expected free energy as ambiguity plus risk minus
expected parameter information gain (`refs/dacosta2020.txt:1403`, equation
42).  They describe that third term as an expectation over predicted states
and outcomes (`refs/dacosta2020.txt:1403-1409`), and equation 58 gives its
analytical form under the predicted states (`refs/dacosta2020.txt:1555-1563`).
Those are source claims about model parameters; the paper does not identify
War Machine patterns or its enabled-frontier co-application rule.

Our modelling choice, inherited from `PatternThetaNovelty`, assigns each
pattern a binary theta parameter.  Its positive Beta counts are the
`PatternTheta` reading pseudo-counts plus admitted witnessed fires.  At each
epoch we credit novelty only for patterns in the enabled frontier that the
co-application kernel can fire.  The state distribution is exactly the same
`prediction` used by the ambiguity/risk score.  We subtract the resulting
expected novelty from `CascadeCoApplyG.scoreCascadeCo`; no refusal or horizon
rule is changed.
-/

namespace DarkTower.WarMachine.CascadeCoApplyGNovelty

open scoped BigOperators
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.CascadeEFE
open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.CascadeCoApplyG
open DarkTower.WarMachine.PatternThetaNovelty
open DarkTower.WarMachine.CTauClassPreference
open DarkTower.WarMachine.Proof2.ContainmentOrder
open DarkTower.WarMachine.Proof2.CoApplicationKernel

noncomputable section

/-- A co-application candidate plus one positive Beta pair per pattern. -/
structure CandidateN (ι V : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] extends Candidate ι V where
  counts : ι → ℝ × ℝ
  counts_pos : ∀ p, 0 < (counts p).1 ∧ 0 < (counts p).2

/-- Expected novelty at epoch `tau + 1`: expectation under the state at
`tau`, followed by the sum over precisely that state's enabled frontier. -/
def expectedNovelty {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (pat : ι → InterpretedPattern V)
    (counts : ι → ℝ × ℝ) (initial : ProbabilityKernel Unit (Finset V))
    (tau : ℕ) : ℝ :=
  ∑ s, (prediction initial (coKernel pat) tau).mass () s *
    ∑ p ∈ enabledFrontier pat (containmentOrder pat) s,
      novelty (counts p).1 (counts p).2

def totalNovelty {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (pat : ι → InterpretedPattern V)
    (counts : ι → ℝ × ℝ) (initial : ProbabilityKernel Unit (Finset V))
    (H : ℕ) : ℝ :=
  ∑ tau : Fin H, expectedNovelty pat counts initial tau.val

/-- The co-application score minus expected pattern-parameter novelty. -/
def scoreCascadeCoN {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (candidate : CandidateN ι V) (H : ℕ)
    (c : Fin H → ProbabilityKernel Unit EndingClass) : Except CascadeCoApplyG.Refusal ℝ :=
  match scoreCascadeCo candidate.toCandidate H c with
  | .error e => .error e
  | .ok g => match candidate.patterns with
    | none => .error .missingInterpretation
    | some pat => .ok (g - totalNovelty pat candidate.counts candidate.initial H)

theorem expectedNovelty_nonneg {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (pat : ι → InterpretedPattern V)
    (counts : ι → ℝ × ℝ) (counts_pos : ∀ p, 0 < (counts p).1 ∧ 0 < (counts p).2)
    (initial : ProbabilityKernel Unit (Finset V)) (tau : ℕ) :
    0 ≤ expectedNovelty pat counts initial tau := by
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg (ProbabilityKernel.nonnegative _ _ _)
  apply Finset.sum_nonneg
  intro p hp
  exact novelty_nonneg _ _ (counts_pos p).1 (counts_pos p).2

theorem totalNovelty_nonneg {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (pat : ι → InterpretedPattern V)
    (counts : ι → ℝ × ℝ) (counts_pos : ∀ p, 0 < (counts p).1 ∧ 0 < (counts p).2)
    (initial : ProbabilityKernel Unit (Finset V)) (H : ℕ) :
    0 ≤ totalNovelty pat counts initial H := by
  exact Finset.sum_nonneg fun tau _ => expectedNovelty_nonneg pat counts counts_pos initial tau.val

/-- (a) On every successful score, novelty can only lower G. -/
theorem scoreCascadeCoN_le_scoreCascadeCo {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (candidate : CandidateN ι V) (H : ℕ)
    (c : Fin H → ProbabilityKernel Unit EndingClass) {gN : ℝ}
    (hN : scoreCascadeCoN candidate H c = .ok gN) :
    ∃ g, scoreCascadeCo candidate.toCandidate H c = .ok g ∧ gN ≤ g := by
  unfold scoreCascadeCoN at hN
  split at hN <;> rename_i old hold
  · simp at hN
  · split at hN <;> rename_i patterns hp
    · simp at hN
    · simp only [Except.ok.injEq] at hN
      subst gN
      exact ⟨old, hold, sub_le_self old
        (totalNovelty_nonneg patterns candidate.counts candidate.counts_pos candidate.initial H)⟩

/-- (c) Changing the counts of a pattern that is never in any predicted
enabled frontier changes no novelty term. -/
theorem never_enabled_contributes_nothing {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (pat : ι → InterpretedPattern V)
    (initial : ProbabilityKernel Unit (Finset V)) (H : ℕ) (p0 : ι)
    (counts₁ counts₂ : ι → ℝ × ℝ)
    (same : ∀ p, p ≠ p0 → counts₁ p = counts₂ p)
    (never : ∀ (tau : Fin H) s,
      (prediction initial (coKernel pat) tau.val).mass () s ≠ 0 →
      p0 ∉ enabledFrontier pat (containmentOrder pat) s) :
    totalNovelty pat counts₁ initial H = totalNovelty pat counts₂ initial H := by
  unfold totalNovelty expectedNovelty
  apply Finset.sum_congr rfl
  intro tau _
  apply Finset.sum_congr rfl
  intro s _
  by_cases hm : (prediction initial (coKernel pat) tau.val).mass () s = 0
  · simp [hm]
  · congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hne : p ≠ p0 := by
      intro h
      subst p
      exact (never tau s hm) hp
    rw [same p hne]

/-! ### Positive-probability less-tried control -/

/-! ## (b) in general: more evidence on a pattern never raises expected novelty -/

private theorem novelty_le_of_total_le (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (h : a + b ≤ c + d) : novelty c d ≤ novelty a b := by
  rw [novelty_eq a b ha hb, novelty_eq c d hc hd]
  apply one_div_le_one_div_of_le
  · positivity
  · linarith

/-- Pointwise larger total counts give no more expected novelty at any epoch. -/
theorem expectedNovelty_antitone {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (pat : ι → InterpretedPattern V)
    (c c' : ι → ℝ × ℝ) (hc : ∀ p, 0 < (c p).1 ∧ 0 < (c p).2)
    (hc' : ∀ p, 0 < (c' p).1 ∧ 0 < (c' p).2)
    (hle : ∀ p, (c p).1 + (c p).2 ≤ (c' p).1 + (c' p).2)
    (initial : ProbabilityKernel Unit (Finset V)) (tau : ℕ) :
    expectedNovelty pat c' initial tau ≤ expectedNovelty pat c initial tau := by
  unfold expectedNovelty
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ ((prediction initial (coKernel pat) tau).nonnegative () s)
  apply Finset.sum_le_sum
  intro p _
  exact novelty_le_of_total_le _ _ _ _ (hc p).1 (hc p).2 (hc' p).1 (hc' p).2 (hle p)

/-- The general form of (b). Two candidates share dynamics, and the second has
pointwise no fewer counts. If, at some epoch, a state of positive predicted mass
enables a pattern with strictly more counts, the first (less-tried) candidate has
strictly larger total novelty, and so strictly lower `scoreCascadeCoN` at equal
`scoreCascadeCo`. -/
theorem totalNovelty_strict {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (pat : ι → InterpretedPattern V)
    (c c' : ι → ℝ × ℝ) (hc : ∀ p, 0 < (c p).1 ∧ 0 < (c p).2)
    (hc' : ∀ p, 0 < (c' p).1 ∧ 0 < (c' p).2)
    (hle : ∀ p, (c p).1 + (c p).2 ≤ (c' p).1 + (c' p).2)
    (initial : ProbabilityKernel Unit (Finset V)) (H : ℕ)
    (t : Fin H) (s : Finset V) (p : ι)
    (hmass : 0 < (prediction initial (coKernel pat) t.val).mass () s)
    (hp : p ∈ enabledFrontier pat (containmentOrder pat) s)
    (hlt : (c p).1 + (c p).2 < (c' p).1 + (c' p).2) :
    totalNovelty pat c' initial H < totalNovelty pat c initial H := by
  unfold totalNovelty
  apply Finset.sum_lt_sum
  · intro τ _
    exact expectedNovelty_antitone pat c c' hc hc' hle initial τ.val
  · refine ⟨t, Finset.mem_univ _, ?_⟩
    unfold expectedNovelty
    apply Finset.sum_lt_sum
    · intro x _
      apply mul_le_mul_of_nonneg_left _ ((prediction initial (coKernel pat) t.val).nonnegative () x)
      apply Finset.sum_le_sum
      intro q _
      exact novelty_le_of_total_le _ _ _ _ (hc q).1 (hc q).2 (hc' q).1 (hc' q).2 (hle q)
    · refine ⟨s, Finset.mem_univ _, ?_⟩
      apply mul_lt_mul_of_pos_left _ hmass
      apply Finset.sum_lt_sum
      · intro q _
        exact novelty_le_of_total_le _ _ _ _ (hc q).1 (hc q).2 (hc' q).1 (hc' q).2 (hle q)
      · exact ⟨p, hp, novelty_lt_of_total_lt _ _ _ _ (hc p).1 (hc p).2 (hc' p).1 (hc' p).2 hlt⟩


def onePattern : Unit → InterpretedPattern Bool := fun _ =>
  { consumes := ∅, produces := {false}, forbids := ∅, theta := 1
    theta_nonneg := by norm_num, theta_le_one := by norm_num }

def oneObservation : ProbabilityKernel (Finset Bool) EndingClass :=
  finiteKernel (fun _ ending => if ending = .focused then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro; simp)

def baseOne : Candidate Unit Bool where
  patterns := some onePattern
  initial := point ∅
  observation := oneObservation

def lessTried : CandidateN Unit Bool where
  toCandidate := baseOne
  counts := fun _ => (1, 1)
  counts_pos := by intro; norm_num

def moreTried : CandidateN Unit Bool where
  toCandidate := baseOne
  counts := fun _ => (2, 1)
  counts_pos := by intro; norm_num

theorem onePattern_noReach (p q : Unit) :
    ¬ Reach (containmentOrder onePattern) p q := by
  apply not_reach_of_empty (r := containmentOrder onePattern)
  intro a b h
  exact h.1 (Subsingleton.elim a b)

theorem onePattern_frontier :
    enabledFrontier onePattern (containmentOrder onePattern) ∅ = {()} := by
  ext p
  simp [enabledFrontier, onePattern, CascadeTransition.guard, onePattern_noReach]

theorem onePattern_guard : CascadeTransition.guard (onePattern ()) ∅ := by
  simp [CascadeTransition.guard, onePattern]

theorem onePattern_totalNovelty_less : totalNovelty onePattern lessTried.counts (point ∅) 1 = 1 / 4 := by
  simp only [totalNovelty, Fin.sum_univ_one]
  unfold expectedNovelty
  simp [prediction, point, finiteKernel, onePattern_frontier, lessTried, novelty]
  norm_num

theorem onePattern_totalNovelty_more : totalNovelty onePattern moreTried.counts (point ∅) 1 = 1 / 6 := by
  simp only [totalNovelty, Fin.sum_univ_one]
  unfold expectedNovelty
  simp [prediction, point, finiteKernel, onePattern_frontier, moreTried, novelty]
  norm_num

/-- (b) The candidates have identical dynamics and differ only by one witnessed
fire in the single pattern's positive Beta count.  That pattern is enabled
with probability one; hence the less-tried candidate has strictly lower G. -/
theorem less_tried_positive_fire_lower_G
    (c : Fin 1 → ProbabilityKernel Unit EndingClass) {g : ℝ}
    (hok : scoreCascadeCo baseOne 1 c = .ok g) :
    ∃ gLess gMore,
      scoreCascadeCoN lessTried 1 c = .ok gLess ∧
      scoreCascadeCoN moreTried 1 c = .ok gMore ∧ gLess < gMore := by
  refine ⟨g - 1 / 4, g - 1 / 6, ?_, ?_, by norm_num⟩
  · unfold scoreCascadeCoN
    rw [show scoreCascadeCo lessTried.toCandidate 1 c = .ok g by
      simpa [lessTried] using hok]
    simp [lessTried, baseOne]
    simpa [lessTried] using onePattern_totalNovelty_less
  · unfold scoreCascadeCoN
    rw [show scoreCascadeCo moreTried.toCandidate 1 c = .ok g by
      simpa [moreTried] using hok]
    simp [moreTried, baseOne]
    simpa [moreTried] using onePattern_totalNovelty_more

/-- Every candidate is evaluated at the supplied common horizon `H`. -/
def compareAtHorizonN {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (H : ℕ) (cands : List (CandidateN ι V)) :
    List (Except CascadeCoApplyG.Refusal ℝ) :=
  cands.map fun candidate => scoreCascadeCoN candidate H (classKernel H)

/-- (d) The novelty comparison preserves `compareAtHorizon`'s one-H rule. -/
theorem compareAtHorizonN_uses_H {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (H : ℕ) (cands : List (CandidateN ι V)) :
    compareAtHorizonN H cands =
      cands.map (fun candidate => scoreCascadeCoN candidate H (classKernel H)) := rfl

#print axioms expectedNovelty_antitone
#print axioms totalNovelty_strict
#print axioms scoreCascadeCoN_le_scoreCascadeCo
#print axioms less_tried_positive_fire_lower_G
#print axioms never_enabled_contributes_nothing
#print axioms compareAtHorizonN_uses_H

end
end DarkTower.WarMachine.CascadeCoApplyGNovelty
