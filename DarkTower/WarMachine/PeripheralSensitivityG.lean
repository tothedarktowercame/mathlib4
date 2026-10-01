import DarkTower.WarMachine.PinnedRepairWant

/-!
# Deterministic and stochastic carrier-sensitivity witnesses

Both comparisons use the single preference distribution pinned in
`PinnedRepairWant`.  The coarse preference is its pushforward along the
completion-only encoding; it is not a separately chosen objective.

The deterministic comparison isolates outcome preference.  The stochastic
comparison gives each policy the same success/fallback probabilities and the
same ambiguity contribution.  Their predictive-entropy terms therefore
cancel, leaving the operationally represented outcomes to decide the strict
ranking.  On the coarse carrier, both predictive distributions coincide and
the policies tie in both models.
-/

namespace DarkTower.WarMachine.PeripheralSensitivityG

open scoped BigOperators
open PinnedRepairWant

noncomputable def surprisal (o : OperationalOutcome) : ℝ :=
  -Real.log (preference pinnedWant o)

theorem surprisal_lt_of_preference_gt {better worse : OperationalOutcome}
    (h : preference pinnedWant worse < preference pinnedWant better) :
    surprisal better < surprisal worse := by
  have hlog : Real.log (preference pinnedWant worse) <
      Real.log (preference pinnedWant better) :=
    Real.log_lt_log (preference_pos pinnedWant worse) h
  unfold surprisal
  linarith

/-- Point-mass risk: `KL(δₒ ∥ C) = -log C(o)`.  Deterministic observation
also makes the ambiguity contribution zero in this fixture. -/
noncomputable def deterministicG (o : OperationalOutcome) : ℝ := surprisal o

theorem deterministic_operational_ranking :
    deterministicG replRepair < deterministicG restartAndReplay :=
  surprisal_lt_of_preference_gt operational_preference_distinguishes

/-- The same semantic preference pushed forward to the coarse observation
space. -/
noncomputable def coarsePreference (c : CoarseOutcome) : ℝ :=
  ∑ o : OperationalOutcome,
    if coarseEncode o = c then preference pinnedWant o else 0

noncomputable def coarseSurprisal (c : CoarseOutcome) : ℝ :=
  -Real.log (coarsePreference c)

noncomputable def coarseDeterministicG (o : OperationalOutcome) : ℝ :=
  coarseSurprisal (coarseEncode o)

theorem deterministic_coarse_tie :
    coarseDeterministicG replRepair = coarseDeterministicG restartAndReplay := by
  rw [coarseDeterministicG, coarseDeterministicG, coarse_completed_collision]

/-- A degraded but state-preserving and observable REPL outcome. -/
def replFallback : OperationalOutcome where
  completed := false
  statePreserved := true
  typedAndAuditable := true
  elapsed := .low
  modelTokens := .low

/-- Failed restart-and-replay: no completion and none of the operational
properties represented by the pinned want. -/
def restartFallback : OperationalOutcome where
  completed := false
  statePreserved := false
  typedAndAuditable := false
  elapsed := .high
  modelTokens := .high

theorem replFallback_utility : utility pinnedWant replFallback = 7 := by
  norm_num [utility, pinnedWant, replFallback, boolReward, lowCostReward]

theorem restartFallback_utility : utility pinnedWant restartFallback = 0 := by
  norm_num [utility, pinnedWant, restartFallback, boolReward, lowCostReward]

theorem fallback_preference_distinguishes :
    preference pinnedWant restartFallback < preference pinnedWant replFallback := by
  unfold preference
  apply (div_lt_div_iff_of_pos_right (normalizer_pos pinnedWant)).2
  apply Real.exp_lt_exp.mpr
  rw [restartFallback_utility, replFallback_utility]
  norm_num

theorem fallback_surprisal_distinguishes :
    surprisal replFallback < surprisal restartFallback :=
  surprisal_lt_of_preference_gt fallback_preference_distinguishes

/-- The common `Σ q log q` part of binary KL risk for probabilities `4/5`
and `1/5`. -/
noncomputable def binaryPredictiveTerm : ℝ :=
  (4 / 5 : ℝ) * Real.log (4 / 5 : ℝ) +
  (1 / 5 : ℝ) * Real.log (1 / 5 : ℝ)

/-- Binary KL risk in expanded form:
`Σ q log(q/C) = Σ q log q + Σ q (-log C)`.
`sharedAmbiguity` is explicit so the theorem states the matched-model
assumption rather than silently omitting the ambiguity term. -/
noncomputable def stochasticG
    (success fallback : OperationalOutcome) (sharedAmbiguity : ℝ) : ℝ :=
  binaryPredictiveTerm +
  (4 / 5 : ℝ) * surprisal success +
  (1 / 5 : ℝ) * surprisal fallback +
  sharedAmbiguity

theorem stochastic_operational_ranking (sharedAmbiguity : ℝ) :
    stochasticG replRepair replFallback sharedAmbiguity <
      stochasticG restartAndReplay restartFallback sharedAmbiguity := by
  have hs := deterministic_operational_ranking
  have hf := fallback_surprisal_distinguishes
  unfold deterministicG at hs
  unfold stochasticG
  nlinarith

theorem coarse_fallback_collision :
    coarseEncode replFallback = coarseEncode restartFallback := by
  rfl

noncomputable def coarseStochasticG
    (success fallback : OperationalOutcome) (sharedAmbiguity : ℝ) : ℝ :=
  binaryPredictiveTerm +
  (4 / 5 : ℝ) * coarseSurprisal (coarseEncode success) +
  (1 / 5 : ℝ) * coarseSurprisal (coarseEncode fallback) +
  sharedAmbiguity

theorem stochastic_coarse_tie (sharedAmbiguity : ℝ) :
    coarseStochasticG replRepair replFallback sharedAmbiguity =
      coarseStochasticG restartAndReplay restartFallback sharedAmbiguity := by
  rw [coarseStochasticG, coarseStochasticG, coarse_completed_collision,
    coarse_fallback_collision]

theorem deterministic_and_stochastic_sensitivity (sharedAmbiguity : ℝ) :
    deterministicG replRepair < deterministicG restartAndReplay ∧
    coarseDeterministicG replRepair = coarseDeterministicG restartAndReplay ∧
    stochasticG replRepair replFallback sharedAmbiguity <
      stochasticG restartAndReplay restartFallback sharedAmbiguity ∧
    coarseStochasticG replRepair replFallback sharedAmbiguity =
      coarseStochasticG restartAndReplay restartFallback sharedAmbiguity :=
  ⟨deterministic_operational_ranking, deterministic_coarse_tie,
    stochastic_operational_ranking sharedAmbiguity,
    stochastic_coarse_tie sharedAmbiguity⟩

#print axioms deterministic_operational_ranking
#print axioms deterministic_coarse_tie
#print axioms stochastic_operational_ranking
#print axioms stochastic_coarse_tie
#print axioms deterministic_and_stochastic_sensitivity

end DarkTower.WarMachine.PeripheralSensitivityG
