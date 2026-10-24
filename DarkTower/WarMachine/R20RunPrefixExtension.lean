import DarkTower.WarMachine.R20RunExample

/-!
# Exact one-step extension of an R20 certified prefix

`R20Run.RunCertified` is a bounded predicate on one supplied click sequence.
This module proves its exact successor decomposition and restriction law.  It
does not construct a successor, establish an infinite run, or connect retained
theta to a construction consumer.
-/

namespace DarkTower.WarMachine.R20RunPrefixExtension

open CTauClassPreference R15StrategicTarget R20FocusedSelection
open R20Run

variable {Policy : Type} [Fintype Policy] [Nonempty Policy]
noncomputable section

/-- The existing per-click triple, named only to state the decomposition
without changing any constituent predicate. -/
def ClickCertified (L : AffectiveLevel) (relation : Target → Target → TargetRelation)
    (click : Click Policy) : Prop :=
  FocusCertified relation click.records click.ports click.selection ∧
    PriorFromCounts click ∧ BetaFromValence L click

omit [Nonempty Policy] in
/-- Exact one-step decomposition on the same supplied sequence. -/
theorem runCertified_succ_iff (L : AffectiveLevel)
    (relation : Target → Target → TargetRelation) (c : ℕ → Click Policy) (n : ℕ) :
    RunCertified L relation c (n + 1) ↔
      RunCertified L relation c n ∧
      ClickCertified L relation (c (n + 1)) ∧
      Carries L (c n) (c (n + 1)) := by
  constructor
  · intro run
    refine ⟨⟨?_, ?_⟩, run.1 (n + 1) (by omega), run.2 n (by omega)⟩
    · intro i hi
      exact run.1 i (by omega)
    · intro i hi
      exact run.2 i (by omega)
  · rintro ⟨priorRun, successor, boundary⟩
    constructor
    · intro i hi
      rcases lt_or_eq_of_le hi with before | rfl
      · exact priorRun.1 i (by omega)
      · exact successor
    · intro i hi
      by_cases before : i < n
      · exact priorRun.2 i before
      · have atBoundary : i = n := by omega
        subst i
        exact boundary

omit [Nonempty Policy] in
/-- Any shorter prefix of the same certified supplied sequence remains
certified. -/
theorem runCertified_mono (L : AffectiveLevel)
    (relation : Target → Target → TargetRelation) (c : ℕ → Click Policy)
    {m n : ℕ} (within : m ≤ n) (run : RunCertified L relation c n) :
    RunCertified L relation c m := by
  constructor
  · intro i hi
    exact run.1 i (by omega)
  · intro i hi
    exact run.2 i (by omega)

/-! ## Existing two-click instance -/

open R20RunExample

theorem example_two_click_decomposes :
    RunCertified R20Run.flatLevel R15InjuryTier.relationExample
        (R20RunExample.clicks R20RunExample.click1) 1 ↔
      RunCertified R20Run.flatLevel R15InjuryTier.relationExample
          (R20RunExample.clicks R20RunExample.click1) 0 ∧
      ClickCertified R20Run.flatLevel R15InjuryTier.relationExample
          (R20RunExample.clicks R20RunExample.click1 1) ∧
      Carries R20Run.flatLevel
        (R20RunExample.clicks R20RunExample.click1 0)
        (R20RunExample.clicks R20RunExample.click1 1) := by
  simpa using runCertified_succ_iff R20Run.flatLevel R15InjuryTier.relationExample
    (R20RunExample.clicks R20RunExample.click1) 0

theorem example_zero_prefix :
    RunCertified R20Run.flatLevel R15InjuryTier.relationExample
      (R20RunExample.clicks R20RunExample.click1) 0 :=
  runCertified_mono R20Run.flatLevel R15InjuryTier.relationExample
    (R20RunExample.clicks R20RunExample.click1) (by omega)
    R20RunExample.example_runCertified

/-! ## Per-click validity does not replace the boundary -/

/-- A replayed successor is locally the same valid click shape, but carries
run id zero again. -/
def replayedClick : Click PrecisionFromObservation.TwoPolicy :=
  R20RunExample.clickAt 0 R20RunExample.before1 R20RunExample.d1

def replayedClicks : ℕ → Click PrecisionFromObservation.TwoPolicy :=
  R20RunExample.clicks replayedClick

theorem replayedClick_certified :
    ClickCertified R20Run.flatLevel R15InjuryTier.relationExample replayedClick := by
  refine ⟨R20RunExample.clickAt_focusCertified 0 R20RunExample.before1 R20RunExample.d1
      R20RunExample.positive1,
    R20RunExample.clickAt_prior 0 R20RunExample.before1 R20RunExample.d1 ?_,
    R20RunExample.clickAt_beta 0 R20RunExample.before1 R20RunExample.d1⟩
  intro s
  rw [R20RunExample.d1_eq]
  dsimp only
  split_ifs <;> norm_num

theorem replayed_boundary_refused :
    ¬ Carries R20Run.flatLevel R20RunExample.click0 replayedClick := by
  intro carries
  exact (Nat.lt_irrefl 0) carries.runAdvances

/-- The prefix and successor each satisfy their local obligations, but the
missing replay boundary prevents extension. -/
theorem per_click_validity_does_not_extend :
    RunCertified R20Run.flatLevel R15InjuryTier.relationExample replayedClicks 0 ∧
    ClickCertified R20Run.flatLevel R15InjuryTier.relationExample (replayedClicks 1) ∧
    ¬ RunCertified R20Run.flatLevel R15InjuryTier.relationExample replayedClicks 1 := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro i hi
      have atZero : i = 0 := by omega
      subst i
      simpa [replayedClicks, R20RunExample.clicks] using
        R20RunExample.example_runCertified.1 0 (by omega)
    · intro i hi
      omega
  · simpa [replayedClicks, R20RunExample.clicks] using replayedClick_certified
  · simpa [replayedClicks, replayedClick] using R20RunExample.replayedRun_breaks_run

#print axioms runCertified_succ_iff
#print axioms runCertified_mono
#print axioms example_two_click_decomposes
#print axioms per_click_validity_does_not_extend

end
end DarkTower.WarMachine.R20RunPrefixExtension
