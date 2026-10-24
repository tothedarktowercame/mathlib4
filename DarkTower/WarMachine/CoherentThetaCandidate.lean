import DarkTower.WarMachine.PatternThetaNovelty
import DarkTower.WarMachine.CascadeCoApplyGNovelty
import DarkTower.WarMachine.ThetaPredictionConsumer

/-!
# One posterior supplies pattern transitions and novelty counts

Parr et al., *Active Inference* (2022), `refs/parr2022.txt:7214-7235`, equations
7.9–7.10, place parameter beliefs `Q(θ)` in the model and describe categorical
Dirichlet parameters as (pseudo-)counts, with their mean approximated by
normalised concentrations.  Equation 7.11 (`refs/parr2022.txt:7301-7325`) adds
expected parameter information gain to expected free energy.

This module selects the already documented binary specialization in
`PatternTheta` and `PatternThetaNovelty`: a Beta posterior's mean supplies the
transition probability, while the same positive concentrations supply the
existing novelty approximation.  `PatternThetaNovelty` explains that its
`1/(2(a+b))` quantity is an asymptotic approximation, not exact expected
information gain (`PatternThetaNovelty.lean:9-30`).  Applying this binary
parameter model to patterns is our explicit modelling choice, not a claim that
Parr names cascade patterns.

The constructor receives published readings and already-admitted histories. It
does not invent a prior, witness, guard fact, or admission evidence. Coherence
alone does not make the scorer enforce this predicate, establish runtime
compliance, or bind an occurrence to R20 selection and `reach`.
-/

namespace DarkTower.WarMachine.CoherentThetaCandidate

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.CascadeEFE
open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.CascadeCoApplyG
open DarkTower.WarMachine.CascadeCoApplyGNovelty
open DarkTower.WarMachine.Proof2.CoApplicationKernel
open DarkTower.WarMachine.Proof2.ContainmentOrder

noncomputable section

/-- A candidate uses one Beta posterior consistently: each transition theta is
the mean of the same positive concentrations supplied to novelty. -/
def Coherent {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (candidate : CandidateN ι V) : Prop :=
  ∃ pat, candidate.patterns = some pat ∧ ∀ p,
    (pat p).theta = (candidate.counts p).1 /
      ((candidate.counts p).1 + (candidate.counts p).2)

/-- Build both transition means and novelty concentrations from the same
published readings and admitted histories. -/
def ofReadings {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (consumes produces forbids : ι → Finset V)
    (reading : ι → PatternTheta.ThetaReading)
    (history : ι → List Bool)
    (initial : ProbabilityKernel Unit (Finset V))
    (observation : ProbabilityKernel (Finset V) CTauClassPreference.EndingClass) :
    CandidateN ι V where
  patterns := some fun p => PatternTheta.interpretWithTheta
    (consumes p) (produces p) (forbids p) (reading p) (history p)
  initial := initial
  observation := observation
  counts := fun p =>
    ((↑((reading p).priorS + PatternTheta.successes (history p)) : ℝ),
      (↑((reading p).priorF + PatternTheta.failures (history p)) : ℝ))
  counts_pos := by
    intro p
    constructor
    · change (0 : ℝ) < ↑((reading p).priorS + PatternTheta.successes (history p))
      exact_mod_cast Nat.lt_of_lt_of_le (reading p).success_positive
        (Nat.le_add_right (reading p).priorS (PatternTheta.successes (history p)))
    · change (0 : ℝ) < ↑((reading p).priorF + PatternTheta.failures (history p))
      exact_mod_cast Nat.lt_of_lt_of_le (reading p).failure_positive
        (Nat.le_add_right (reading p).priorF (PatternTheta.failures (history p)))

theorem ofReadings_coherent {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (consumes produces forbids : ι → Finset V)
    (reading : ι → PatternTheta.ThetaReading)
    (history : ι → List Bool)
    (initial : ProbabilityKernel Unit (Finset V))
    (observation : ProbabilityKernel (Finset V) CTauClassPreference.EndingClass) :
    Coherent (ofReadings consumes produces forbids reading history initial observation) := by
  refine ⟨fun p => PatternTheta.interpretWithTheta
    (consumes p) (produces p) (forbids p) (reading p) (history p), rfl, ?_⟩
  intro p
  simp [ofReadings, PatternTheta.interpretWithTheta, PatternTheta.thetaOf]

/-! ## Existing enabled singleton prediction consumer -/

def singleton (r : PatternTheta.ThetaReading) (xs : List Bool) : CandidateN Unit Bool :=
  ofReadings (fun _ => ∅) (fun _ => {true}) (fun _ => ∅)
    (fun _ => r) (fun _ => xs) (point ∅) ThetaPredictionConsumer.observation

theorem singleton_coherent (r : PatternTheta.ThetaReading) (xs : List Bool) :
    Coherent (singleton r xs) :=
  ofReadings_coherent _ _ _ _ _ _ _

theorem singleton_pattern (r : PatternTheta.ThetaReading) (xs : List Bool) :
    (singleton r xs).patterns = some (ThetaPredictionConsumer.pattern r xs) := rfl

theorem singleton_counts (r : PatternTheta.ThetaReading) (xs : List Bool) :
    (singleton r xs).counts () =
      ((↑(r.priorS + PatternTheta.successes xs) : ℝ),
        (↑(r.priorF + PatternTheta.failures xs) : ℝ)) := rfl

/-- Horizon one evaluates novelty at the initial state, where the sole
occurrence is enabled; hence it is exactly this reading's novelty. -/
theorem singleton_totalNovelty_eq (r : PatternTheta.ThetaReading) (xs : List Bool) :
    totalNovelty (ThetaPredictionConsumer.pattern r xs) (singleton r xs).counts
      (singleton r xs).initial 1 = PatternThetaNovelty.readingNovelty r xs := by
  classical
  simp only [totalNovelty, Fin.sum_univ_one]
  unfold expectedNovelty
  simp [singleton, ofReadings, prediction, point, finiteKernel,
    PatternThetaNovelty.readingNovelty, ThetaPredictionConsumer.frontier_eq,
    show (Finset.univ : Finset (Finset Bool)) = {∅, {false}, {true}, {false, true}} by decide]

/-- One admitted success moves both views of the same posterior: the canonical
focused prediction rises and the horizon-one novelty approximation falls. -/
theorem coherent_admitted_success_moves_both
    (r : PatternTheta.ThetaReading) (xs : List Bool) :
    (ThetaPredictionConsumer.oneStep r xs).mass () .focused <
        (ThetaPredictionConsumer.oneStep r (xs ++ [true])).mass () .focused ∧
      totalNovelty (ThetaPredictionConsumer.pattern r (xs ++ [true]))
          (singleton r (xs ++ [true])).counts (singleton r (xs ++ [true])).initial 1 <
        totalNovelty (ThetaPredictionConsumer.pattern r xs)
          (singleton r xs).counts (singleton r xs).initial 1 := by
  constructor
  · exact ThetaPredictionConsumer.admitted_success_raises_prediction r xs
  · rw [singleton_totalNovelty_eq, singleton_totalNovelty_eq]
    unfold PatternThetaNovelty.readingNovelty
    have ha : (0 : ℝ) < ↑(r.priorS + PatternTheta.successes xs) := by
      exact_mod_cast Nat.lt_of_lt_of_le r.success_positive
        (Nat.le_add_right r.priorS (PatternTheta.successes xs))
    have hb : (0 : ℝ) < ↑(r.priorF + PatternTheta.failures xs) := by
      exact_mod_cast Nat.lt_of_lt_of_le r.failure_positive
        (Nat.le_add_right r.priorF (PatternTheta.failures xs))
    simpa [PatternTheta.successes_append, PatternTheta.failures_append,
      PatternTheta.successes, PatternTheta.failures, Nat.cast_add, add_assoc] using
        PatternThetaNovelty.success_decreases
          (↑(r.priorS + PatternTheta.successes xs))
          (↑(r.priorF + PatternTheta.failures xs)) ha hb

/-! ## Incoherent independently supplied controls -/

def staleCounts (r : PatternTheta.ThetaReading) (xs : List Bool) : CandidateN Unit Bool where
  toCandidate := (singleton r (xs ++ [true])).toCandidate
  counts := (singleton r xs).counts
  counts_pos := (singleton r xs).counts_pos

def frozenThetaFreshCounts (r : PatternTheta.ThetaReading) (xs : List Bool) :
    CandidateN Unit Bool where
  toCandidate := (singleton r xs).toCandidate
  counts := (singleton r (xs ++ [true])).counts
  counts_pos := (singleton r (xs ++ [true])).counts_pos

theorem staleCounts_incoherent (r : PatternTheta.ThetaReading) (xs : List Bool) :
    ¬ Coherent (staleCounts r xs) := by
  rintro ⟨pat, hp, hmean⟩
  simp only [staleCounts, singleton, ofReadings] at hp hmean
  cases hp
  have hm := hmean ()
  simp [PatternTheta.interpretWithTheta, PatternTheta.thetaOf] at hm
  have hs := PatternTheta.success_raises r xs
  have hreal : (PatternTheta.thetaOf r (xs ++ [true]) : ℝ) =
      (PatternTheta.thetaOf r xs : ℝ) := by
    simpa [PatternTheta.thetaOf, Nat.cast_add] using hm
  have hne : (PatternTheta.thetaOf r (xs ++ [true]) : ℝ) ≠
      (PatternTheta.thetaOf r xs : ℝ) := by
    exact_mod_cast (ne_of_gt hs)
  exact hne hreal

theorem frozenThetaFreshCounts_incoherent (r : PatternTheta.ThetaReading) (xs : List Bool) :
    ¬ Coherent (frozenThetaFreshCounts r xs) := by
  rintro ⟨pat, hp, hmean⟩
  simp only [frozenThetaFreshCounts, singleton, ofReadings] at hp hmean
  cases hp
  have hm := hmean ()
  simp [PatternTheta.interpretWithTheta, PatternTheta.thetaOf] at hm
  have hs := PatternTheta.success_raises r xs
  have hreal : (PatternTheta.thetaOf r xs : ℝ) =
      (PatternTheta.thetaOf r (xs ++ [true]) : ℝ) := by
    simpa [PatternTheta.thetaOf, Nat.cast_add] using hm
  have hne : (PatternTheta.thetaOf r xs : ℝ) ≠
      (PatternTheta.thetaOf r (xs ++ [true]) : ℝ) := by
    exact_mod_cast (ne_of_lt hs)
  exact hne hreal

theorem lessTried_incoherent : ¬ Coherent lessTried := by
  rintro ⟨pat, hp, hmean⟩
  simp [lessTried, baseOne] at hp
  cases hp
  have := hmean ()
  norm_num [lessTried, onePattern] at this

theorem moreTried_incoherent : ¬ Coherent moreTried := by
  rintro ⟨pat, hp, hmean⟩
  simp [moreTried, baseOne] at hp
  cases hp
  have := hmean ()
  norm_num [moreTried, onePattern] at this

#print axioms ofReadings_coherent
#print axioms coherent_admitted_success_moves_both
#print axioms staleCounts_incoherent
#print axioms frozenThetaFreshCounts_incoherent
#print axioms lessTried_incoherent
#print axioms moreTried_incoherent

end
end DarkTower.WarMachine.CoherentThetaCandidate
