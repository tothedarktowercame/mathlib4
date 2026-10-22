import DarkTower.WarMachine.PatternTheta
import Mathlib.Probability.Distributions.Beta
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic

/-!
# Novelty of one pattern's learned binary parameter

Source: refs/dacosta2020.txt:1397–1421, Appendix C, equations 42–44:
expected free energy subtracts expected parameter information gain. Equations
55–58, refs/dacosta2020.txt:1520–1563, obtain the reference implementation's
approximation from a one-count Dirichlet update. In particular :1546 says
“We can use an asymptotic expansion of the digamma function”. Equation 57
approximates the outcome-conditioned KL by 1/(2 a_j) - 1/(2 a_0).

Our specialization: one known pattern, one Beta column, positive real counts
a,b, and predictive probabilities a/(a+b), b/(a+b). `novelty` averages that
approximation over the two outcomes. Its simplification is 1/(2(a+b)); this
is not an identity for the exact information gain, especially at small counts.
The source derives the formula for observation parameters A; applying the same
binary Dirichlet arithmetic to a pattern's transition parameter θ is our model
choice, not a claim that the paper names patterns. Witness admission remains
PatternTheta's caller's responsibility.

`expectedInfoGain` states the exact expected posterior KL for the conjugate
Beta/Bernoulli experiment, using Mathlib's Beta measures and extended-nonnegative
KL. It is the standard expected-KL definition of outcome/parameter mutual
information: success has posterior Beta(a+1,b), failure Beta(a,b+1).
We do not prove conjugacy, finiteness, or an approximation error bound here;
all ordering theorems below concern `novelty`, not `expectedInfoGain`.

G_with_novelty = risk + ambiguity − novelty is the next composition packet.
The local ordering lemma only pins the sign; no cascade G module is changed.
-/

namespace DarkTower.WarMachine.PatternThetaNovelty

open scoped ENNReal

noncomputable section

/-- Equation 57 averaged using the Beta posterior predictive mean. -/
def novelty (a b : ℝ) : ℝ :=
  (a / (a + b)) * (1 / (2 * a) - 1 / (2 * (a + b))) +
  (b / (a + b)) * (1 / (2 * b) - 1 / (2 * (a + b)))

/-- Exact expected posterior KL, distinct from the asymptotic approximation.
Its Beta/Bernoulli interpretation requires positive a and b. -/
def expectedInfoGain (a b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (a / (a + b)) *
    InformationTheory.klDiv (ProbabilityTheory.betaMeasure (a + 1) b)
      (ProbabilityTheory.betaMeasure a b) +
  ENNReal.ofReal (b / (a + b)) *
    InformationTheory.klDiv (ProbabilityTheory.betaMeasure a (b + 1))
      (ProbabilityTheory.betaMeasure a b)

/-- For two outcomes the approximation depends only on total concentration. -/
theorem novelty_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    novelty a b = 1 / (2 * (a + b)) := by
  unfold novelty
  field_simp
  nlinarith

theorem novelty_nonneg (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ novelty a b := by
  rw [novelty_eq a b ha hb]
  positivity

/-- Any increase in total positive concentration strictly reduces novelty. -/
theorem novelty_lt_of_total_lt (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b < c + d) : novelty c d < novelty a b := by
  rw [novelty_eq a b ha hb, novelty_eq c d hc hd]
  apply one_div_lt_one_div_of_lt
  · positivity
  · linarith

theorem success_decreases (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    novelty (a + 1) b < novelty a b := by
  apply novelty_lt_of_total_lt <;> linarith

theorem failure_decreases (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    novelty a (b + 1) < novelty a b := by
  apply novelty_lt_of_total_lt <;> linarith

/-- Explicit inverse-concentration bound, with C = 1/2. -/
theorem novelty_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    novelty a b ≤ (1 / 2 : ℝ) / (a + b) := by
  rw [novelty_eq a b ha hb]
  apply le_of_eq
  field_simp

/-- Reading pseudo-counts plus only the caller's admitted witnessed outcomes. -/
def readingNovelty (r : PatternTheta.ThetaReading) (xs : List Bool) : ℝ :=
  novelty ((r.priorS : ℝ) + PatternTheta.successes xs)
    ((r.priorF : ℝ) + PatternTheta.failures xs)

/-- Any nonempty witnessed history reduces the approximation, even if the mean changes. -/
theorem fires_reduce (r : PatternTheta.ThetaReading) (xs : List Bool)
    (hne : xs ≠ []) : readingNovelty r xs < readingNovelty r [] := by
  have ha : (0 : ℝ) < r.priorS := by exact_mod_cast r.success_positive
  have hb : (0 : ℝ) < r.priorF := by exact_mod_cast r.failure_positive
  have hn : 0 < xs.length := List.length_pos_iff.mpr hne
  have hs : (0 : ℝ) < (PatternTheta.successes xs : ℝ) + PatternTheta.failures xs := by
    exact_mod_cast (show 0 < PatternTheta.successes xs + PatternTheta.failures xs by
      rw [PatternTheta.counts_length]; exact hn)
  simp only [readingNovelty, PatternTheta.successes, PatternTheta.failures,
    Nat.cast_zero, add_zero]
  apply novelty_lt_of_total_lt
  · exact ha
  · exact hb
  · positivity
  · positivity
  · linarith

/-- Requested equal-means case; the stronger theorem does not need mean equality. -/
theorem equal_mean_fires_reduce (r : PatternTheta.ThetaReading) (xs : List Bool)
    (hne : xs ≠ []) (_hmean : PatternTheta.thetaOf r xs = PatternTheta.thetaOf r []) :
    readingNovelty r xs < readingNovelty r [] := fires_reduce r xs hne

/-- At equal risk and ambiguity the less-tried pattern has lower G. -/
theorem less_tried_lower_G (r : PatternTheta.ThetaReading) (xs : List Bool)
    (hne : xs ≠ []) (risk ambiguity : ℝ) :
    risk + ambiguity - readingNovelty r [] <
      risk + ambiguity - readingNovelty r xs := by
  have h := fires_reduce r xs hne
  linarith

/-- A non-vacuous equal-means instance: one success and one failure preserve 1/2. -/
theorem balanced_fires_example :
    PatternTheta.thetaOf PatternTheta.controlReading [true, false] =
      PatternTheta.thetaOf PatternTheta.controlReading [] ∧
    readingNovelty PatternTheta.controlReading [true, false] = 1 / 8 ∧
    readingNovelty PatternTheta.controlReading [] = 1 / 4 := by
  norm_num [PatternTheta.thetaOf, PatternTheta.controlReading, readingNovelty,
    PatternTheta.successes, PatternTheta.failures, novelty]

end
end DarkTower.WarMachine.PatternThetaNovelty

#print axioms DarkTower.WarMachine.PatternThetaNovelty.novelty_eq
#print axioms DarkTower.WarMachine.PatternThetaNovelty.novelty_nonneg
#print axioms DarkTower.WarMachine.PatternThetaNovelty.success_decreases
#print axioms DarkTower.WarMachine.PatternThetaNovelty.failure_decreases
#print axioms DarkTower.WarMachine.PatternThetaNovelty.novelty_bound
#print axioms DarkTower.WarMachine.PatternThetaNovelty.fires_reduce
#print axioms DarkTower.WarMachine.PatternThetaNovelty.equal_mean_fires_reduce
#print axioms DarkTower.WarMachine.PatternThetaNovelty.less_tried_lower_G
#print axioms DarkTower.WarMachine.PatternThetaNovelty.balanced_fires_example
