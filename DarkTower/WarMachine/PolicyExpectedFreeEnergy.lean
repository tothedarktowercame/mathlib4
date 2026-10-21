import DarkTower.WarMachine.CTauClassPreference
import Mathlib.Tactic

/-!
# Expected free energy of a fixed categorical observation model

Friston (2017), refs/friston2017.txt:596-625, eq.2.6: predicted outcomes
o = A s, risk o·(ln o - U), U = ln C, plus expected observation entropy.
This is the fixed-A categorical specialization requested by H3: the full
paper also distinguishes E[A] and E[ln A] for uncertain Dirichlet parameters;
we do not identify E[ln A] with ln E[A]. Parr (2022) B.7-B.9,
refs/parr2022.txt:12636-12670, confirms G's role in policy inference, but
does not repeat this decomposition there.

Holes.observationEntropy and Holes.ambiguity express the same categorical
quantity using list-supported kernels; Holes.expectedFreeEnergy takes an
ambiguity estimator as an argument. Here finite sums compute both prediction
and ambiguity directly from A and s. AmbiguityBridge.categoricalAmbiguity
references that list-based definition; its Gaussian quantity is NOT reused.
The existing CTau classRisk is reused through the proved rational-cast bridge.
Real.log 0 = 0 gives zero entropy contributions at zero mass, but unsupported
preferences require an explicit EReal top branch, not a finite log-zero score.
-/

namespace DarkTower.WarMachine.PolicyExpectedFreeEnergy
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {S O : Type*} [Fintype S] [Fintype O]

def predictedOutcome (A : O → S → ℝ) (s : S → ℝ) : O → ℝ :=
  fun o => ∑ x, A o x * s x

def columnEntropy (A : O → S → ℝ) (x : S) : ℝ :=
  -(∑ o, A o x * Real.log (A o x))

def ambiguity (A : O → S → ℝ) (s : S → ℝ) : ℝ :=
  ∑ x, s x * columnEntropy A x

def Unsupported (o C : O → ℝ) : Prop := ∃ x, 0 < o x ∧ C x = 0

def finiteRisk (o C : O → ℝ) : ℝ :=
  ∑ x, if 0 < o x then o x * (Real.log (o x) - Real.log (C x)) else 0

def risk (o C : O → ℝ) : EReal :=
  if Unsupported o C then ⊤ else (finiteRisk o C : EReal)

def tickG (A : O → S → ℝ) (s : S → ℝ) (C : O → ℝ) : EReal :=
  risk (predictedOutcome A s) C + (ambiguity A s : EReal)

def policyExpectedFreeEnergy {Policy : Type*} {T : ℕ}
    (A : O → S → ℝ) (s : Policy → Fin T → S → ℝ)
    (C : Fin T → O → ℝ) (π : Policy) : EReal :=
  ∑ t, tickG A (s π t) (C t)

/-- T1: stochastic columns have nonnegative entropy; nonnegative state
weights suffice (normalization of the weights is not needed). -/
theorem ambiguity_nonneg (A : O → S → ℝ) (s : S → ℝ)
    (ha : ∀ o x, 0 ≤ A o x) (normal : ∀ x, ∑ o, A o x = 1)
    (hs : ∀ x, 0 ≤ s x) : 0 ≤ ambiguity A s := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (hs x)
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro o _
  have bound : A o x ≤ 1 := by
    rw [← normal x]
    exact Finset.single_le_sum (fun y _ => ha y x) (Finset.mem_univ o)
  exact mul_nonpos_of_nonneg_of_nonpos (ha o x) (Real.log_nonpos (ha o x) bound)

/-- T1 deterministic case: every column is a point mass. -/
theorem ambiguity_point_mass (A : O → S → ℝ) (s : S → ℝ)
    (point : ∀ x, ∃ y, ∀ o, A o x = if o = y then 1 else 0) :
    ambiguity A s = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  obtain ⟨y, hy⟩ := point x
  simp [columnEntropy, hy]

/-- T2: finite ambiguity cannot rescue unsupported predicted mass. -/
theorem tickG_eq_top_iff (A : O → S → ℝ) (s : S → ℝ) (C : O → ℝ) :
    tickG A s C = ⊤ ↔ Unsupported (predictedOutcome A s) C := by
  unfold tickG risk
  split_ifs with h
  · simp [h]
  · rw [← EReal.coe_add]
    exact iff_of_false (EReal.coe_ne_top _) h

/-- T3: CTau's raw Distribution permits negative rationals; for nonnegative
predictions its nonzero summation agrees with the positive-mass definition. -/
theorem risk_eq_classRisk (o C : CTauClassPreference.Distribution)
    (ho : ∀ x, 0 ≤ o x) :
    risk (fun x => (o x : ℝ)) (fun x => (C x : ℝ)) =
      CTauClassPreference.classRisk o C := by
  have support : Unsupported (fun x => (o x : ℝ)) (fun x => (C x : ℝ)) ↔
      CTauClassPreference.Unsupported o C := by
    simp [Unsupported, CTauClassPreference.Unsupported]
  unfold risk CTauClassPreference.classRisk
  rw [support]
  split_ifs with h
  · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases zero : o x = 0
    · simp [zero]
    · have pos : 0 < o x := lt_of_le_of_ne (ho x) (Ne.symm zero)
      have realpos : 0 < (o x : ℝ) := by exact_mod_cast pos
      have cn : C x ≠ 0 := fun hc => h ⟨x, pos, hc⟩
      have cr : (C x : ℝ) ≠ 0 := by exact_mod_cast cn
      simp [zero, realpos, Real.log_div (ne_of_gt realpos) cr]

/-- T4b: putting the prediction in the preference port erases risk. -/
theorem risk_self (o : O → ℝ) : risk o o = 0 := by
  have supported : ¬ Unsupported o o := by
    rintro ⟨x, hx, hz⟩
    linarith
  simp [risk, supported, finiteRisk]

def deterministicA : Bool → Unit → ℝ := fun o _ => if o then 1 else 0
def certainState : Unit → ℝ := fun _ => 1
def uniformC : Bool → ℝ := fun _ => 1 / 2

private theorem control_prediction :
    predictedOutcome deterministicA certainState = fun o => if o then 1 else 0 := by
  funext o
  simp [predictedOutcome, deterministicA, certainState]

private theorem control_ambiguity : ambiguity deterministicA certainState = 0 := by
  apply ambiguity_point_mass
  intro x
  exact ⟨true, by intro o; cases o <;> simp [deterministicA]⟩

private theorem control_risk :
    risk (predictedOutcome deterministicA certainState) uniformC = (Real.log 2 : EReal) := by
  rw [control_prediction]
  have supported : ¬ Unsupported (fun o : Bool => if o then 1 else 0) uniformC := by
    simp [Unsupported, uniformC]
  simp [risk, supported, finiteRisk, uniformC]

/-- T4a/b concrete control: preferring the prediction gives G=0; the real
uniform preference gives G=log 2>0. Both are probability distributions. -/
theorem preference_changes_G :
    tickG deterministicA certainState (predictedOutcome deterministicA certainState) = 0 ∧
    tickG deterministicA certainState uniformC = (Real.log 2 : EReal) ∧
    tickG deterministicA certainState (predictedOutcome deterministicA certainState) <
      tickG deterministicA certainState uniformC := by
  have positive : (0 : EReal) < (Real.log 2 : ℝ) := by
    exact_mod_cast Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  simp [tickG, risk_self, control_ambiguity, control_risk, positive]

/-- T4b: the real preference's risk is strictly positive, unlike self-risk. -/
theorem real_preference_risk_positive :
    0 < risk (predictedOutcome deterministicA certainState) uniformC := by
  rw [control_risk]
  exact_mod_cast Real.log_pos (show (1 : ℝ) < 2 by norm_num)

/-- T4c: any off-waiting predicted mass makes pre-horizon G infinite. -/
theorem before_horizon_top (A : CTauClassPreference.EndingClass → S → ℝ) (s : S → ℝ)
    (off : ∃ x, x ≠ CTauClassPreference.EndingClass.notYetEvaluated ∧
      0 < predictedOutcome A s x) :
    tickG A s (fun x => (CTauClassPreference.waitingPreference x : ℝ)) = ⊤ := by
  rw [tickG_eq_top_iff]
  obtain ⟨x, hx, pos⟩ := off
  refine ⟨x, pos, ?_⟩
  cases x <;> simp_all [CTauClassPreference.waitingPreference]

#print axioms ambiguity_nonneg
#print axioms ambiguity_point_mass
#print axioms tickG_eq_top_iff
#print axioms risk_eq_classRisk
#print axioms risk_self
#print axioms preference_changes_G
#print axioms real_preference_risk_positive
#print axioms before_horizon_top

end
end DarkTower.WarMachine.PolicyExpectedFreeEnergy
