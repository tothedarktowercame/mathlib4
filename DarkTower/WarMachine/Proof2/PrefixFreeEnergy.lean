import DarkTower.WarMachine.ExactBeliefTrajectory

/-!
# Observed-prefix variational free energy

This relation sums filtering VFE on the supplied step inputs. It does not
establish historical admission or continuity, nor a floating-point refinement.
The algebra permits an empty sum; production admission separately requires a
nonempty prefix. No finiteness assumption on the individual VFE is imposed.
-/
namespace DarkTower.WarMachine.Proof2.PrefixFreeEnergy

open scoped BigOperators
open PolicyVariationalFreeEnergy ExactBeliefTrajectory

private theorem coe_sum_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (↑(∑ i ∈ s, f i) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert, ha, EReal.coe_add, ih]

/-- A finite sum of extended values above finite lower bounds attains the
sum of the bounds exactly when every summand attains its own bound. -/
private theorem sum_eq_bounds_iff {ι : Type*} (s : Finset ι)
    (f : ι → EReal) (b : ι → ℝ) (h : ∀ i ∈ s, (b i : EReal) ≤ f i) :
    ∑ i ∈ s, f i = (↑(∑ i ∈ s, b i) : EReal) ↔
      ∀ i ∈ s, f i = (b i : EReal) := by
  classical
  constructor
  · intro heq i hi
    apply le_antisymm _ (h i hi)
    by_contra hn
    have hlt : (b i : EReal) < f i := lt_of_not_ge hn
    have hrest : (↑(∑ j ∈ s.erase i, b j) : EReal) ≤ ∑ j ∈ s.erase i, f j := by
      rw [coe_sum_real]
      exact Finset.sum_le_sum fun j hj => h j (Finset.mem_of_mem_erase hj)
    have hbot : (∑ j ∈ s.erase i, f j) ≠ (⊥ : EReal) := by
      intro he
      rw [he] at hrest
      exact EReal.coe_ne_bot _ (le_bot_iff.mp hrest)
    have hstrict := EReal.add_lt_add_of_lt_of_le' hlt hrest hbot
      (fun _ hz => False.elim (EReal.coe_ne_top _ hz))
    rw [← EReal.coe_add, Finset.add_sum_erase _ _ hi,
      Finset.add_sum_erase _ _ hi, heq] at hstrict
    exact (lt_irrefl _ hstrict)
  · intro hall
    rw [coe_sum_real]
    exact Finset.sum_congr rfl hall

section PrefixTheorems

variable {S O : Type*} [Fintype S] [DecidableEq S] {n : ℕ}

/-- H4 prefix F, without averaging or temperature scaling. Each step retains
its own likelihood, transition, prior belief, observation and posterior. -/
noncomputable def prefixVFE (A : Fin n → S → O → ℝ) (B : Fin n → S → S → ℝ)
    (o : Fin n → O) (sPrev q : Fin n → S → ℝ) : EReal :=
  ∑ i : Fin n, variationalFreeEnergy (fun x => A i x (o i))
    (predictedState (B i) (sPrev i)) (q i)

variable (A : Fin n → S → O → ℝ) (B : Fin n → S → S → ℝ)
  (o : Fin n → O) (sPrev q : Fin n → S → ℝ)
  (hA : ∀ i x, 0 ≤ A i x (o i))
  (hB : ∀ i s x, 0 ≤ B i s x)
  (hB1 : ∀ i s, ∑ x, B i s x = 1)
  (hp : ∀ i s, 0 ≤ sPrev i s)
  (hp1 : ∀ i, ∑ s, sPrev i s = 1)
  (hZ : ∀ i, 0 < observationProbability (A i) (B i) (o i) (sPrev i))
  (hq0 : ∀ i x, 0 ≤ q i x)
  (hq1 : ∀ i, ∑ x, q i x = 1)

include hA hB hB1 hp hp1 hZ hq0 hq1

/-- Summed B.2 lower bound, including the possibility of an infinite VFE. -/
theorem prefixVFE_ge_neg_log_evidence :
    (↑(∑ i : Fin n, -Real.log
      (observationProbability (A i) (B i) (o i) (sPrev i))) : EReal)
      ≤ prefixVFE A B o sPrev q := by
  rw [prefixVFE, coe_sum_real]
  apply Finset.sum_le_sum
  intro i _
  exact vfe_ge_neg_log_evidence _ _ _ (hA i)
    (predictedState_nonneg _ _ (hB i) (hp i))
    (predictedState_sum _ _ (hB1 i) (hp1 i)) (hq0 i) (hq1 i) (hZ i)

/-- Equality of the total forces equality at every step: no positive gap can
be cancelled by another step, and an infinite summand cannot attain the bound. -/
theorem prefixVFE_eq_neg_log_evidence_iff :
    prefixVFE A B o sPrev q =
      (↑(∑ i : Fin n, -Real.log
        (observationProbability (A i) (B i) (o i) (sPrev i))) : EReal)
      ↔ ∀ i, exactUpdate (A i) (B i) (o i) (sPrev i) = some (q i) := by
  unfold prefixVFE
  rw [sum_eq_bounds_iff]
  · simp only [Finset.mem_univ, forall_const]
    exact forall_congr' fun i => exactUpdate_minimises_vfe _ _ _ _
      (hA i) (hB i) (hB1 i) (hp i) (hp1 i) (hZ i) (q i) (hq0 i) (hq1 i)
  · intro i _
    exact vfe_ge_neg_log_evidence _ _ _ (hA i)
      (predictedState_nonneg _ _ (hB i) (hp i))
      (predictedState_sum _ _ (hB1 i) (hp1 i)) (hq0 i) (hq1 i) (hZ i)

/-- The exact-update equality case summed across the observed prefix. -/
theorem prefixVFE_exactUpdate_eq
    (hupdate : ∀ i, exactUpdate (A i) (B i) (o i) (sPrev i) = some (q i)) :
    prefixVFE A B o sPrev q =
      (↑(∑ i : Fin n, -Real.log
        (observationProbability (A i) (B i) (o i) (sPrev i))) : EReal) :=
  (prefixVFE_eq_neg_log_evidence_iff A B o sPrev q hA hB hB1 hp hp1 hZ hq0 hq1).mpr
    hupdate

end PrefixTheorems

/-! A synthetic two-step falsifier, not a live-record witness. -/
namespace TwoStep

noncomputable def likelihood (i : Fin 2) (_ : Unit) (o : Bool) : ℝ :=
  let p : ℝ := if i = 0 then 1 / 2 else 1 / 4
  if o then p else 1 - p

def transition (_ : Fin 2) (_ _ : Unit) : ℝ := 1
def belief (_ : Fin 2) (_ : Unit) : ℝ := 1
def observed (_ : Fin 2) : Bool := true

/-- Both observation rows are distributions, including the unobserved outcome. -/
theorem likelihood_normalized (i : Fin 2) :
    ∑ o : Bool, likelihood i () o = 1 := by
  fin_cases i <;> norm_num [likelihood]

/-- Each retained q is actually the exact update, not merely a convenient mass. -/
theorem updates (i : Fin 2) :
    exactUpdate (likelihood i) (transition i) (observed i) (belief i) =
      some (belief i) := by
  fin_cases i <;>
    norm_num [exactUpdate, observationProbability, predictedState,
      likelihood, transition, observed, belief] <;> rfl

noncomputable def stepF (i : Fin 2) : EReal :=
  variationalFreeEnergy (fun x => likelihood i x (observed i))
    (predictedState (transition i) (belief i)) (belief i)

theorem first_value : stepF 0 = (Real.log 2 : EReal) := by
  norm_num [stepF, variationalFreeEnergy, qsupport, likelihood, transition,
    observed, belief, predictedState, Real.log_div]

theorem last_value : stepF 1 = (Real.log 4 : EReal) := by
  norm_num [stepF, variationalFreeEnergy, qsupport, likelihood, transition,
    observed, belief, predictedState, Real.log_div]

/-- The total contains both summands; a singleton is not the definition. -/
theorem total_value : prefixVFE likelihood transition observed belief belief =
    ((Real.log 2 + Real.log 4 : ℝ) : EReal) := by
  change (∑ i : Fin 2, stepF i) = _
  rw [Fin.sum_univ_two, first_value, last_value, EReal.coe_add]

/-- Exact symbolic discrepancy when the last summand replaces the total. -/
theorem last_substitution_gap :
    (prefixVFE likelihood transition observed belief belief).toReal -
      (stepF 1).toReal = Real.log 2 := by
  rw [total_value, last_value]
  change (Real.log 2 + Real.log 4) - Real.log 4 = Real.log 2
  ring

/-- The discrepancy is strictly positive, so the proposed substitution is false. -/
theorem total_ne_last : prefixVFE likelihood transition observed belief belief ≠ stepF 1 := by
  intro h
  have hgap := last_substitution_gap
  rw [h, sub_self] at hgap
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : prefixVFE likelihood transition observed belief belief = stepF 1 := by
  simp only [total_ne_last]

end TwoStep

#print axioms coe_sum_real
#print axioms sum_eq_bounds_iff
#print axioms prefixVFE_ge_neg_log_evidence
#print axioms prefixVFE_eq_neg_log_evidence_iff
#print axioms prefixVFE_exactUpdate_eq
#print axioms TwoStep.likelihood_normalized
#print axioms TwoStep.updates
#print axioms TwoStep.first_value
#print axioms TwoStep.last_value
#print axioms TwoStep.total_value
#print axioms TwoStep.last_substitution_gap
#print axioms TwoStep.total_ne_last

end DarkTower.WarMachine.Proof2.PrefixFreeEnergy
