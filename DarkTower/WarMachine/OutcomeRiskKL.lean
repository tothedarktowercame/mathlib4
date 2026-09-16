import DarkTower.WarMachine.Holes

/-! The risk term of expected free energy as an exact extended-real
KL divergence, per Da Costa et al. 2020 eq. (44)
(`futon2/holes/labs/wm-contract/refs/dacosta2020.txt:1418-1423`):
`risk(π) := D_KL[Q(o|π) ‖ C]`.  Unlike `Holes.predictiveOutcomeRisk`, which is
real-valued and therefore restricted to preferences strictly positive on the
predictive support, `outcomeRisk` represents the infinite case
(`Q(o|π) > 0` with `C(o) = 0`) as `⊤` instead of excluding it. -/

namespace DarkTower.WarMachine.OutcomeRiskKL

open Holes

noncomputable section

/-! ## Definition -/

/-- The finite branch of the risk term: the Gibbs sum over listed predictive
outcomes with positive predictive mass.  Zero-mass outcomes contribute `0`
(the standard `0 · log 0 = 0` convention, which `Real.log 0 = 0` supplies). -/
def finiteOutcomeRisk {PolicyIndex : Type*} {Obs : Vertex → Type*}
    (Q : PredictiveOutcomeKernel PolicyIndex Obs)
    (C : PreferenceDistribution Obs) (π : PolicyIndex) : ℝ :=
  (((Q.support π).filter (fun o => decide (0 < Q.mass π o))).map
    (fun o => Q.mass π o * Real.log (Q.mass π o / C.mass () o))).sum

/-- The risk term `D_KL[Q(o∣π) ‖ C]` of Da Costa et al. 2020 eq. (44)
(`refs/dacosta2020.txt:1418-1423`), valued in `EReal` so that an outcome with
positive predictive mass and zero preferred mass contributes `⊤` rather than
being excluded. -/
def outcomeRisk {PolicyIndex : Type*} {Obs : Vertex → Type*}
    (Q : PredictiveOutcomeKernel PolicyIndex Obs)
    (C : PreferenceDistribution Obs) (π : PolicyIndex) : EReal :=
  if (Q.support π).any (fun o => decide (0 < Q.mass π o ∧ C.mass () o = 0)) then ⊤
  else ↑(finiteOutcomeRisk Q C π)

/-! ## List helper lemmas -/

/-- Terms falsifying the filter predicate and equal to zero do not change the
sum. -/
theorem list_map_sum_filter_eq_of_zero {α : Type*} (f : α → ℝ) (l : List α)
    (p : α → Bool) (h0 : ∀ o ∈ l, p o = false → f o = 0) :
    (l.map f).sum = ((l.filter p).map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    by_cases hp : p a = true
    · rw [List.map_cons, List.sum_cons, List.filter_cons, if_pos hp,
        List.map_cons, List.sum_cons,
        ih (fun o ho hc => h0 o (List.mem_cons_of_mem _ ho) hc)]
    · have hp' : p a = false := by
        cases h : p a
        · rfl
        · exact absurd h hp
      rw [List.map_cons, List.sum_cons, List.filter_cons, if_neg hp,
        h0 a (List.mem_cons_self ..) hp',
        ih (fun o ho hc => h0 o (List.mem_cons_of_mem _ ho) hc)]
      ring

/-- Filtering out entries never increases a sum of nonnegative terms. -/
theorem list_map_sum_filter_le {α : Type*} (f : α → ℝ) (l : List α) (p : α → Bool)
    (hn : ∀ o, 0 ≤ f o) : ((l.filter p).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    by_cases hp : p a = true
    · rw [List.filter_cons, if_pos hp, List.map_cons, List.map_cons,
        List.sum_cons, List.sum_cons]
      exact add_le_add (le_refl _) ih
    · have hp' : p a = false := by
        cases h : p a
        · rfl
        · exact absurd h hp
      rw [List.filter_cons, if_neg hp, List.map_cons, List.sum_cons]
      calc ((List.filter p as).map f).sum ≤ (as.map f).sum := ih
        _ ≤ f a + (as.map f).sum := by linarith [hn a]

/-- Pointwise order sums to order of sums. -/
theorem list_map_sum_le_of_forall {α : Type*} (f g : α → ℝ) (l : List α)
    (h : ∀ o ∈ l, f o ≤ g o) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact add_le_add (h a (List.mem_cons_self ..))
      (ih (fun o ho => h o (List.mem_cons_of_mem _ ho)))

/-- Pointwise subtraction sums to the difference of the sums. -/
theorem list_map_sum_sub {α : Type*} (f g : α → ℝ) (l : List α) :
    (l.map (fun o => f o - g o)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      List.sum_cons, ih]
    ring

/-- A sum of nonnegative terms is nonnegative. -/
theorem list_map_sum_nonneg {α : Type*} (f : α → ℝ) (l : List α)
    (hn : ∀ o, 0 ≤ f o) : 0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, List.sum_cons]
    exact add_nonneg (hn a) ih

open scoped Classical in
/-- Erasing one listed element of a `Nodup` list (matched by an equality
predicate) removes exactly its term from the sum. -/
theorem list_map_sum_eraseP {α : Type*} (f : α → ℝ) {a : α} {t : List α}
    (hmem : a ∈ t) (hnd : t.Nodup) :
    ((t.eraseP (fun x => decide (x = a))).map f).sum + f a = (t.map f).sum := by
  classical
  induction t with
  | nil => cases hmem
  | cons b ts ih =>
    by_cases hab : a = b
    · subst hab
      rw [List.eraseP_cons_of_pos (by simp), List.map_cons, List.sum_cons]
      ring
    · have hmem' : a ∈ ts := (List.mem_cons.mp hmem).resolve_left hab
      rw [List.eraseP_cons_of_neg (by simp [Ne.symm hab]), List.map_cons, List.map_cons,
        List.sum_cons, List.sum_cons, add_assoc,
        ih hmem' ((List.nodup_cons.mp hnd).2)]

open scoped Classical in
/-- A sum of nonnegative terms over a `Nodup` list is bounded by the sum over
any `Nodup` list off which the summand vanishes. -/
theorem list_map_sum_le_of_zero_off {α : Type*} (f : α → ℝ) (l t : List α)
    (hlnd : l.Nodup) (htnd : t.Nodup) (hn : ∀ o, 0 ≤ f o)
    (hz : ∀ o ∈ l, o ∉ t → f o = 0) :
    (l.map f).sum ≤ (t.map f).sum := by
  classical
  induction l generalizing t with
  | nil => exact list_map_sum_nonneg f t hn
  | cons a as ih =>
    have hasnd : as.Nodup := (List.nodup_cons.mp hlnd).2
    have hanotas : a ∉ as := (List.nodup_cons.mp hlnd).1
    by_cases ha : a ∈ t
    · have hnd' : (t.eraseP (fun x => decide (x = a))).Nodup :=
        List.Nodup.eraseP _ htnd
      have hzero : ∀ o ∈ as, o ∉ t.eraseP (fun x => decide (x = a)) → f o = 0 := by
        intro o hoas ho
        by_cases hot : o ∈ t
        · rcases eq_or_ne o a with rfl | hne
          · exact absurd hoas hanotas
          · exact absurd
              ((List.mem_eraseP_of_neg (by simpa using hne)).mpr hot) ho
        · exact hz o (List.mem_cons_of_mem _ hoas) hot
      calc ((a :: as).map f).sum = f a + (as.map f).sum := rfl
        _ ≤ f a + ((t.eraseP (fun x => decide (x = a))).map f).sum :=
            add_le_add (le_refl _) (ih _ hasnd hnd' hzero)
        _ = ((t.eraseP (fun x => decide (x = a))).map f).sum + f a := by ring
        _ = (t.map f).sum := list_map_sum_eraseP f ha htnd
    · have hfa : f a = 0 := hz a (List.mem_cons_self ..) ha
      show f a + (as.map f).sum ≤ (t.map f).sum
      rw [hfa, zero_add]
      exact ih t hasnd htnd (fun o ho ho' => hz o (List.mem_cons_of_mem _ ho) ho')

/-! ## Agreement with the real-valued special case -/

/-- When the preference distribution is strictly positive on the predictive
support, `outcomeRisk` agrees with `Holes.predictiveOutcomeRisk`; the
real-valued formula is the finite special case. -/
theorem outcomeRisk_eq_predictiveOutcomeRisk {PolicyIndex : Type*} {Obs : Vertex → Type*}
    (Q : PredictiveOutcomeKernel PolicyIndex Obs) (C : PreferenceDistribution Obs)
    (h : ∀ π o, o ∈ Q.support π → 0 < C.mass () o) (π : PolicyIndex) :
    outcomeRisk Q C π = ↑(Holes.predictiveOutcomeRisk Q C h π) := by
  have hf : ¬ ((Q.support π).any
      (fun o => decide (0 < Q.mass π o ∧ C.mass () o = 0))) := by
    intro hany
    obtain ⟨o, ho, htrue⟩ := List.any_eq_true.mp hany
    have hc0 : C.mass () o = 0 := by
      have := by simpa using htrue
      exact this.2
    exact absurd (h π o ho) (by rw [hc0]; exact lt_irrefl 0)
  have h0 : ∀ o ∈ Q.support π, decide (0 < Q.mass π o) = false →
      Q.mass π o * Real.log (Q.mass π o / C.mass () o) = 0 := by
    intro o ho hfalse
    have hnq : ¬ 0 < Q.mass π o := by simpa using hfalse
    have hq0 : Q.mass π o = 0 := le_antisymm (not_lt.mp hnq) (Q.nonnegative π o)
    rw [hq0, zero_mul]
  rw [outcomeRisk, if_neg hf, finiteOutcomeRisk]
  simp only [Holes.predictiveOutcomeRisk]
  rw [← list_map_sum_filter_eq_of_zero
    (fun o => Q.mass π o * Real.log (Q.mass π o / C.mass () o)) (Q.support π)
    (fun o => decide (0 < Q.mass π o)) h0]

/-! ## The infinite case -/

/-- `outcomeRisk` is infinite exactly when some listed predictive outcome has
positive predictive mass and zero preferred mass. -/
theorem outcomeRisk_eq_top_iff {PolicyIndex : Type*} {Obs : Vertex → Type*}
    (Q : PredictiveOutcomeKernel PolicyIndex Obs) (C : PreferenceDistribution Obs)
    (π : PolicyIndex) :
    outcomeRisk Q C π = ⊤ ↔ ∃ o ∈ Q.support π, 0 < Q.mass π o ∧ C.mass () o = 0 := by
  constructor
  · intro h
    by_contra hc
    have hf : ¬ ((Q.support π).any
        (fun o => decide (0 < Q.mass π o ∧ C.mass () o = 0))) := by
      intro hany
      obtain ⟨o, ho, htrue⟩ := List.any_eq_true.mp hany
      exact hc ⟨o, ho, by simpa using htrue⟩
    rw [outcomeRisk, if_neg hf] at h
    exact EReal.coe_ne_top _ h
  · rintro ⟨o, ho, h1, h2⟩
    have hany : ((Q.support π).any
        (fun o' => decide (0 < Q.mass π o' ∧ C.mass () o' = 0))) = true :=
      List.any_eq_true.mpr ⟨o, ho, by simpa using And.intro h1 h2⟩
    rw [outcomeRisk, if_pos hany]

/-! ## Nonnegativity (Gibbs' inequality) -/

/-- Per-term Gibbs bound: for `0 < q` and `0 < c`, `q - c ≤ q · log (q / c)`. -/
theorem klTerm_ge_sub {q c : ℝ} (hq : 0 < q) (hc : 0 < c) :
    q - c ≤ q * Real.log (q / c) := by
  have hpos : 0 < c / q := by positivity
  have h1 : Real.log (c / q) ≤ c / q - 1 := Real.log_le_sub_one_of_pos hpos
  have h2 : Real.log (q / c) + Real.log (c / q) = 0 := by
    rw [Real.log_div hq.ne' hc.ne', Real.log_div hc.ne' hq.ne']
    ring
  have hnq : (-q : ℝ) ≤ 0 := by nlinarith
  have h4 := mul_le_mul_of_nonpos_right h1 hnq
  calc q - c = (-q) * (c / q - 1) := by field_simp; ring
    _ ≤ (-q) * Real.log (c / q) := by nlinarith [h4]
    _ = q * Real.log (q / c) := by linear_combination -q * h2

/-- `D_KL[Q(o∣π) ‖ C] ≥ 0`: Gibbs' inequality on the finite branch, immediate
on the infinite branch.  Uses normalisation of both kernel rows and
nonnegativity of `C`. -/
theorem outcomeRisk_nonneg {PolicyIndex : Type*} {Obs : Vertex → Type*}
    (Q : PredictiveOutcomeKernel PolicyIndex Obs) (C : PreferenceDistribution Obs)
    (π : PolicyIndex) : (0 : EReal) ≤ outcomeRisk Q C π := by
  by_cases hany : (Q.support π).any
      (fun o => decide (0 < Q.mass π o ∧ C.mass () o = 0))
  · rw [outcomeRisk, if_pos hany]
    exact le_top
  · rw [outcomeRisk, if_neg hany]
    refine EReal.coe_le_coe ?_
    have hqpos : ∀ o ∈ (Q.support π).filter (fun o => decide (0 < Q.mass π o)),
        0 < Q.mass π o := by
      intro o ho
      simpa using (List.mem_filter.mp ho).2
    have hfin : ∀ o ∈ (Q.support π).filter (fun o => decide (0 < Q.mass π o)),
        0 < C.mass () o := by
      intro o ho
      have hmem := (List.mem_filter.mp ho).1
      have hq := hqpos o ho
      have hne : C.mass () o ≠ 0 := by
        intro h0
        exact hany (List.any_eq_true.mpr ⟨o, hmem, by
          simp only [decide_eq_true_eq]
          exact ⟨hq, h0⟩⟩)
      rcases lt_or_eq_of_le (C.nonnegative () o) with h | h
      · exact h
      · exact absurd h.symm hne
    -- Sum of predictive masses over the filtered support is one.
    have hq1 : (((Q.support π).filter (fun o => decide (0 < Q.mass π o))).map
        (Q.mass π)).sum = 1 := by
      rw [← list_map_sum_filter_eq_of_zero (Q.mass π) (Q.support π)
        (fun o => decide (0 < Q.mass π o)) ?_]
      · exact Q.normalised π
      · intro o ho hfalse
        have hnq : ¬ 0 < Q.mass π o := by simpa using hfalse
        exact le_antisymm (not_lt.mp hnq) (Q.nonnegative π o)
    -- Sum of preferred masses over the filtered support is at most one.
    have hc1 : (((Q.support π).filter (fun o => decide (0 < Q.mass π o))).map
        (fun o => C.mass () o)).sum ≤ 1 := by
      have h1 : (((Q.support π).filter (fun o => decide (0 < Q.mass π o))).map
          (fun o => C.mass () o)).sum ≤
          ((Q.support π).map (fun o => C.mass () o)).sum :=
        list_map_sum_filter_le _ _ _ (fun o => C.nonnegative () o)
      have h2 : ((Q.support π).map (fun o => C.mass () o)).sum ≤
          ((C.support ()).map (C.mass ())).sum :=
        list_map_sum_le_of_zero_off _ (Q.support π) (C.support ())
          (Q.support_nodup π) (C.support_nodup ()) (fun o => C.nonnegative () o)
          (fun o _ ho => C.mass_eq_zero_of_not_mem () o ho)
      exact (h1.trans h2).trans_eq (C.normalised ())
    -- Gibbs per term, then sum.
    have hterm : ∀ o ∈ (Q.support π).filter (fun o => decide (0 < Q.mass π o)),
        Q.mass π o - C.mass () o ≤
          Q.mass π o * Real.log (Q.mass π o / C.mass () o) :=
      fun o ho => klTerm_ge_sub (hqpos o ho) (hfin o ho)
    have hsum := list_map_sum_le_of_forall (fun o => Q.mass π o - C.mass () o)
      (fun o => Q.mass π o * Real.log (Q.mass π o / C.mass () o))
      ((Q.support π).filter (fun o => decide (0 < Q.mass π o))) hterm
    rw [list_map_sum_sub, hq1] at hsum
    simp only [finiteOutcomeRisk]
    have hc1' : ((List.filter (fun o => decide (0 < Q.mass π o)) (Q.support π)).map
        (C.mass ())).sum ≤ 1 := hc1
    linarith [hsum, hc1']

/-! ## Fixtures -/

/-- Two-point organisation observation carrier for the fixtures; all other
vertices are named-empty. -/
inductive FixtureOrg where
  | a | b
  deriving DecidableEq

/-- Tagged observation family for the fixtures. -/
def FixtureObs : Vertex → Type
  | .nouns => Empty
  | .verbs => Empty
  | .organization => FixtureOrg
  | .evidence => Empty

/-- The outcome `a` of the fixture carrier. -/
def outcomeA : Outcome FixtureObs := ⟨.organization, .a⟩

/-- The outcome `b` of the fixture carrier. -/
def outcomeB : Outcome FixtureObs := ⟨.organization, .b⟩

/-- `δ_a` as a preference distribution: all mass on `a`. -/
noncomputable def cDeltaA : PreferenceDistribution FixtureObs where
  support := fun _ => [outcomeA]
  mass := fun _ o => match o with
    | ⟨.organization, .a⟩ => 1
    | _ => 0
  nonnegative := by intro _ o; rcases o with ⟨v, o⟩; cases v <;> cases o <;> norm_num
  support_nodup := by intro; simp [outcomeA]
  mass_eq_zero_of_not_mem := by
    intro _ o h
    rcases o with ⟨v, o⟩; cases v <;> cases o <;> simp_all [outcomeA]
  normalised := by intro; norm_num [outcomeA]

/-- `δ_b` as a preference distribution: all mass on `b`. -/
noncomputable def cDeltaB : PreferenceDistribution FixtureObs where
  support := fun _ => [outcomeB]
  mass := fun _ o => match o with
    | ⟨.organization, .b⟩ => 1
    | _ => 0
  nonnegative := by intro _ o; rcases o with ⟨v, o⟩; cases v <;> cases o <;> norm_num
  support_nodup := by intro; simp [outcomeB]
  mass_eq_zero_of_not_mem := by
    intro _ o h
    rcases o with ⟨v, o⟩; cases v <;> cases o <;> simp_all [outcomeB]
  normalised := by intro; norm_num [outcomeB]

/-- `δ_a` as a predictive kernel, with the declared support additionally
listing the zero-mass outcome `b`: the padding case of the audit. -/
noncomputable def qPad : PredictiveOutcomeKernel Unit FixtureObs where
  support := fun _ => [outcomeA, outcomeB]
  mass := fun _ o => match o with
    | ⟨.organization, .a⟩ => 1
    | _ => 0
  nonnegative := by intro _ o; rcases o with ⟨v, o⟩; cases v <;> cases o <;> norm_num
  support_nodup := by intro; simp [outcomeA, outcomeB]
  mass_eq_zero_of_not_mem := by
    intro _ o h
    rcases o with ⟨v, o⟩; cases v <;> cases o <;> simp_all [outcomeA, outcomeB]
  normalised := by intro; norm_num [outcomeA, outcomeB]

/-- `δ_a` as a predictive kernel with minimal support. -/
noncomputable def qDeltaA : PredictiveOutcomeKernel Unit FixtureObs where
  support := fun _ => [outcomeA]
  mass := fun _ o => match o with
    | ⟨.organization, .a⟩ => 1
    | _ => 0
  nonnegative := by intro _ o; rcases o with ⟨v, o⟩; cases v <;> cases o <;> norm_num
  support_nodup := by intro; simp [outcomeA]
  mass_eq_zero_of_not_mem := by
    intro _ o h
    rcases o with ⟨v, o⟩; cases v <;> cases o <;> simp_all [outcomeA]
  normalised := by intro; norm_num [outcomeA]

/-- Fixture (a), padding case: `Q = δ_a` whose declared support additionally
lists the zero-mass outcome `b`, with `C(b) = 0` (all `C`-mass is on `a`).
The extended-real divergence is exactly `0`, where the real-valued
construction of `Holes.predictiveOutcomeRisk` is blocked by `C(b) = 0`. -/
theorem outcomeRisk_padding_delta : outcomeRisk qPad cDeltaA () = 0 := by
  have hf : ¬ ((qPad.support ()).any
      (fun o => decide (0 < qPad.mass () o ∧ cDeltaA.mass () o = 0))) := by
    intro hany
    obtain ⟨o, ho, htrue⟩ := List.any_eq_true.mp hany
    have hp := by simpa using htrue
    rcases o with ⟨v, o⟩
    cases v <;> cases o <;> simp_all [qPad, cDeltaA, outcomeA, outcomeB]
  rw [outcomeRisk, if_neg hf, finiteOutcomeRisk]
  simp [qPad, cDeltaA, outcomeA, outcomeB]

/-- Fixture (b), disjoint point masses: `Q = δ_a`, `C = δ_b` with `a ≠ b`.
The divergence is infinite. -/
theorem outcomeRisk_disjoint_deltas : outcomeRisk qDeltaA cDeltaB () = ⊤ := by
  have hany : ((qDeltaA.support ()).any
      (fun o => decide (0 < qDeltaA.mass () o ∧ cDeltaB.mass () o = 0))) = true :=
    List.any_eq_true.mpr ⟨outcomeA, by simp [qDeltaA, outcomeA], by
      simp only [decide_eq_true_eq]
      constructor
      · norm_num [qDeltaA, outcomeA]
      · simp [cDeltaB, outcomeA]⟩
  rw [outcomeRisk, if_pos hany]

end
end DarkTower.WarMachine.OutcomeRiskKL
