import DarkTower.WarMachine.Holes
import DarkTower.WarMachine.PreferenceRiskSeparation

/-! Finite cascade EFE: filtered guarded controls and a shared predictive joint.
This module is a mathematical model, not a correspondence claim about the live
machine. Interpretation provenance and parameter acquisition are external.
-/
namespace DarkTower.WarMachine.CascadeEFE
open Holes
open scoped BigOperators
noncomputable section

variable {X Y Z : Type*}

theorem kernel_sum [Fintype Y] (k : ProbabilityKernel X Y) (x : X) :
    ∑ y, k.mass x y = 1 := by
  classical
  let t : Finset Y := ⟨k.support x, k.support_nodup x⟩
  have h : ∑ y ∈ t, k.mass x y = 1 := by
    simpa [t, Finset.sum_mk] using k.normalised x
  rw [← h]
  symm
  apply Finset.sum_subset (Finset.subset_univ t)
  intro y _ hy
  exact k.mass_eq_zero_of_not_mem x y hy

/-- Full finite support is legitimate, including entries with zero mass. -/
def finiteKernel [Fintype Y] (m : X → Y → ℝ)
    (hn : ∀ x y, 0 ≤ m x y) (hs : ∀ x, ∑ y, m x y = 1) :
    ProbabilityKernel X Y where
  support := fun _ => Finset.univ.toList
  mass := m
  nonnegative := hn
  normalised := by intro x; simpa using hs x
  support_nodup := fun _ => Finset.nodup_toList _
  mass_eq_zero_of_not_mem := by simp

def point [Fintype X] [DecidableEq X] (x : X) : ProbabilityKernel Unit X :=
  finiteKernel (fun _ y => if y = x then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro; simp)

def push [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (b : ProbabilityKernel X Y) : ProbabilityKernel Unit Y :=
  finiteKernel (fun _ y => ∑ x, q.mass () x * b.mass x y)
    (by intros; exact Finset.sum_nonneg fun x _ => mul_nonneg (q.nonnegative () x) (b.nonnegative x _))
    (by intro; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, kernel_sum]; simpa using kernel_sum q ())

/-- Node membership is an explicit decidable input. Cascade.precedence is the
pair's precedence, not a second independently mutable ordering. -/
structure Policy (P : Type*) where
  cascade : Cascade P
  nodeDecidable : DecidablePred (· ∈ cascade.nodes)

def firing {P : Type*} (pi : Policy P) : List P :=
  letI := pi.nodeDecidable
  pi.cascade.precedence.filter (fun p => decide (p ∈ pi.cascade.nodes))

structure Model (P S O : Type*) where
  initial : ProbabilityKernel Unit S
  observation : ProbabilityKernel S O
  guard : P → S → Bool
  interpretation : P → Option (ProbabilityKernel S S)

/-- Resolve every firing entry before selection; a missing interpretation never
falls through to another rule. -/
def resolve {P S O : Type*} (m : Model P S O) :
    List P → Option (List (P × ProbabilityKernel S S))
  | [] => some []
  | p :: ps => match m.interpretation p, resolve m ps with
      | some b, some bs => some ((p,b) :: bs)
      | _, _ => none

def choose {P S O : Type*} [Fintype S] [DecidableEq S] (m : Model P S O)
    (bs : List (P × ProbabilityKernel S S)) (s : S) : ProbabilityKernel Unit S :=
  match bs with
  | [] => point s
  | (p,b) :: rest => if m.guard p s then
      { support := fun _ => b.support s
        mass := fun _ => b.mass s
        nonnegative := fun _ => b.nonnegative s
        normalised := fun _ => b.normalised s
        support_nodup := fun _ => b.support_nodup s
        mass_eq_zero_of_not_mem := fun _ => b.mass_eq_zero_of_not_mem s }
    else choose m rest s

/-- EXTRAPOLATION 3: prediction evaluates guards on hidden state, while enactment
uses information state. They coincide only for guards reading observed facts.
Uninterpreted firing patterns refuse before any guard is evaluated. -/
def policyKernel {P S O : Type*} [Fintype S] [DecidableEq S]
    (m : Model P S O) (pi : Policy P) : Option (ProbabilityKernel S S) :=
  match resolve m (firing pi) with
  | none => none
  | some bs => some {
         support := fun s => (choose m bs s).support ()
         mass := fun s => (choose m bs s).mass ()
         nonnegative := fun s => (choose m bs s).nonnegative ()
         normalised := fun s => (choose m bs s).normalised ()
         support_nodup := fun s => (choose m bs s).support_nodup ()
         mass_eq_zero_of_not_mem := fun s => (choose m bs s).mass_eq_zero_of_not_mem () }

def prediction [Fintype X] (q : ProbabilityKernel Unit X)
    (b : ProbabilityKernel X X) : ℕ → ProbabilityKernel Unit X
  | 0 => q
  | t + 1 => push (prediction q b t) b

def joint [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (a : ProbabilityKernel X Y) : ProbabilityKernel Unit (X × Y) :=
  finiteKernel (fun _ z => q.mass () z.1 * a.mass z.1 z.2)
    (by intro _ z; exact mul_nonneg (q.nonnegative () z.1) (a.nonnegative z.1 z.2))
    (by intro; rw [Fintype.sum_prod_type]; simp_rw [← Finset.mul_sum, kernel_sum]; simpa using kernel_sum q ())

theorem prediction_normalised [Fintype X] (q : ProbabilityKernel Unit X)
    (b : ProbabilityKernel X X) (t : ℕ) : ∑ s, (prediction q b t).mass () s = 1 :=
  kernel_sum _ _

theorem joint_normalised [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (a : ProbabilityKernel X Y) : ∑ z, (joint q a).mass () z = 1 := kernel_sum _ _

theorem outcome_normalised [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (a : ProbabilityKernel X Y) : ∑ o, (push q a).mass () o = 1 := kernel_sum _ _

/-- Zero mass contributes zero; preferred zero is checked by riskAdmissible. -/
def klTerm (p c : ℝ) : ℝ := if p = 0 then 0 else p * Real.log (p / c)

def entropy [Fintype X] (p : X → ℝ) : ℝ := -∑ x, if p x = 0 then 0 else p x * Real.log (p x)

def ambiguity [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (a : ProbabilityKernel X Y) : ℝ := ∑ s, q.mass () s * entropy (a.mass s)

def risk [Fintype Y] (q c : ProbabilityKernel Unit Y)
    (_h : PreferenceRiskSeparation.riskAdmissible q c) : ℝ :=
  ∑ o, klTerm (q.mass () o) (c.mass () o)

def pragmaticCost [Fintype Y] (q c : ProbabilityKernel Unit Y) : ℝ :=
  -∑ o, if q.mass () o = 0 then 0 else q.mass () o * Real.log (c.mass () o)

def information [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (a : ProbabilityKernel X Y) : ℝ :=
  ∑ z : X × Y, if 0 < (joint q a).mass () z then
    (joint q a).mass () z * Real.log
      ((joint q a).mass () z / (q.mass () z.1 * (push q a).mass () z.2)) else 0

def stepG [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (a : ProbabilityKernel X Y) (c : ProbabilityKernel Unit Y)
    (h : PreferenceRiskSeparation.riskAdmissible (push q a) c) : ℝ :=
  risk (push q a) c h + ambiguity q a

theorem zero_mass_term (c : ℝ) : klTerm 0 c = 0 := by simp [klTerm]

theorem risk_domain (q c : ProbabilityKernel Unit Y) (y : Y)
    (hq : q.mass () y ≠ 0) (hc : c.mass () y = 0) :
    ¬ PreferenceRiskSeparation.riskAdmissible q c := by
  apply PreferenceRiskSeparation.preferred_zero_refuses q c () y _ hq hc
  by_contra hn
  exact hq (q.mass_eq_zero_of_not_mem () y hn)

theorem entropy_eq [Fintype X] (p : X → ℝ) :
    entropy p = -∑ x, p x * Real.log (p x) := by
  unfold entropy
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with h <;> simp_all

theorem klTerm_expand {p c : ℝ} (_hp : 0 ≤ p) (hc : p ≠ 0 → 0 < c) :
    klTerm p c = p * Real.log p - p * Real.log c := by
  by_cases h : p = 0
  · simp [klTerm, h]
  · rw [klTerm, if_neg h, Real.log_div h (ne_of_gt (hc h))]
    ring

theorem klTerm_lower {p c : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c)
    (hpc : p ≠ 0 → 0 < c) : p - c ≤ klTerm p c := by
  by_cases h : p = 0
  · simp [h, klTerm]; exact hc
  · have pp : 0 < p := lt_of_le_of_ne hp (Ne.symm h)
    have cc := hpc h
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos pp cc)
    have hm := mul_le_mul_of_nonneg_left hl hp
    rw [klTerm, if_neg h]
    convert hm using 1
    field_simp

theorem finite_kl_nonnegative [Fintype X] (p c : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hc : ∀ x, 0 ≤ c x)
    (sp : ∑ x, p x = 1) (sc : ∑ x, c x = 1)
    (hpc : ∀ x, p x ≠ 0 → 0 < c x) : 0 ≤ ∑ x, klTerm (p x) (c x) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ => klTerm_lower (hp x) (hc x) (hpc x))
  simpa [Finset.sum_sub_distrib, sp, sc] using h

theorem kernel_mass_le_one [Fintype Y] (k : ProbabilityKernel X Y) (x : X) (y : Y) :
    k.mass x y ≤ 1 := by
  classical
  have h := Finset.single_le_sum (fun z (_ : z ∈ Finset.univ) => k.nonnegative x z)
    (Finset.mem_univ y)
  simpa [kernel_sum] using h

theorem entropy_nonnegative [Fintype Y] (k : ProbabilityKernel X Y) (x : X) :
    0 ≤ entropy (k.mass x) := by
  rw [entropy_eq]
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro y _
  exact mul_nonpos_of_nonneg_of_nonpos (k.nonnegative x y)
    (Real.log_nonpos (k.nonnegative x y) (kernel_mass_le_one k x y))

theorem ambiguity_nonnegative [Fintype X] [Fintype Y]
    (q : ProbabilityKernel Unit X) (a : ProbabilityKernel X Y) : 0 ≤ ambiguity q a := by
  exact Finset.sum_nonneg fun s _ => mul_nonneg (q.nonnegative () s) (entropy_nonnegative a s)

theorem risk_nonnegative [Fintype Y] (q c : ProbabilityKernel Unit Y)
    (h : PreferenceRiskSeparation.riskAdmissible q c) : 0 ≤ risk q c h := by
  apply finite_kl_nonnegative _ _ (q.nonnegative ()) (c.nonnegative ()) (kernel_sum q ()) (kernel_sum c ())
  intro y hy
  apply h () y _ hy
  by_contra hn
  exact hy (q.mass_eq_zero_of_not_mem () y hn)

theorem stepG_nonnegative [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (a : ProbabilityKernel X Y) (c : ProbabilityKernel Unit Y)
    (h : PreferenceRiskSeparation.riskAdmissible (push q a) c) : 0 ≤ stepG q a c h :=
  add_nonneg (risk_nonnegative _ _ h) (ambiguity_nonnegative q a)

theorem joint_le_outcome [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (a : ProbabilityKernel X Y) (s : X) (o : Y) :
    (joint q a).mass () (s,o) ≤ (push q a).mass () o := by
  classical
  exact Finset.single_le_sum (fun x _ => mul_nonneg (q.nonnegative () x) (a.nonnegative x o))
    (Finset.mem_univ s)

theorem positive_joint_factors [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (a : ProbabilityKernel X Y) (s : X) (o : Y)
    (h : 0 < (joint q a).mass () (s,o)) :
    0 < q.mass () s ∧ 0 < a.mass s o ∧ 0 < (push q a).mass () o := by
  have hprod : 0 < q.mass () s * a.mass s o := h
  have hq := q.nonnegative () s
  have ha := a.nonnegative s o
  exact ⟨by nlinarith, by nlinarith, lt_of_lt_of_le h (joint_le_outcome q a s o)⟩

theorem information_term [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (a : ProbabilityKernel X Y) (s : X) (o : Y) :
    (if 0 < (joint q a).mass () (s,o) then
      (joint q a).mass () (s,o) * Real.log
        ((joint q a).mass () (s,o) / (q.mass () s * (push q a).mass () o)) else 0) =
    q.mass () s * (a.mass s o * Real.log (a.mass s o)) -
      (q.mass () s * a.mass s o) * Real.log ((push q a).mass () o) := by
  by_cases h : 0 < (joint q a).mass () (s,o)
  · rw [if_pos h]
    obtain ⟨hq, ha, ho⟩ := positive_joint_factors q a s o h
    change (q.mass () s * a.mass s o) * Real.log
      ((q.mass () s * a.mass s o) / (q.mass () s * (push q a).mass () o)) = _
    rw [Real.log_div (ne_of_gt (mul_pos hq ha)) (ne_of_gt (mul_pos hq ho)),
      Real.log_mul (ne_of_gt hq) (ne_of_gt ha), Real.log_mul (ne_of_gt hq) (ne_of_gt ho)]
    ring
  · rw [if_neg h]
    have hz : q.mass () s * a.mass s o = 0 :=
      le_antisymm (le_of_not_gt h) (mul_nonneg (q.nonnegative () s) (a.nonnegative s o))
    rw [← mul_assoc, hz]; simp

theorem information_entropy_identity [Fintype X] [Fintype Y]
    (q : ProbabilityKernel Unit X) (a : ProbabilityKernel X Y) :
    information q a = entropy ((push q a).mass ()) - ambiguity q a := by
  unfold information
  rw [Fintype.sum_prod_type]
  simp_rw [information_term, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  unfold ambiguity
  simp_rw [entropy_eq, mul_neg]
  rw [Finset.sum_neg_distrib]
  have hm : (∑ s, ∑ o, q.mass () s * a.mass s o * Real.log ((push q a).mass () o)) =
      ∑ o, (push q a).mass () o * Real.log ((push q a).mass () o) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro o _
    rw [← Finset.sum_mul]
    rfl
  rw [hm]
  ring

theorem information_nonnegative [Fintype X] [Fintype Y]
    (q : ProbabilityKernel Unit X) (a : ProbabilityKernel X Y) : 0 ≤ information q a := by
  let p := (joint q a).mass ()
  let c := fun z : X × Y => q.mass () z.1 * (push q a).mass () z.2
  have hc : ∀ z, 0 ≤ c z := fun z => mul_nonneg (q.nonnegative () z.1) ((push q a).nonnegative () z.2)
  have hsc : ∑ z, c z = 1 := by
    dsimp [c]; rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, kernel_sum]; simpa using kernel_sum q ()
  have hdom : ∀ z, p z ≠ 0 → 0 < c z := by
    intro z hz
    have hj : 0 < (joint q a).mass () z := lt_of_le_of_ne ((joint q a).nonnegative () z) (Ne.symm hz)
    obtain ⟨hq, _, ho⟩ := positive_joint_factors q a z.1 z.2 hj
    exact mul_pos hq ho
  have hk := finite_kl_nonnegative p c ((joint q a).nonnegative ()) hc (kernel_sum (joint q a) ()) hsc hdom
  convert hk using 1
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : p z = 0
  · have hn : ¬ 0 < (joint q a).mass () z := by change ¬ 0 < p z; simp [hz]
    simp [klTerm, hz, hn]
  · have hp : 0 < (joint q a).mass () z := lt_of_le_of_ne ((joint q a).nonnegative () z) (Ne.symm hz)
    simp only [klTerm, if_neg hz, if_pos hp]
    rfl

theorem risk_entropy_identity [Fintype Y] (q c : ProbabilityKernel Unit Y)
    (h : PreferenceRiskSeparation.riskAdmissible q c) :
    risk q c h = pragmaticCost q c - entropy (q.mass ()) := by
  have hd (y : Y) : q.mass () y ≠ 0 → 0 < c.mass () y := by
    intro hy; apply h () y _ hy
    by_contra hn; exact hy (q.mass_eq_zero_of_not_mem () y hn)
  unfold risk pragmaticCost
  simp_rw [klTerm_expand (q.nonnegative () _) (hd _), Finset.sum_sub_distrib]
  have he : (∑ o, if q.mass () o = 0 then 0 else q.mass () o * Real.log (c.mass () o)) =
      ∑ o, q.mass () o * Real.log (c.mass () o) := by
    apply Finset.sum_congr rfl
    intro o _; split_ifs with hz <;> simp_all
  rw [he, entropy_eq]; ring

theorem step_decomposition [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (a : ProbabilityKernel X Y) (c : ProbabilityKernel Unit Y)
    (h : PreferenceRiskSeparation.riskAdmissible (push q a) c) :
    stepG q a c h = pragmaticCost (push q a) c - information q a := by
  rw [stepG, risk_entropy_identity, information_entropy_identity]; ring

/-- Agreement with the existing risk functional, not a second admission rule. -/
theorem risk_eq_scalarKL [Fintype Y] (q c : ProbabilityKernel Unit Y)
    (h : PreferenceRiskSeparation.riskAdmissible q c) :
    risk q c h = (PreferenceRiskSeparation.scalarKL q c h).value () := by
  classical
  let t : Finset Y := ⟨q.support (), q.support_nodup ()⟩
  have hs : (∑ y ∈ t, klTerm (q.mass () y) (c.mass () y)) =
      (PreferenceRiskSeparation.scalarKL q c h).value () := by
    simp [t, Finset.sum_mk, PreferenceRiskSeparation.scalarKL, klTerm]
  rw [← hs]
  symm
  apply Finset.sum_subset (Finset.subset_univ t)
  intro y _ hy
  simp [q.mass_eq_zero_of_not_mem () y hy, klTerm]

theorem resolve_isSome_iff {P S O : Type*} (m : Model P S O) (ps : List P) :
    (resolve m ps).isSome = true ↔ ∀ p ∈ ps, (m.interpretation p).isSome = true := by
  induction ps with
  | nil => simp [resolve]
  | cons p ps ih =>
    cases hb : m.interpretation p <;> cases hr : resolve m ps <;>
      simp_all [resolve]

theorem policyKernel_isSome_iff {P S O : Type*} [Fintype S] [DecidableEq S]
    (m : Model P S O) (pi : Policy P) :
    (policyKernel m pi).isSome = true ↔
      ∀ p ∈ firing pi, (m.interpretation p).isSome = true := by
  rw [← resolve_isSome_iff]
  unfold policyKernel
  cases resolve m (firing pi) <;> rfl

theorem uninterpreted_refuses {P S O : Type*} [Fintype S] [DecidableEq S]
    (m : Model P S O) (pi : Policy P) (p : P)
    (hp : p ∈ firing pi) (hb : m.interpretation p = none) :
    policyKernel m pi = none := by
  have hn : ¬ (policyKernel m pi).isSome = true := by
    intro h
    have hh := (policyKernel_isSome_iff m pi).mp h p hp
    simp [hb] at hh
  cases he : policyKernel m pi <;> simp_all

theorem firing_members {P : Type*} (pi : Policy P) (p : P) :
    p ∈ firing pi ↔ p ∈ pi.cascade.precedence ∧ p ∈ pi.cascade.nodes := by
  letI := pi.nodeDecidable
  simp [firing]

/-- Time t : Fin T scores observation t+1, after one application for t=0. -/
def totalG [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (b : ProbabilityKernel X X) (a : ProbabilityKernel X Y) (T : ℕ)
    (c : Fin T → ProbabilityKernel Unit Y)
    (h : ∀ t : Fin T, PreferenceRiskSeparation.riskAdmissible
      (push (prediction q b (t.val + 1)) a) (c t)) : ℝ :=
  ∑ t : Fin T, stepG (prediction q b (t.val + 1)) a (c t) (h t)

theorem total_decomposition [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (b : ProbabilityKernel X X) (a : ProbabilityKernel X Y) (T : ℕ)
    (c : Fin T → ProbabilityKernel Unit Y)
    (h : ∀ t : Fin T, PreferenceRiskSeparation.riskAdmissible
      (push (prediction q b (t.val + 1)) a) (c t)) :
    totalG q b a T c h =
      (∑ t : Fin T, pragmaticCost (push (prediction q b (t.val + 1)) a) (c t)) -
      ∑ t : Fin T, information (prediction q b (t.val + 1)) a := by
  simp only [totalG, step_decomposition, Finset.sum_sub_distrib]

theorem totalG_nonnegative [Fintype X] [Fintype Y] (q : ProbabilityKernel Unit X)
    (b : ProbabilityKernel X X) (a : ProbabilityKernel X Y) (T : ℕ)
    (c : Fin T → ProbabilityKernel Unit Y)
    (h : ∀ t : Fin T, PreferenceRiskSeparation.riskAdmissible
      (push (prediction q b (t.val + 1)) a) (c t)) : 0 ≤ totalG q b a T c h :=
  Finset.sum_nonneg fun t _ => stepG_nonnegative _ _ _ (h t)

inductive Refusal where
  | missingInterpretation
  | inadmissibleRisk
  deriving DecidableEq

/-- Total mathematical scoring interface. Deciding riskAdmissible over real
parameters is noncomputable; this is not an executable numeric estimator. -/
def scoreCascade {P S O : Type*} [Fintype S] [Fintype O] [DecidableEq S]
    (m : Model P S O) (pi : Policy P) (T : ℕ)
    (c : Fin T → ProbabilityKernel Unit O) : Except Refusal ℝ := by
  classical
  exact match policyKernel m pi with
  | none => .error .missingInterpretation
  | some b => if h : ∀ t : Fin T, PreferenceRiskSeparation.riskAdmissible
      (push (prediction m.initial b (t.val + 1)) m.observation) (c t) then
      .ok (totalG m.initial b m.observation T c h)
    else .error .inadmissibleRisk

theorem joint_state_marginal [Fintype X] [Fintype Y]
    (q : ProbabilityKernel Unit X) (a : ProbabilityKernel X Y) (x : X) :
    (∑ y, (joint q a).mass () (x,y)) = q.mass () x := by
  change (∑ y, q.mass () x * a.mass x y) = _
  rw [← Finset.mul_sum, kernel_sum, mul_one]

theorem joint_outcome_marginal [Fintype X] [Fintype Y]
    (q : ProbabilityKernel Unit X) (a : ProbabilityKernel X Y) (y : Y) :
    (∑ x, (joint q a).mass () (x,y)) = (push q a).mass () y := rfl

/-- All the repaired kernel obligations hold for each predicted distribution.
The same obligations for joint and outcome are supplied by their kernel types. -/
theorem prediction_wellFormed [Fintype X] (q : ProbabilityKernel Unit X)
    (b : ProbabilityKernel X X) (t : ℕ) :
    (∀ x, 0 ≤ (prediction q b t).mass () x) ∧
    (∑ x, (prediction q b t).mass () x) = 1 ∧
    ((prediction q b t).support ()).Nodup ∧
    (∀ x, x ∉ (prediction q b t).support () → (prediction q b t).mass () x = 0) :=
  ⟨(prediction q b t).nonnegative (), kernel_sum _ _,
    (prediction q b t).support_nodup (), (prediction q b t).mass_eq_zero_of_not_mem ()⟩

-- Machine-readable theorem signatures and kernel-reported dependencies.
#check kernel_sum
#print axioms kernel_sum
#check prediction_normalised
#print axioms prediction_normalised
#check joint_normalised
#print axioms joint_normalised
#check outcome_normalised
#print axioms outcome_normalised
#check zero_mass_term
#print axioms zero_mass_term
#check risk_domain
#print axioms risk_domain
#check entropy_eq
#print axioms entropy_eq
#check klTerm_expand
#print axioms klTerm_expand
#check klTerm_lower
#print axioms klTerm_lower
#check finite_kl_nonnegative
#print axioms finite_kl_nonnegative
#check kernel_mass_le_one
#print axioms kernel_mass_le_one
#check entropy_nonnegative
#print axioms entropy_nonnegative
#check ambiguity_nonnegative
#print axioms ambiguity_nonnegative
#check risk_nonnegative
#print axioms risk_nonnegative
#check stepG_nonnegative
#print axioms stepG_nonnegative
#check joint_le_outcome
#print axioms joint_le_outcome
#check positive_joint_factors
#print axioms positive_joint_factors
#check information_term
#print axioms information_term
#check information_entropy_identity
#print axioms information_entropy_identity
#check information_nonnegative
#print axioms information_nonnegative
#check risk_entropy_identity
#print axioms risk_entropy_identity
#check step_decomposition
#print axioms step_decomposition
#check risk_eq_scalarKL
#print axioms risk_eq_scalarKL
#check resolve_isSome_iff
#print axioms resolve_isSome_iff
#check policyKernel_isSome_iff
#print axioms policyKernel_isSome_iff
#check uninterpreted_refuses
#print axioms uninterpreted_refuses
#check firing_members
#print axioms firing_members
#check total_decomposition
#print axioms total_decomposition
#check totalG_nonnegative
#print axioms totalG_nonnegative
#check joint_state_marginal
#print axioms joint_state_marginal
#check joint_outcome_marginal
#print axioms joint_outcome_marginal
#check prediction_wellFormed
#print axioms prediction_wellFormed

end
end DarkTower.WarMachine.CascadeEFE
