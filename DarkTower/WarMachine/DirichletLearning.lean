import DarkTower.WarMachine.Holes

/-!
# Dirichlet accumulation (Da Costa et al. 2020, eq. 21)

Da Costa et al. 2020, eq. (21): `a_post = a_prior + Σ_{τ=1}^{T} o_τ ⊗ s_τ`,
where `o_τ` is the observed outcome vector and `s_τ` the posterior state
belief at tick `τ`; the posterior becomes the next trial's prior
(`refs/dacosta2020.txt:943-955`, PDF p. 18).  The shape and common dimension
come from the types: a concentration array over outcomes `O` and states `S`
cannot be combined with one of a different shape.
-/

namespace DarkTower.WarMachine.DirichletLearning

/-- Concentration carrier with matrix shape: one positive concentration per
(outcome, state) pair.  Equation: Da Costa et al. 2020 eq. (21),
`refs/dacosta2020.txt:943-955`. -/
structure DirichletParams (O S : Type*) where
  conc : O → S → ℝ
  pos : ∀ o s, 0 < conc o s

/-- Extensionality: two parameter arrays are equal when their concentrations
agree pointwise (positivity is a proof). -/
theorem ext {O S : Type*} {a b : DirichletParams O S}
    (h : ∀ o s, a.conc o s = b.conc o s) : a = b := by
  obtain ⟨c1, p1⟩ := a
  obtain ⟨c2, p2⟩ := b
  have hc : c1 = c2 := funext fun o => funext fun s => h o s
  subst hc
  rfl

/-- One trial: a list of (outcome vector, state belief) pairs, one per tick. -/
abbrev Trial (O S : Type*) := List ((O → ℝ) × (S → ℝ))

/-- Every outcome entry and state entry of every tick is nonnegative. -/
def TrialNonneg {O S : Type*} (t : Trial O S) : Prop :=
  ∀ p ∈ t, (∀ o, 0 ≤ p.1 o) ∧ (∀ s, 0 ≤ p.2 s)

theorem trialNonneg_of_cons {O S : Type*} {p : (O → ℝ) × (S → ℝ)} {rest : Trial O S}
    (h : TrialNonneg (p :: rest)) :
    (∀ o, 0 ≤ p.1 o) ∧ (∀ s, 0 ≤ p.2 s) := h p (by simp)

theorem trialNonneg_tail_of_cons {O S : Type*} {p : (O → ℝ) × (S → ℝ)} {rest : Trial O S}
    (h : TrialNonneg (p :: rest)) : TrialNonneg rest :=
  fun q hq => h q (by simp [hq])

/-- One-tick outer-product update: add `o ⊗ s` componentwise, staying
positive. -/
def step {O S : Type*} (a : DirichletParams O S) (p : (O → ℝ) × (S → ℝ))
    (hn1 : ∀ o, 0 ≤ p.1 o) (hn2 : ∀ s, 0 ≤ p.2 s) : DirichletParams O S where
  conc := fun o s => a.conc o s + p.1 o * p.2 s
  pos := fun o s => by
    have h1 : (0 : ℝ) < a.conc o s := a.pos o s
    have h2 : (0 : ℝ) ≤ p.1 o * p.2 s := mul_nonneg (hn1 o) (hn2 s)
    linarith

/-- Eq. (21): accumulate the whole trial's outer products into the prior;
the result is the next trial's prior. -/
def accumulate {O S : Type*} :
    (a : DirichletParams O S) → (t : Trial O S) → TrialNonneg t →
    DirichletParams O S
  | a, [], _ => a
  | a, p :: rest, h =>
      accumulate (step a p (trialNonneg_of_cons h).1 (trialNonneg_of_cons h).2)
        rest (trialNonneg_tail_of_cons h)

/-- The recursion equation for a one-tick extension of the trial. -/
theorem accumulate_cons {O S : Type*} (a : DirichletParams O S)
    (p : (O → ℝ) × (S → ℝ)) (rest : Trial O S) (h : TrialNonneg (p :: rest)) :
    accumulate a (p :: rest) h =
      accumulate (step a p (trialNonneg_of_cons h).1 (trialNonneg_of_cons h).2)
        rest (trialNonneg_tail_of_cons h) := rfl

/-- (iii) An empty trial leaves the prior unchanged. -/
theorem accumulate_nil {O S : Type*} (a : DirichletParams O S)
    (h : TrialNonneg ([] : Trial O S)) : accumulate a [] h = a := rfl

/-- (i) The defining equation (21) as a stated equality: the posterior
concentration at (o, s) is the prior plus the sum of outer products over
the trial's ticks. -/
theorem accumulate_conc {O S : Type*} (a : DirichletParams O S) (t : Trial O S)
    (h : TrialNonneg t) (o : O) (s : S) :
    (accumulate a t h).conc o s =
      a.conc o s + (t.map fun p => p.1 o * p.2 s).sum := by
  revert h
  induction t generalizing a with
  | nil => intro _; simp [accumulate]
  | cons p rest ih =>
      intro h
      rw [accumulate_cons, ih _ (trialNonneg_tail_of_cons h)]
      simp only [step, List.map_cons, List.sum_cons]
      ring

/-- (ii) The posterior-becomes-prior step: accumulating trial₁ ++ trial₂ in
one pass equals accumulating trial₁ first and using that posterior as the
prior for trial₂. -/
theorem accumulate_append {O S : Type*} (a : DirichletParams O S)
    (t1 t2 : Trial O S) (h1 : TrialNonneg t1) (h2 : TrialNonneg t2) :
    accumulate a (t1 ++ t2) (by
      intro p hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact h1 p hp'
      · exact h2 p hp') =
      accumulate (accumulate a t1 h1) t2 h2 := by
  apply ext
  intro o s
  rw [accumulate_conc a (t1 ++ t2) _ o s,
    accumulate_conc (accumulate a t1 h1) t2 h2 o s, accumulate_conc a t1 h1 o s]
  simp only [List.map_append, List.sum_append]
  ring

/-- (iv) One-hot case: a single tick whose outcome is the indicator of `o*`
and whose state belief is the indicator of `s*` adds exactly 1 to cell
`(o*, s*)` and 0 elsewhere — eq. (21)'s "counts the number of times a
specific mapping ... has been observed". -/
theorem accumulate_onehot {O S : Type*} [DecidableEq O] [DecidableEq S]
    (a : DirichletParams O S) (oStar : O) (sStar : S) :
    (accumulate a
        [(fun o => if o = oStar then 1 else 0, fun s => if s = sStar then 1 else 0)]
        (by
          intro p hp
          simp only [List.mem_singleton] at hp
          subst hp
          constructor
          · intro x; simp only; split <;> norm_num
          · intro x; simp only; split <;> norm_num)).conc =
      fun o s => a.conc o s +
        (if o = oStar ∧ s = sStar then (1 : ℝ) else 0) := by
  funext o s
  rw [accumulate_conc]
  by_cases ho : o = oStar <;> by_cases hs : s = sStar <;>
    simp [ho, hs]

section Total

variable {O S : Type*} [Fintype O] [Fintype S]

/-- Total concentration of a parameter array. -/
def total (a : DirichletParams O S) : ℝ :=
  ∑ o, ∑ s, a.conc o s

/-- One tick grows the total concentration by the product of the outcome
and state masses. -/
theorem total_step (a : DirichletParams O S) (p : (O → ℝ) × (S → ℝ))
    (hn1 : ∀ o, 0 ≤ p.1 o) (hn2 : ∀ s, 0 ≤ p.2 s) :
    total (step a p hn1 hn2) =
      total a + (∑ o, p.1 o) * (∑ s, p.2 s) := by
  simp only [total, step, Finset.sum_add_distrib]
  rw [← Finset.sum_mul_sum]

/-- (v) The total concentration grows by the sum over ticks of the product
of the outcome and state masses. -/
theorem accumulate_total (a : DirichletParams O S) (t : Trial O S)
    (h : TrialNonneg t) :
    total (accumulate a t h) =
      total a + (t.map fun p => (∑ o, p.1 o) * (∑ s, p.2 s)).sum := by
  revert h
  induction t generalizing a with
  | nil => intro _; simp [accumulate, total]
  | cons p rest ih =>
      intro h
      rw [accumulate_cons, ih _ (trialNonneg_tail_of_cons h),
        total_step a p (trialNonneg_of_cons h).1 (trialNonneg_of_cons h).2]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- (v) corollary: when every outcome vector and state belief sums to one,
the total concentration grows by exactly the number of ticks. -/
theorem map_masses_sum {O S : Type*} [Fintype O] [Fintype S] (t : Trial O S)
    (ho : ∀ p ∈ t, ∑ o, p.1 o = 1) (hs : ∀ p ∈ t, ∑ s, p.2 s = 1) :
    (t.map fun p => (∑ o, p.1 o) * (∑ s, p.2 s)).sum = (t.length : ℝ) := by
  induction t with
  | nil => simp
  | cons p rest ih =>
      rw [List.map_cons, List.sum_cons, ho p (by simp), hs p (by simp), mul_one,
        ih (fun q hq => ho q (by simp [hq])) (fun q hq => hs q (by simp [hq]))]
      simp
      ring

theorem accumulate_total_of_normalized (a : DirichletParams O S) (t : Trial O S)
    (h : TrialNonneg t)
    (ho : ∀ p ∈ t, ∑ o, p.1 o = 1) (hs : ∀ p ∈ t, ∑ s, p.2 s = 1) :
    total (accumulate a t h) = total a + (t.length : ℝ) := by
  rw [accumulate_total a t h, map_masses_sum t ho hs]

end Total

section Fixture
/- Fixture: 2×2 with uniform positive prior and a two-tick one-hot trial. -/

def fixturePrior : DirichletParams (Fin 2) (Fin 2) :=
  ⟨fun _ _ => 1, by intro; norm_num⟩

def fixtureTrial : Trial (Fin 2) (Fin 2) :=
  [(fun o => if o = 0 then 1 else 0, fun s => if s = 0 then 1 else 0),
   (fun o => if o = 1 then 1 else 0, fun s => if s = 1 then 1 else 0)]

theorem fixtureTrial_nonneg : TrialNonneg fixtureTrial := by
  intro p hp
  simp only [fixtureTrial, List.mem_cons] at hp
  rcases hp with hp | hp | hp
  · subst hp
    constructor
    · intro x; simp only; split <;> norm_num
    · intro x; simp only; split <;> norm_num
  · subst hp
    constructor
    · intro x; simp only; split <;> norm_num
    · intro x; simp only; split <;> norm_num
  · simp at hp

/-- Two one-hot ticks on the diagonal raise exactly the diagonal cells from
1 to 2 and leave the off-diagonal cells at 1. -/
theorem fixture_accumulate (o s : Fin 2) :
    (accumulate fixturePrior fixtureTrial fixtureTrial_nonneg).conc o s =
      if o.val = s.val then 2 else 1 := by
  rw [accumulate_conc]
  fin_cases o <;> fin_cases s <;>
    simp [fixturePrior, fixtureTrial] <;> norm_num

/-- The fixture's total concentration grows by exactly 2, the number of
ticks. -/
theorem fixture_total :
    total (accumulate fixturePrior fixtureTrial fixtureTrial_nonneg) =
      total fixturePrior + 2 := by
  rw [accumulate_total_of_normalized]
  · simp [fixtureTrial]
  · intro p hp
    simp only [fixtureTrial, List.mem_cons] at hp
    rcases hp with hp | hp | hp
    · subst hp; simp
    · subst hp; simp
    · simp at hp
  · intro p hp
    simp only [fixtureTrial, List.mem_cons] at hp
    rcases hp with hp | hp | hp
    · subst hp; simp
    · subst hp; simp
    · simp at hp

end Fixture

#print axioms ext
#print axioms accumulate_conc
#print axioms accumulate_append
#print axioms accumulate_nil
#print axioms accumulate_onehot
#print axioms accumulate_total
#print axioms accumulate_total_of_normalized
#print axioms fixture_accumulate
#print axioms fixture_total

end DarkTower.WarMachine.DirichletLearning
