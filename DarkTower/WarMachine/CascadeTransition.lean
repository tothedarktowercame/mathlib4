import Mathlib
import DarkTower.WarMachine.PolicyRollout

/-!
# Interpreted pattern kernel and first-enabled cascade transition (WM-03, design P3)

A pattern `p` has `consumes`/`produces` token sets and an interpretation
`θ_p ∈ [0,1]`: the probability its THEN succeeds, taken from its attested or
documented interpretation. Its guard holds at `s` iff `consumes ⊆ s`.
`patternKernel` moves `s` to `s ∪ produces` with probability `θ_p` and stays
with probability `1 − θ_p`. A cascade policy is a precedence list of patterns;
`cascadeKernel` is the kernel of the first enabled pattern, or the identity
when none is enabled. A firing pattern with no interpretation makes the policy
a typed hole (`SPEC-cascade-policy-semantics-2026-09-15`, A1, A4, §2).
-/

namespace DarkTower.WarMachine.CascadeTransition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A pattern with token sets and an interpretation `θ ∈ [0,1]`. -/
structure InterpretedPattern (V : Type*) [Fintype V] [DecidableEq V] where
  consumes : Finset V
  produces : Finset V
  theta : ℝ
  theta_nonneg : 0 ≤ theta
  theta_le_one : theta ≤ 1

/-- The guard of `p` holds at `s` iff `p.consumes ⊆ s`. -/
def guard (p : InterpretedPattern V) (s : Finset V) : Prop := p.consumes ⊆ s

instance (p : InterpretedPattern V) (s : Finset V) : Decidable (guard p s) :=
  inferInstanceAs (Decidable (p.consumes ⊆ s))

/-- The interpreted kernel of one pattern: to `s ∪ produces` with probability
`θ_p`, stay with probability `1 − θ_p`. -/
noncomputable def patternKernel (p : InterpretedPattern V) (s s' : Finset V) : ℝ :=
  (if s' = s ∪ p.produces then p.theta else 0) + (if s' = s then 1 - p.theta else 0)

theorem patternKernel_nonneg (p : InterpretedPattern V) (s s' : Finset V) :
    0 ≤ patternKernel p s s' := by
  unfold patternKernel
  split_ifs <;> linarith [p.theta_nonneg, p.theta_le_one]

theorem patternKernel_rowsum (p : InterpretedPattern V) (s : Finset V) :
    ∑ s' : Finset V, patternKernel p s s' = 1 := by
  simp only [patternKernel, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  ring

/-- Idempotence: re-firing an achieved pattern changes nothing. -/
theorem patternKernel_of_achieved (p : InterpretedPattern V) (s s' : Finset V)
    (h : p.produces ⊆ s) :
    patternKernel p s s' = if s' = s then 1 else 0 := by
  have hus : s ∪ p.produces = s := by
    ext a
    simp only [Finset.mem_union]
    constructor
    · rintro (ha | ha)
      · exact ha
      · exact h ha
    · intro ha
      exact Or.inl ha
  by_cases hs : s' = s
  · simp only [patternKernel, hus, hs, if_true]
    ring
  · simp only [patternKernel, hus, hs, if_false]
    ring

/-- The first pattern in precedence whose guard holds at `s`. -/
def firstEnabled : List (InterpretedPattern V) → Finset V → Option (InterpretedPattern V)
  | [], _ => none
  | p :: ps, s => if p.consumes ⊆ s then some p else firstEnabled ps s

/-- The cascade kernel: the pattern kernel of the first enabled pattern, or
the identity when no pattern is enabled. -/
noncomputable def cascadeKernel (precedence : List (InterpretedPattern V))
    (s s' : Finset V) : ℝ :=
  match firstEnabled precedence s with
  | none => if s' = s then 1 else 0
  | some p => patternKernel p s s'

theorem cascadeKernel_nonneg (precedence : List (InterpretedPattern V)) (s s' : Finset V) :
    0 ≤ cascadeKernel precedence s s' := by
  cases h : firstEnabled precedence s with
  | none => simp only [cascadeKernel, h]; split_ifs <;> norm_num
  | some p =>
      simp only [cascadeKernel, h]
      exact patternKernel_nonneg p s s'

theorem cascadeKernel_rowsum (precedence : List (InterpretedPattern V)) (s : Finset V) :
    ∑ s' : Finset V, cascadeKernel precedence s s' = 1 := by
  cases h : firstEnabled precedence s with
  | none =>
      simp only [cascadeKernel, h, Finset.sum_ite_eq']
      norm_num
  | some p =>
      simp only [cascadeKernel, h]
      exact patternKernel_rowsum p s

theorem cascadeKernel_of_noEnabled (precedence : List (InterpretedPattern V)) (s s' : Finset V)
    (h : firstEnabled precedence s = none) :
    cascadeKernel precedence s s' = if s' = s then 1 else 0 := by
  simp only [cascadeKernel, h]

/-! ## Typed hole: a firing pattern with no interpretation -/

/-- A pattern slot whose interpretation may be missing (`interp = none`); when
present it is bounded in `[0,1]` (SPEC A1, A4, §2). -/
structure PatternSlot (V : Type*) [Fintype V] [DecidableEq V] where
  consumes : Finset V
  produces : Finset V
  interp : Option ℝ
  interp_bounded : ∀ x ∈ interp, 0 ≤ x ∧ x ≤ 1

/-- Interpret every slot, or `none` if any slot lacks an interpretation. -/
def interpret : List (PatternSlot V) → Option (List (InterpretedPattern V))
  | [] => some []
  | ⟨_, _, none, _⟩ :: _ => none
  | ⟨c, pr, some x, hb⟩ :: slots =>
      (interpret slots).map fun rest =>
        ⟨c, pr, x, (hb x (by simp)).1, (hb x (by simp)).2⟩ :: rest

theorem interpret_eq_none_iff (slots : List (PatternSlot V)) :
    interpret slots = none ↔ ∃ slot ∈ slots, slot.interp = none := by
  induction slots with
  | nil => simp [interpret]
  | cons slot slots ih =>
    rcases slot with ⟨c, pr, interp, hb⟩
    cases interp with
    | none =>
        rw [interpret]
        constructor
        · intro _
          exact ⟨_, List.mem_cons_self .., rfl⟩
        · intro _
          rfl
    | some x =>
        rw [interpret, Option.map_eq_none_iff, ih]
        constructor
        · rintro ⟨s, hs2, h2⟩
          exact ⟨s, List.mem_cons_of_mem _ hs2, h2⟩
        · rintro ⟨s, hs2, h2⟩
          rcases List.mem_cons.mp hs2 with rfl | hm
          · exact absurd h2 (by simp)
          · exact ⟨s, hm, h2⟩

/-! ## Rollout compatibility -/

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- A forward model whose transition is the cascade kernel of the policy
(a precedence list), given any observation kernel `A` and initial belief
`q₀` with their normalisation facts. -/
noncomputable def cascadeForwardModel
    (A : Finset V → O → ℝ) (A_nonneg : ∀ s o, 0 ≤ A s o) (A_colsum : ∀ s, ∑ o, A s o = 1)
    (q₀ : Finset V → ℝ) (q₀_nonneg : ∀ s, 0 ≤ q₀ s) (q₀_sum : ∑ s, q₀ s = 1) :
    PolicyRollout.ForwardModel (Finset V) O (List (InterpretedPattern V)) where
  B := fun π s s' => cascadeKernel π s s'
  B_nonneg := fun _ s s' => cascadeKernel_nonneg _ s s'
  B_rowsum := fun _ s => cascadeKernel_rowsum _ s
  A := A
  A_nonneg := A_nonneg
  A_colsum := A_colsum
  q₀ := q₀
  q₀_nonneg := q₀_nonneg
  q₀_sum := q₀_sum

/-! ## Depth fixture: V = Fin 3, two chained patterns -/

open DarkTower.WarMachine.PolicyRollout

private def fp1 (t : ℝ) (h1 : 0 ≤ t) (h2 : t ≤ 1) : InterpretedPattern (Fin 3) where
  consumes := ∅
  produces := {0, 1}
  theta := t
  theta_nonneg := h1
  theta_le_one := h2

private def fp2 (t : ℝ) (h1 : 0 ≤ t) (h2 : t ≤ 1) : InterpretedPattern (Fin 3) where
  consumes := {0, 1}
  produces := {2}
  theta := t
  theta_nonneg := h1
  theta_le_one := h2

private def fprec0 (t1 t2 : ℝ) (h1 : 0 ≤ t1) (h1' : t1 ≤ 1) (h2 : 0 ≤ t2) (h2' : t2 ≤ 1) :
    List (InterpretedPattern (Fin 3)) := [fp1 t1 h1 h1', fp2 t2 h2 h2']

private def fprec1 (t1 t2 : ℝ) (h1 : 0 ≤ t1) (h1' : t1 ≤ 1) (h2 : 0 ≤ t2) (h2' : t2 ≤ 1) :
    List (InterpretedPattern (Fin 3)) := [fp2 t2 h2 h2', fp1 t1 h1 h1']

private def fA : Finset (Fin 3) → Unit → ℝ := fun _ _ => 1

private def fq₀ : Finset (Fin 3) → ℝ := fun s => if s = ∅ then 1 else 0

private noncomputable def fModel :
    ForwardModel (Finset (Fin 3)) Unit (List (InterpretedPattern (Fin 3))) :=
  cascadeForwardModel fA (fun _ _ => by simp [fA]) (fun _ => by simp [fA])
    fq₀ (fun s => by unfold fq₀; split_ifs <;> norm_num)
    (by simp [fq₀, Finset.sum_ite_eq'])

/-- One step from the point mass at `∅` is just the kernel at `∅`. -/
private theorem oneStep (prec : List (InterpretedPattern (Fin 3)))
    (π : ℕ → List (InterpretedPattern (Fin 3))) (h0 : π 0 = prec)
    (s' : Finset (Fin 3)) :
    rolloutState fModel π 1 s' = cascadeKernel prec ∅ s' := by
  have hr : rolloutState fModel π 1 s'
      = ∑ s : Finset (Fin 3), fModel.B (π 0) s s' * fModel.q₀ s := rfl
  rw [hr, h0]
  have hq : ∀ s : Finset (Fin 3), fModel.B prec s s' * fModel.q₀ s
      = if s = (∅ : Finset (Fin 3)) then fModel.B prec ∅ s' else 0 := by
    intro s
    by_cases hs : s = ∅ <;> simp [fModel, cascadeForwardModel, fq₀, hs]
  rw [Finset.sum_congr rfl fun s _ => hq s, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rfl

end DarkTower.WarMachine.CascadeTransition

