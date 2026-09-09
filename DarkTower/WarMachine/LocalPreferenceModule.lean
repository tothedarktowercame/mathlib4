import DarkTower.WarMachine.Holes

/-! Versioned local C module: exact rational tables embed in the canonical
PreferenceDistribution type. This proves the representation boundary, not
that Clojure implements Lean or that a declared preference is desirable. -/
namespace DarkTower.WarMachine.LocalPreferenceModule
open Holes

structure ExactTable (O : Type) where
  support : List O
  mass : O → ℚ
  nonnegative : ∀ o, 0 ≤ mass o
  normalised : (support.map mass).sum = 1

noncomputable def ExactTable.kernel {O : Type} (t : ExactTable O) :
    ProbabilityKernel Unit O where
  support := fun _ => t.support
  mass := fun _ o => (t.mass o : ℝ)
  nonnegative := by intro _ o; exact_mod_cast t.nonnegative o
  normalised := by
    intro _
    have cast_sum : ∀ xs : List O,
        (xs.map (fun o => (t.mass o : ℝ))).sum = ((xs.map t.mass).sum : ℚ) := by
      intro xs
      induction xs with
      | nil => simp
      | cons a xs ih => simp [ih]
    rw [cast_sum, t.normalised]
    norm_num

structure Module (Obs : Vertex → Type) where
  id : String
  version : Nat
  positiveVersion : 0 < version
  context : String
  table : ExactTable (Outcome Obs)

noncomputable def Module.C {Obs : Vertex → Type} (m : Module Obs) :
    PreferenceDistribution Obs := m.table.kernel

theorem preserves_named_zero {O : Type} (t : ExactTable O) (o : O)
    (h : t.mass o = 0) : t.kernel.mass () o = 0 := by
  simp [ExactTable.kernel, h]

/-- Binary local organisation criterion. Other vertices carry no mass. This is
an example domain, not a replacement for the ruled flight disposition type. -/
abbrev BinaryObs : Vertex → Type := fun _ => Bool

def yes : Outcome BinaryObs := ⟨.organization, true⟩
def no : Outcome BinaryObs := ⟨.organization, false⟩

def binaryTable (p : ℚ) (hlo : 0 ≤ p) (hhi : p ≤ 1) :
    ExactTable (Outcome BinaryObs) where
  support := [yes, no]
  mass := fun o => match o with
    | ⟨.organization, true⟩ => p
    | ⟨.organization, false⟩ => 1 - p
    | _ => 0
  nonnegative := by
    intro o
    rcases o with ⟨v, b⟩
    cases v <;> cases b <;> simp_all
  normalised := by simp [yes, no]

noncomputable def softBinary (p : ℚ) (hlo : 1 / 2 < p) (hhi : p < 1) :
    PreferenceDistribution BinaryObs :=
  (binaryTable p (by linarith) (by linarith)).kernel

theorem softBinary_positive (p : ℚ) (hlo : 1 / 2 < p) (hhi : p < 1)
    (o : Outcome BinaryObs) (ho : o ∈ (softBinary p hlo hhi).support ()) :
    0 < (softBinary p hlo hhi).mass () o := by
  simp [softBinary, ExactTable.kernel, binaryTable] at ho
  rcases ho with rfl | rfl
  · change (0 : ℝ) < (p : ℝ)
    exact_mod_cast (show (0 : ℚ) < p by linarith)
  · change (0 : ℝ) < ((1 - p : ℚ) : ℝ)
    exact_mod_cast (show (0 : ℚ) < 1 - p by linarith)

end DarkTower.WarMachine.LocalPreferenceModule
