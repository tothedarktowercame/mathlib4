import DarkTower.AIF.Terms

/-!
# Grain maps — inducing cascade-grain preference from mission-grain C

The live C is derived at mission grain; cascade decisions score outcomes
at cascade-token grain; the vocabularies are disjoint (WIRE-3's
`:derived-no-overlap`, 2026-09-18). This module states what legitimately
induces the finer-grain preference: a **pullback of weights along a
partial grain map** `g : O' → Option O` (a cascade outcome maps to the
mission event it closes, or to nothing).

Design laws, committed to claude-4 and zai-55 (WM-06 narrowing) before
this module existed — the Clojure mirrors these laws, not this file's
signatures:

1. **Pull-only direction.** C pulls back; Q never moves grain at runtime.
   The pushforward appears only in the conservativity theorem.
2. **Zeros are exact.** A pulled weight is zero iff the outcome is
   unmapped or its mission weight is zero (`pullWeight_eq_zero_iff`);
   no renormalisation can smooth or mint one. Unmapped outcomes are
   NEUTRAL (weight 0 in the utility sense — absent from want, enlarging
   Z downstream), never hard-zeroed: under non-zero observation rates a
   hard zero anywhere Q reaches makes risk infinite.
3. **Renormalisation lives downstream.** Weights feed the already-live
   Z-normalisation over the comparison universe (`log-preference-fn`,
   Lean `TokenPreference`); this module introduces no second normaliser.
   Unreachable mission mass simply never arrives (`sum_pullWeight`), and
   **coverage** — the reachable fraction of mission mass — is a recorded
   quantity, with `0 < coverage`-style positivity as the only theorem
   hypothesis it ever becomes.
4. **The within-fiber split is a declared default.** `uniformSplit`
   satisfies the `FiberSplit` law; any future institutional weighting
   (preference over HOW an outcome is pursued — the second half of Joe's
   view of C) replaces the split, not the pullback.

WM-13's "C as a family across grain and time": the family is one C per
grain plus grain maps satisfying `pushforward_pullWeight`; the step index
of `Preference` commutes with all of this pointwise and is omitted here.
-/

namespace DarkTower.AIF

variable {O' O : Type*} [Fintype O'] [DecidableEq O'] [DecidableEq O]

section GrainMap

variable (g : O' → Option O)

/-- The fiber of a mission event: the cascade outcomes that close it. -/
def fiber (m : O) : Finset O' :=
  Finset.univ.filter (fun o' => g o' = some m)

omit [DecidableEq O'] in
@[simp] theorem mem_fiber {m : O} {o' : O'} :
    o' ∈ fiber g m ↔ g o' = some m := by
  simp [fiber]

/-- Weight pullback along the grain map: a mapped outcome carries its
mission event's weight scaled by the declared split; an unmapped outcome
carries weight 0 (neutral, NOT a hard zero — see module docstring). -/
def pullWeight (s : O' → ℝ) (w : O → ℝ) : O' → ℝ :=
  fun o' => match g o' with
    | none => 0
    | some m => s o' * w m

omit [Fintype O'] [DecidableEq O'] [DecidableEq O] in
@[simp] theorem pullWeight_of_none {s : O' → ℝ} {w : O → ℝ} {o' : O'}
    (h : g o' = none) : pullWeight g s w o' = 0 := by
  simp [pullWeight, h]

omit [Fintype O'] [DecidableEq O'] [DecidableEq O] in
theorem pullWeight_of_some {s : O' → ℝ} {w : O → ℝ} {o' : O'} {m : O}
    (h : g o' = some m) : pullWeight g s w o' = s o' * w m := by
  simp [pullWeight, h]

omit [Fintype O'] [DecidableEq O'] [DecidableEq O] in
/-- Zero-preservation on the mapped part: with a positive split, the
pulled weight vanishes exactly when the mission weight does. One
statement covers zero behaviour at both grains. -/
theorem pullWeight_eq_zero_iff {s : O' → ℝ} {w : O → ℝ} {o' : O'} {m : O}
    (h : g o' = some m) (hs : 0 < s o') :
    pullWeight g s w o' = 0 ↔ w m = 0 := by
  rw [pullWeight_of_some g h]
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with hs0 | hw
    · exact absurd hs0 (ne_of_gt hs)
    · exact hw
  · intro hw; rw [hw, mul_zero]

omit [Fintype O'] [DecidableEq O'] [DecidableEq O] in
/-- Nonnegativity is preserved. -/
theorem pullWeight_nonneg {s : O' → ℝ} {w : O → ℝ}
    (hs : ∀ o', 0 ≤ s o') (hw : ∀ m, 0 ≤ w m) (o' : O') :
    0 ≤ pullWeight g s w o' := by
  unfold pullWeight
  cases hg : g o' with
  | none => simp
  | some m => exact mul_nonneg (hs o') (hw m)

/-- The law a within-fiber split must satisfy: nonnegative, and summing
to 1 on every nonempty fiber. Between-fiber mass is then fixed by the
mission C alone; the split only distributes it. -/
def FiberSplit (s : O' → ℝ) : Prop :=
  (∀ o', 0 ≤ s o') ∧ ∀ m : O, (fiber g m).Nonempty → ∑ o' ∈ fiber g m, s o' = 1

omit [DecidableEq O'] in
/-- **Conservativity**: pushing the pulled-back weights forward along the
grain map recovers the mission weight exactly, on every reachable mission
event. This is the theorem that makes "C as a family across grain" a
checkable statement rather than a phrase. -/
theorem pushforward_pullWeight {s : O' → ℝ} {w : O → ℝ}
    (hs : FiberSplit g s) {m : O} (hm : (fiber g m).Nonempty) :
    ∑ o' ∈ fiber g m, pullWeight g s w o' = w m := by
  have : ∀ o' ∈ fiber g m, pullWeight g s w o' = s o' * w m := fun o' ho' =>
    pullWeight_of_some g ((mem_fiber g).mp ho')
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hs.2 m hm, one_mul]

/-- The declared default split: uniform within each fiber. -/
noncomputable def uniformSplit : O' → ℝ :=
  fun o' => match g o' with
    | none => 0
    | some m => ((fiber g m).card : ℝ)⁻¹

omit [DecidableEq O'] in
theorem uniformSplit_fiberSplit : FiberSplit g (uniformSplit g) := by
  constructor
  · intro o'
    unfold uniformSplit
    cases hg : g o' with
    | none => simp
    | some m => positivity
  · intro m hm
    have hcard : (0 : ℝ) < (fiber g m).card := by
      exact_mod_cast Finset.card_pos.mpr hm
    have : ∀ o' ∈ fiber g m, uniformSplit g o' = ((fiber g m).card : ℝ)⁻¹ := by
      intro o' ho'
      unfold uniformSplit
      rw [(mem_fiber g).mp ho']
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul,
      mul_inv_cancel₀ (ne_of_gt hcard)]

omit [DecidableEq O'] in
/-- The uniform split is positive on every mapped outcome (its fiber
contains at least that outcome), so zero-preservation applies to the
default unconditionally. -/
theorem uniformSplit_pos {o' : O'} {m : O} (h : g o' = some m) :
    0 < uniformSplit g o' := by
  unfold uniformSplit
  rw [h]
  have : o' ∈ fiber g m := (mem_fiber g).mpr h
  have hcard : (0 : ℝ) < (fiber g m).card :=
    by exact_mod_cast Finset.card_pos.mpr ⟨o', this⟩
  positivity

end GrainMap

section Coverage

variable [Fintype O] (g : O' → Option O)

/-- The reachable mission events: those some cascade outcome closes. -/
noncomputable def reachableSet : Finset O :=
  Finset.univ.filter (fun m => (fiber g m).Nonempty)

/-- Total pulled mass equals the reachable mission mass: unreachable
mission-grain mass never arrives at cascade grain. `coverage` (the
recorded quantity: reachable mass / total mass) is this sum divided by
`∑ m, w m`; it enters theorems only as a positivity hypothesis. -/
theorem sum_pullWeight {s : O' → ℝ} {w : O → ℝ} (hs : FiberSplit g s) :
    ∑ o', pullWeight g s w o' = ∑ m ∈ reachableSet g, w m := by
  classical
  have hpart :
      ∑ o', pullWeight g s w o'
        = ∑ b ∈ (Finset.univ : Finset (Option O)),
            ∑ o' ∈ Finset.univ.filter (fun o' => g o' = b),
              pullWeight g s w o' := by
    rw [Finset.sum_fiberwise_of_maps_to (fun o' _ => Finset.mem_univ (g o'))]
  rw [hpart, Fintype.sum_option]
  have hnone :
      ∑ o' ∈ Finset.univ.filter (fun o' => g o' = none),
        pullWeight g s w o' = 0 :=
    Finset.sum_eq_zero fun o' ho' =>
      pullWeight_of_none g (Finset.mem_filter.mp ho').2
  rw [hnone, zero_add]
  have hfib : ∀ m : O,
      Finset.univ.filter (fun o' => g o' = some m) = fiber g m := fun m => rfl
  calc ∑ m : O, ∑ o' ∈ Finset.univ.filter (fun o' => g o' = some m),
          pullWeight g s w o'
      = ∑ m ∈ reachableSet g, ∑ o' ∈ fiber g m, pullWeight g s w o' := by
        rw [← Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset O) (fun m => (fiber g m).Nonempty)]
        have hempty :
            ∑ m ∈ Finset.univ.filter (fun m => ¬(fiber g m).Nonempty),
              ∑ o' ∈ fiber g m, pullWeight g s w o' = 0 :=
          Finset.sum_eq_zero fun m hm => by
            have : fiber g m = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp (Finset.mem_filter.mp hm).2
            rw [this, Finset.sum_empty]
        simp only [hfib]
        rw [hempty, add_zero]
        rfl
    _ = ∑ m ∈ reachableSet g, w m :=
        Finset.sum_congr rfl fun m hm =>
          pushforward_pullWeight g hs (Finset.mem_filter.mp hm).2

/-- The hard-zero (`zeroed`) mechanism pulls back as the exact preimage:
a cascade outcome is zeroed iff it closes a zeroed mission event. -/
def pullZeroed (Z : Finset O) : Finset O' :=
  Finset.univ.filter (fun o' => ∃ m ∈ Z, g o' = some m)

omit [DecidableEq O'] [Fintype O] in
@[simp] theorem mem_pullZeroed {Z : Finset O} {o' : O'} :
    o' ∈ pullZeroed g Z ↔ ∃ m ∈ Z, g o' = some m := by
  simp [pullZeroed]

end Coverage

end DarkTower.AIF
