import DarkTower.WarMachine.Holes

/-!
# The machine's precision map Π, stated

`futon2:holes/labs/wm-contract/worklist.edn` `:F8`, leg 1 (Lean completion),
slice 1. The quantity is `:precision` (Π, node R7) of
`futon2:holes/labs/wm-contract/aif-equations.edn:81-86`, whose row carried
`:lean nil :lean-status :missing` before this module.

WHAT WAS IN LEAN BEFORE. `Holes.PrecisionMap` (`Holes.lean:6820`) is an
`abbrev` for `Channel → NonnegativeReal` — the CARRIER, a nonnegative
channel-indexed weight. Nothing said where the weight comes from.
`PrecisionWitness.lean` witnesses only that precision and prediction error are
not interchangeable inside `variationalFreeEnergy`. So the R7 equation itself
had no Lean statement.

WHAT THIS MODULE STATES. The map the implementation actually computes
(`futon2:src/futon2/aif/precision.clj:116-150`, `update-channel-precision`
under the production `:salience-mode :separate`):

    window   := the last `windowSize` prediction errors of the channel
    V        := (priorStrength · priorVariance + Σ_{e ∈ window} e²)
                / (priorStrength + |window|)
    Π        := min (max (1 / max V minVariance) floor) cap

The registry's `:formal` line is `Pi_k := 1 / max(Var(eps_k), eps0)`.
`registryFormOfUnclamped` below is the exact statement of the relation between
the two: the registry line is the implementation's map wherever the
floor/cap clamp is inactive, and nowhere else. Two further reductions the
registry line does not carry are visible in `V`: the estimate is a posterior
mean squared error under a variance prior rather than a sample variance
(`precision.clj:73-86`), and it is taken over a bounded window rather than the
whole history.

WHAT THIS MODULE FINDS. Under the DECLARED DEFAULTS
(`precision.clj:42-54`: window 20, minVariance 0.01, priorVariance 1.0,
priorStrength 1.0, floor 0.1, cap 200.0) two of the three guards in that
expression are DEAD. `V ≥ 1/21 > minVariance`, so `max V minVariance` is
always `V` and the `eps0` branch of the registry's own formal line is never
taken (`defaultsMinVarianceInert`); and `Π ≤ 21 < cap`, so the cap is never
taken (`defaultsCapInert`, `defaultsLeTwentyOne`). Only the floor is
reachable, and `MachinePrecisionWitness` exhibits a history that reaches it.
The two dead guards are properties of the default parameters and not of the
formula: `MachinePrecisionWitness.wideWindowReachesMinVariance` exhibits a
parameter set under which the `minVariance` branch is taken, so the inertness
theorems are not vacuous statements about an expression that could never fire.

WHAT THIS MODULE DOES NOT DO. It states no ruling about whether the two dead
guards should be changed, and it does not touch the `:choices` registry. It
makes no claim about generalised coordinates, about the `:salience-mode
:summed` historical path (`precision.clj:152-158`), or about the need term,
which production Π does not contain.
-/

namespace DarkTower.WarMachine.MachinePrecision

open DarkTower.WarMachine.Holes

/-- The declared parameters of the precision map, with the positivity the
implementation's own guard asserts at runtime (`precision.clj:79-82` throws
unless the variance prior is positive). -/
structure PrecisionParameters where
  windowSize : Nat
  minVariance : ℝ
  priorVariance : ℝ
  priorStrength : ℝ
  floor : ℝ
  cap : ℝ
  windowPositive : 0 < windowSize
  minVariancePositive : 0 < minVariance
  priorVariancePositive : 0 < priorVariance
  priorStrengthPositive : 0 < priorStrength
  floorPositive : 0 < floor
  floorLeCap : floor ≤ cap

/-- The bounded error window: the last `n` entries of the history.
`precision.clj:136-140` appends the new error and keeps the trailing
`window-size` entries when the history is longer, the whole history otherwise;
`List.drop (length - n)` is both cases, because `length - n` is `0` in `Nat`
when the history is short. -/
def windowOf (n : Nat) (history : List ℝ) : List ℝ :=
  history.drop (history.length - n)

/-- `precision.clj:73-86` `regularized-error-variance`: the posterior mean
squared prediction error under a variance prior. Errors are NOT centred on
their sample mean — they are centred on the model-implied target zero, so a
constant nonzero residual stays evidence of imprecision. -/
noncomputable def regularizedErrorVariance (p : PrecisionParameters) (window : List ℝ) : ℝ :=
  (p.priorStrength * p.priorVariance + (window.map (fun e => e ^ 2)).sum)
    / (p.priorStrength + window.length)

/-- `precision.clj:142`: the variance component, `1 / max(V, minVariance)`.
This is the registry's `:formal` line in full. -/
noncomputable def varianceComponent (p : PrecisionParameters) (history : List ℝ) : ℝ :=
  1 / max (regularizedErrorVariance p (windowOf p.windowSize history)) p.minVariance

/-- PRODUCTION Π, `precision.clj:145-146` under `:salience-mode :separate`:
the variance component clamped into `[floor, cap]`. The need term is emitted
beside it under `:salience` and is not summed in. -/
noncomputable def machinePrecision (p : PrecisionParameters) (history : List ℝ) : ℝ :=
  min (max (varianceComponent p history) p.floor) p.cap

theorem windowOf_length_le (n : Nat) (history : List ℝ) :
    (windowOf n history).length ≤ n := by
  simp only [windowOf, List.length_drop]
  omega

/-- The window of a constant history is that history, truncated to the window
length. -/
theorem windowOf_replicate (n m : Nat) (x : ℝ) :
    windowOf n (List.replicate m x) = List.replicate (min m n) x := by
  simp only [windowOf, List.length_replicate, List.drop_replicate]
  congr 1
  omega

/-- A STILL CHANNEL. With every error in the window zero, the variance estimate
is the prior alone, `priorStrength · priorVariance / (priorStrength + n)`. This
is why the reference values below are the integers `n+1`, and why `V` cannot
reach `minVariance` without a long window. -/
theorem regularizedErrorVariance_replicate_zero (p : PrecisionParameters) (n : Nat) :
    regularizedErrorVariance p (List.replicate n (0:ℝ))
      = p.priorStrength * p.priorVariance / (p.priorStrength + n) := by
  simp [regularizedErrorVariance]

theorem regularizedErrorVariance_pos (p : PrecisionParameters) (w : List ℝ) :
    0 < regularizedErrorVariance p w := by
  have hsum : (0:ℝ) ≤ (w.map (fun e => e ^ 2)).sum := by
    apply List.sum_nonneg
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, _, rfl⟩ := hx
    positivity
  have hnum : 0 < p.priorStrength * p.priorVariance +
      (w.map (fun e => e ^ 2)).sum :=
    by nlinarith [mul_pos p.priorStrengthPositive p.priorVariancePositive]
  have hden : 0 < p.priorStrength + (w.length : ℝ) := by
    have := p.priorStrengthPositive
    have hc : (0:ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
    linarith
  exact div_pos hnum hden

/-- The prior floors the variance estimate: no history, however long or however
still, can drive `V` below `priorStrength · priorVariance / (priorStrength +
windowSize)`. This is what makes the `minVariance` guard reachable or not. -/
theorem regularizedErrorVariance_ge (p : PrecisionParameters) (w : List ℝ)
    (hw : w.length ≤ p.windowSize) :
    p.priorStrength * p.priorVariance / (p.priorStrength + p.windowSize)
      ≤ regularizedErrorVariance p w := by
  have hsum : (0:ℝ) ≤ (w.map (fun e => e ^ 2)).sum := by
    apply List.sum_nonneg
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, _, rfl⟩ := hx
    positivity
  have hpp : 0 < p.priorStrength * p.priorVariance :=
    mul_pos p.priorStrengthPositive p.priorVariancePositive
  have hlen : (w.length : ℝ) ≤ (p.windowSize : ℝ) := Nat.cast_le.mpr hw
  have hd1 : 0 < p.priorStrength + (p.windowSize : ℝ) := by
    have := p.priorStrengthPositive
    have hc : (0:ℝ) ≤ (p.windowSize : ℝ) := Nat.cast_nonneg _
    linarith
  have hd2 : 0 < p.priorStrength + (w.length : ℝ) := by
    have := p.priorStrengthPositive
    have hc : (0:ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
    linarith
  rw [regularizedErrorVariance, div_le_div_iff₀ hd1 hd2]
  nlinarith

/-- Π never falls below the declared floor. -/
theorem floor_le_machinePrecision (p : PrecisionParameters) (history : List ℝ) :
    p.floor ≤ machinePrecision p history :=
  le_min (le_max_right _ _) p.floorLeCap

/-- THE REGISTRY LINE, EXACTLY WHERE IT HOLDS. `aif-equations.edn:83` writes
`Pi_k := 1 / max(Var(eps_k), eps0)`; the implementation's map agrees with that
line precisely on the histories whose variance component already lies inside
`[floor, cap]`, and the clamp is the whole of the difference. -/
theorem registryFormOfUnclamped (p : PrecisionParameters) (history : List ℝ)
    (hlo : p.floor ≤ varianceComponent p history)
    (hhi : varianceComponent p history ≤ p.cap) :
    machinePrecision p history
      = 1 / max (regularizedErrorVariance p (windowOf p.windowSize history))
          p.minVariance := by
  rw [machinePrecision, max_eq_left hlo, min_eq_left hhi, varianceComponent]

/-- Π as the carrier `Holes.PrecisionMap` the rest of the corpus consumes:
the R7 → R8 seam, since `Holes.variationalFreeEnergy` weights by exactly this
map. Nonnegativity is discharged by the floor, not assumed. -/
noncomputable def machinePrecisionMap (p : PrecisionParameters)
    (history : Channel → List ℝ) : PrecisionMap :=
  fun k => ⟨machinePrecision p (history k),
    le_trans (le_of_lt p.floorPositive) (floor_le_machinePrecision p (history k))⟩

theorem machinePrecisionMap_value (p : PrecisionParameters)
    (history : Channel → List ℝ) (k : Channel) :
    (machinePrecisionMap p history k).value = machinePrecision p (history k) := rfl

/-! ### The declared defaults, and the two guards they kill -/

/-- `precision.clj:42-54`, the values the production path runs with. -/
noncomputable def defaults : PrecisionParameters where
  windowSize := 20
  minVariance := 1 / 100
  priorVariance := 1
  priorStrength := 1
  floor := 1 / 10
  cap := 200
  windowPositive := by norm_num
  minVariancePositive := by norm_num
  priorVariancePositive := by norm_num
  priorStrengthPositive := by norm_num
  floorPositive := by norm_num
  floorLeCap := by norm_num

theorem defaultsVarianceGe (history : List ℝ) :
    (1:ℝ) / 21 ≤ regularizedErrorVariance defaults
      (windowOf defaults.windowSize history) := by
  have h := regularizedErrorVariance_ge defaults
    (windowOf defaults.windowSize history) (windowOf_length_le _ _)
  norm_num [defaults] at h
  exact h

/-- FIRST DEAD GUARD. `1/21 > 1/100`, so under the defaults `max V minVariance`
is always `V`: the `eps0` branch of the registry's `:formal` line is never
taken on any history. -/
theorem defaultsMinVarianceInert (history : List ℝ) :
    max (regularizedErrorVariance defaults (windowOf defaults.windowSize history))
        defaults.minVariance
      = regularizedErrorVariance defaults (windowOf defaults.windowSize history) := by
  apply max_eq_left
  have h := defaultsVarianceGe history
  have hmin : defaults.minVariance = 1 / 100 := rfl
  rw [hmin]
  linarith

theorem defaultsVarianceComponentLe (history : List ℝ) :
    varianceComponent defaults history ≤ 21 := by
  have hpos := regularizedErrorVariance_pos defaults
    (windowOf defaults.windowSize history)
  have hge := defaultsVarianceGe history
  rw [varianceComponent, defaultsMinVarianceInert, div_le_iff₀ hpos]
  linarith

/-- SECOND DEAD GUARD. Π is bounded above by 21 under the defaults, and the
declared cap is 200: the cap is never taken on any history. -/
theorem defaultsCapInert (history : List ℝ) :
    machinePrecision defaults history
      = max (varianceComponent defaults history) defaults.floor := by
  apply min_eq_left
  have h := defaultsVarianceComponentLe history
  have hfloor : defaults.floor ≤ (21:ℝ) := by norm_num [defaults]
  have hmax : max (varianceComponent defaults history) defaults.floor ≤ 21 :=
    max_le h hfloor
  have hcap : (21:ℝ) ≤ defaults.cap := by norm_num [defaults]
  linarith

theorem defaultsLeTwentyOne (history : List ℝ) :
    machinePrecision defaults history ≤ 21 := by
  rw [defaultsCapInert]
  exact max_le (defaultsVarianceComponentLe history) (by norm_num [defaults])

/-- What survives of the clamp under the defaults: one bound, not three. -/
theorem defaultsRange (history : List ℝ) :
    (1:ℝ) / 10 ≤ machinePrecision defaults history ∧
      machinePrecision defaults history ≤ 21 := by
  refine ⟨?_, defaultsLeTwentyOne history⟩
  have h := floor_le_machinePrecision defaults history
  norm_num [defaults] at h
  exact h

end DarkTower.WarMachine.MachinePrecision
