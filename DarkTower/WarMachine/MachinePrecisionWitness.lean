import DarkTower.WarMachine.MachinePrecision

/-!
# Reference values for the machine's precision map

`futon2:holes/labs/wm-contract/worklist.edn` `:F8`, leg 1, slice 1. Exact
arithmetic against the production implementation
(`futon2:src/futon2/aif/precision.clj`), whose doubles were read by
`futon2:holes/labs/wm-contract/runs/F8-precision/clojure-readback.txt`.
Every history below is dyadic, so the Clojure double and the Lean rational are
the same number and the comparison is exact rather than toleranced.

The zero-error histories are the interesting ones: with the errors all zero the
variance estimate is the prior alone, `1/(1+n)`, so Π is `n+1` and the window
bound is visible as the place the sequence stops growing.
-/

namespace DarkTower.WarMachine.MachinePrecisionWitness

open DarkTower.WarMachine.MachinePrecision

/-- One still tick: `V = 1/2`, `Π = 2`. -/
theorem oneStillError : machinePrecision defaults [0] = 2 := by
  norm_num [machinePrecision, varianceComponent, regularizedErrorVariance,
    windowOf, defaults]

theorem threeStillErrors : machinePrecision defaults (List.replicate 3 0) = 4 := by
  norm_num [machinePrecision, varianceComponent, regularizedErrorVariance,
    windowOf, defaults, List.replicate_succ]

theorem sevenStillErrors : machinePrecision defaults (List.replicate 7 0) = 8 := by
  norm_num [machinePrecision, varianceComponent, regularizedErrorVariance,
    windowOf, defaults, List.replicate_succ]

theorem fifteenStillErrors : machinePrecision defaults (List.replicate 15 0) = 16 := by
  norm_num [machinePrecision, varianceComponent, regularizedErrorVariance,
    windowOf, defaults, List.replicate_succ]

/-- The window full: `Π = 21`, which `MachinePrecision.defaultsLeTwentyOne`
proves is the supremum. The cap of 200 is an order of magnitude above the
largest value any history can produce. -/
theorem fullWindowOfStillErrors :
    machinePrecision defaults (List.replicate 20 0) = 21 := by
  norm_num [machinePrecision, varianceComponent, regularizedErrorVariance,
    windowOf, defaults, List.replicate_succ]

/-- THE WINDOW BINDS. Five further still ticks do not move Π, because the
oldest five errors have left the window — an unbounded history would give 26. -/
theorem windowBinds :
    machinePrecision defaults (List.replicate 25 0)
      = machinePrecision defaults (List.replicate 20 0) := by
  norm_num [machinePrecision, varianceComponent, regularizedErrorVariance,
    windowOf, defaults, List.replicate_succ]

theorem unitError : machinePrecision defaults [1] = 1 := by
  norm_num [machinePrecision, varianceComponent, regularizedErrorVariance,
    windowOf, defaults]

theorem halfError : machinePrecision defaults [1/2] = 8/5 := by
  norm_num [machinePrecision, varianceComponent, regularizedErrorVariance,
    windowOf, defaults]

theorem tripleError : machinePrecision defaults [3] = 1/5 := by
  norm_num [machinePrecision, varianceComponent, regularizedErrorVariance,
    windowOf, defaults]

/-! ### The one guard that is reachable -/

/-- THE FLOOR IS REACHED, so `defaultsRange`'s lower bound is not vacuous:
twenty errors of size ten give a variance component of `7/667`, well under the
declared floor of `1/10`. -/
theorem floorIsReached :
    varianceComponent defaults (List.replicate 20 10) = 7/667 ∧
      machinePrecision defaults (List.replicate 20 10) = 1/10 := by
  constructor <;>
    norm_num [machinePrecision, varianceComponent, regularizedErrorVariance,
      windowOf, defaults, List.replicate_succ]

/-- And so the registry's `:formal` line is NOT the implementation's map there:
`MachinePrecision.registryFormOfUnclamped`'s hypothesis fails on this history,
and the two values differ. The clamp is a real difference, not a formality. -/
theorem registryFormFailsAtTheFloor :
    ¬ (defaults.floor ≤ varianceComponent defaults (List.replicate 20 10)) ∧
      machinePrecision defaults (List.replicate 20 10)
        ≠ 1 / max (regularizedErrorVariance defaults
            (windowOf defaults.windowSize (List.replicate 20 10)))
            defaults.minVariance := by
  constructor <;>
    norm_num [machinePrecision, varianceComponent, regularizedErrorVariance,
      windowOf, defaults, List.replicate_succ]

/-! ### The dead guards are dead by parameter, not by formula -/

/-- A parameter set differing from `defaults` only in its window: 200 instead
of 20. Everything else is the production value. -/
noncomputable def wideWindow : PrecisionParameters where
  windowSize := 200
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

/-- NON-VACUITY OF `defaultsMinVarianceInert`. Widen the window and the
`minVariance` guard fires: `V = 1/201 < 1/100`, so the map returns `100` where
the ungarded reciprocal would return `201`. The guard is dead under the
declared defaults because of the window length, not because the expression
could never take that branch. -/
theorem wideWindowReachesMinVariance :
    regularizedErrorVariance wideWindow
        (windowOf wideWindow.windowSize (List.replicate 200 0)) = 1/201 ∧
      max (regularizedErrorVariance wideWindow
          (windowOf wideWindow.windowSize (List.replicate 200 0)))
          wideWindow.minVariance = 1/100 ∧
      machinePrecision wideWindow (List.replicate 200 0) = 100 := by
  have hv : regularizedErrorVariance wideWindow
      (windowOf wideWindow.windowSize (List.replicate 200 0)) = 1/201 := by
    rw [show wideWindow.windowSize = 200 from rfl, windowOf_replicate,
      regularizedErrorVariance_replicate_zero]
    norm_num [wideWindow]
  refine ⟨hv, ?_, ?_⟩
  · rw [hv]; norm_num [wideWindow]
  · rw [machinePrecision, varianceComponent, hv]
    norm_num [wideWindow]

end DarkTower.WarMachine.MachinePrecisionWitness
