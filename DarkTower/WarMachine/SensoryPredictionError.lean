import DarkTower.WarMachine.MachinePredictionError

/-!
# The sensory prediction error of Buckley et al. 2017 eq. (46), stated

Row `:prediction-error` of `futon2:holes/labs/wm-contract/aif-equations.edn`,
per audit A2 §2 (`AUDIT-lean-aif-equations-2026-09-16.md`): the row cites
Buckley et al. 2017 eq. (46), ε_z = φ − g(μ), and the audit's finding was that
the typed producer `machineChannelPredictionError` refuses when a variance is
missing and admits negative variances — a quantity that is not in the
equation. This module binds the row to the equation itself and relates the
producer to it; it does not patch the producer.

Reduction the row adopts: no generalised coordinates, so only the order-0
term is kept (`refs/buckley2017.txt:1128–1134`); the dynamical error eq. (47)
is not part of this row.
-/

namespace DarkTower.WarMachine.SensoryPredictionError

open DarkTower.WarMachine.Holes DarkTower.WarMachine.MachinePredictionError

/-- Buckley et al. 2017 eq. (46), order-0 reduction: the sensory prediction
error at channel `k` is the observation `o.value k` minus the observation map
`g` applied to the belief mean `μ` at `k`. `g` is a parameter because (46) is
stated for a general observation map; no variance appears. -/
def sensoryPredictionError {M : Type*} (g : M → Channel → ℝ)
    (o : ObservationVector) (μ : M) : Channel → ℝ :=
  fun k => o.value k - g μ k

/-- With `M := Channel → ℝ` and the identity observation map, the error is
`o.value k - μ k` — the registry form `eps_k := o_k - mu_k`. -/
theorem sensoryPredictionError_identity (o : ObservationVector) (μ : Channel → ℝ)
    (k : Channel) :
    sensoryPredictionError (fun (μ : Channel → ℝ) k => μ k) o μ k = o.value k - μ k := rfl

/-- The error vanishes at every channel iff the observation vector is exactly
`g μ`. -/
theorem sensoryPredictionError_eq_zero_iff {M : Type*} (g : M → Channel → ℝ)
    (o : ObservationVector) (μ : M) :
    (∀ k, sensoryPredictionError g o μ k = 0) ↔ o.value = g μ := by
  constructor
  · intro h
    funext k
    exact sub_eq_zero.mp (h k)
  · intro h k
    rw [sensoryPredictionError, h]
    ring

/-! ### Bridge to the producer

`machineChannelPredictionError` gates on a variance that eq. (46) does not
mention. On its present branch, and only there, its `error` field computes
(46) with predicted mean `g μ k`. -/

/-- The present record's `error` field equals eq. (46) whenever the observed
value and the predicted mean match the equation's operands. -/
theorem presentRecord_error_eq_eq46 (minVariance ob m v : ℝ) {M : Type*}
    (g : M → Channel → ℝ) (o : ObservationVector) (μ : M) (k : Channel)
    (hobs : o.value k = ob) (hg : g μ k = m) :
    (presentRecord minVariance ob m v).error = sensoryPredictionError g o μ k := by
  simp [presentRecord, sensoryPredictionError, hobs, hg]

/-- THE BRIDGE. On real operands the producer returns `Outcome.present r` with
`r.error = ob - m` (see `present_eq`, `presentRecord`), and that number is
eq. (46) at any `g μ` whose value at `k` is `m` and any observation vector
whose value at `k` is `ob`. The variance `v` and the floor `minVariance` are
gating and precision, not the equation. -/
theorem machine_present_computes_eq46 (minVariance ob m v : ℝ) {M : Type*}
    (g : M → Channel → ℝ) (o : ObservationVector) (μ : M) (k : Channel)
    (hobs : o.value k = ob) (hg : g μ k = m) :
    ∃ r, machineChannelPredictionError minVariance (Field.value ob)
          ⟨Field.value m, Field.value v⟩ = Outcome.present r
        ∧ r.error = sensoryPredictionError g o μ k :=
  ⟨presentRecord minVariance ob m v, present_eq minVariance ob m v,
    presentRecord_error_eq_eq46 minVariance ob m v g o μ k hobs hg⟩

/-! ### The audit's counterexample (A2 §2): observation 3, mean 1, variance missing

The producer refuses; the equation has all its operands and returns 2. -/

/-- The complete observation vector carrying the same real number at every
channel. -/
def constObservation (x : ℝ) : ObservationVector := ⟨fun _ => x⟩

/-- The producer's refusal: a missing variance is not in eq. (46), and it
empties the update. -/
theorem audit_counterexample_producer_refuses :
    ∃ l, machineChannelPredictionError defaultMinVariance (Field.value 3)
        ⟨Field.value 1, Field.missing⟩ = Outcome.refused l :=
  ⟨offences (Field.value 3) ⟨Field.value 1, Field.missing⟩, rfl⟩

/-- The equation has all its operands and returns 2 at every channel. -/
theorem audit_counterexample_eq_value (k : Channel) :
    sensoryPredictionError (fun (μ : Channel → ℝ) k => μ k) (constObservation 3)
        (fun _ => 1) k = 2 := by
  simp only [sensoryPredictionError, constObservation]
  norm_num

end DarkTower.WarMachine.SensoryPredictionError
