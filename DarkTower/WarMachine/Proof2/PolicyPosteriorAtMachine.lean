import DarkTower.WarMachine.PolicyPosterior
import DarkTower.WarMachine.MachineTemperature
import DarkTower.WarMachine.PolicyVariationalFreeEnergy

/-!
# The policy posterior at the machine's own τ and F(π) (W1, registry `:policy-posterior`)

WM-LEAN-ABSENT-TRIAGE-D (`futon2 57849fb9`) §3 W1. `PolicyPosterior.softmaxWithFPi`
states Q(π) ∝ exp(ln E(π) − G(π)/τ − F_π(π)) with `tau` and `fPi` as FREE
PARAMETERS, and imports only `Holes`; `MachineTemperature.machineTemperature` and
`PolicyVariationalFreeEnergy.variationalFreeEnergy` state the machine's own values
for those two parameters. Nothing applied the one to the other, so the registry
edges R14→R6 (τ) and R8→R6 (F_π) had a term present in the consumer's signature
and no import behind it. This module is that application.

## The two absences this module carries, and why neither may default

The triage required the error arm to be carried as a typed absence rather than
given a default τ. Reading the two producers turns up a second one, of the same
shape:

* **τ.** `machineTemperature` returns `Except TemperatureError ℝ`. The refusal
  (`invalidVariationalBeta`) is one absence. But `softmaxWithFPi` also demands
  `htau : 0 < tau`, and THE OK ARM DOES NOT SUPPLY IT in general:
  `variationalOkIsPositive` discharges positivity from the machine's own guard
  on the variational arm, and `gainOnlyOkIsZeroAtDegenerateFloor` exhibits an
  ok τ of zero on an engineering arm. So `machineTau` carries
  `TauAbsence.nonPositive` as well, and `engineeringOkPositiveOfFloor` states
  the hypothesis ON THE MACHINE that would discharge it (a positive floor).

* **F(π).** `variationalFreeEnergy` is `EReal`-valued, and is `⊤` exactly when
  the approximate posterior puts mass where the joint is zero
  (`PolicyVariationalFreeEnergy.vfe_eq_top_of_impossible`). `softmaxWithFPi`
  needs a real. `EReal.toReal ⊤ = 0`, and zero is the BEST attainable F, so
  coercing would turn "this policy's outcome is impossible" into "this policy
  fits perfectly" and would raise its posterior weight
  (`defaultingInfiniteFIsTheBestScore`). That is why the ⊤ case is refused by
  name instead.

## What this module does not claim

It does not claim the machine computes F(π) on the live path. It does not:
`policy_prefix_evidence/production-ranked` strips `:f` from every ranked entry
and stamps `:f-prefix :not-supplied`, which the registry row records as
`:policy-free-energy`'s `:live-status :not-computed-on-live-path` (futon2
`f39bf0a1`). This is the posterior the machine SHOULD compute, stated at the
machine's own terms so that the gap between it and the running code is a
difference between two written things rather than between a written thing and
an absence.

Nor does it state where the habit prior E(π) comes from: `hhabit` is passed
through to `softmaxWithFPi` unexamined, and the registry's own
`:enactment-habit` row carries `:latex-absent` for the counting rule.
-/

namespace DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

open DarkTower.WarMachine

noncomputable section

variable {PolicyIndex : Type*}

/-! ## Typed absences -/

/-- The two ways the machine fails to supply a temperature `softmaxWithFPi` can
use: its own refusal, and an ok value that is not positive. -/
inductive TauAbsence where
  | refused (e : MachineTemperature.TemperatureError)
  | nonPositive (tau : ℝ)

/-- Everything that stops the machine's posterior from being a distribution.
Each arm NAMES what is missing; none of them stands a value in for it. -/
inductive Absence (PolicyIndex : Type*) where
  | tau (a : TauAbsence)
  | infiniteFreeEnergy (π : PolicyIndex)

/-! ## τ at the machine, with positivity carried rather than assumed -/

/-- `machineTemperature`'s value together with the positivity `softmaxWithFPi`
requires, or the absence that stopped it. The subtype is the point: a caller
cannot obtain the number without the proof. -/
def machineTau (opts : MachineTemperature.TemperatureOpts) :
    Except TauAbsence {t : ℝ // 0 < t} :=
  match MachineTemperature.machineTemperature opts with
  | .error e => .error (.refused e)
  | .ok t => if ht : 0 < t then .ok ⟨t, ht⟩ else .error (.nonPositive t)

/-- **The guarantee, where it exists.** On the variational arm every ok value is
positive, because that arm's own guard is `if 0 < beta`
(`MachineTemperature.lean:46-50`). This is what discharges `htau` for R14→R6. -/
theorem variationalOkIsPositive (opts : MachineTemperature.TemperatureOpts)
    (hmode : opts.mode = .variationalBetaGamma) (t : ℝ)
    (hok : MachineTemperature.machineTemperature opts = .ok t) : 0 < t := by
  rw [MachineTemperature.machineTemperature, hmode] at hok
  cases hbeta : opts.variationalBeta with
  | none => rw [hbeta] at hok; exact absurd hok (by simp)
  | some n =>
    cases n with
    | nonfinite => rw [hbeta] at hok; exact absurd hok (by simp)
    | finite beta =>
      rw [hbeta] at hok
      by_cases hb : 0 < beta
      · simp only [hb, if_true, Except.ok.injEq] at hok
        exact hok ▸ hb
      · simp only [hb, if_false] at hok
        exact absurd hok (by simp)

/-- So on the variational arm with a positive β, `machineTau` succeeds, and the
value it carries is β itself. -/
theorem variationalMachineTau (tauMin spread gain beta : ℝ) (hbeta : 0 < beta) :
    (machineTau ⟨.variationalBetaGamma, tauMin, spread, gain,
      some (.finite beta)⟩).map Subtype.val = .ok beta := by
  simp [machineTau, MachineTemperature.machineTemperature, hbeta, Except.map]

/-- **And the guarantee does not extend to the other two arms.** With the floor
and the gain both zero the gain-only law divides by zero, which in `ℝ` is zero,
so the machine returns `.ok 0` — an ok temperature that `softmaxWithFPi` cannot
take. -/
theorem gainOnlyOkIsZeroAtDegenerateFloor :
    MachineTemperature.machineTemperature ⟨.selectionGainOnly, 0, 0, 0, none⟩ = .ok 0 := by
  simp [MachineTemperature.machineTemperature]

/-- That value is refused BY NAME rather than nudged to something usable. -/
theorem degenerateFloorIsRefused :
    machineTau ⟨.selectionGainOnly, 0, 0, 0, none⟩ = .error (.nonPositive 0) := by
  simp [machineTau, gainOnlyOkIsZeroAtDegenerateFloor]

/-- **The hypothesis on the machine that would discharge positivity for the
engineering arms**, since no theorem about them can: a positive floor. Production
sets `tauMin = 1/100` (`policy.clj:33-45`), so the hypothesis holds there — but it
is a property of the CALLER's options, not of `machineTemperature`. -/
theorem gainOnlyOkPositiveOfFloor (tauMin spread gain : ℝ) (hmin : 0 < tauMin) (t : ℝ)
    (hok : MachineTemperature.machineTemperature ⟨.selectionGainOnly, tauMin, spread, gain, none⟩
      = .ok t) : 0 < t := by
  simp only [MachineTemperature.machineTemperature, Except.ok.injEq] at hok
  subst hok
  exact div_pos one_pos (lt_of_lt_of_le hmin (le_max_left _ _))

/-- The spread arm needs its numerator positive as well. -/
theorem spreadOkPositiveOfFloor (tauMin spread gain : ℝ) (hmin : 0 < tauMin)
    (hspread : 0 < spread) (t : ℝ)
    (hok : MachineTemperature.machineTemperature ⟨.spread, tauMin, spread, gain, none⟩
      = .ok t) : 0 < t := by
  simp only [MachineTemperature.machineTemperature, Except.ok.injEq] at hok
  subst hok
  exact div_pos hspread (lt_of_lt_of_le hmin (le_max_left _ _))

/-! ## F(π) at the machine, with the infinite arm refused -/

/-- The first policy of the list whose free energy is not finite, if any. -/
def firstInfinite (F : PolicyIndex → EReal) : List PolicyIndex → Option PolicyIndex
  | [] => none
  | π :: rest => if F π = ⊤ ∨ F π = ⊥ then some π else firstInfinite F rest

/-- A list on which every free energy is finite has no first infinite member. -/
theorem firstInfinite_eq_none (F : PolicyIndex → EReal) (policies : List PolicyIndex)
    (h : ∀ π ∈ policies, F π ≠ ⊤ ∧ F π ≠ ⊥) : firstInfinite F policies = none := by
  induction policies with
  | nil => rfl
  | cons a as ih =>
    have ha := h a (by simp)
    have hcond : ¬ (F a = ⊤ ∨ F a = ⊥) := by tauto
    simp only [firstInfinite]
    rw [if_neg hcond]
    exact ih (fun π hπ => h π (by simp [hπ]))

/-- `EReal.toReal ⊤ = 0`, and by `softmaxWithFPi`'s weight
`exp (ln E − G/τ − F_π)` a SMALLER `F_π` is a LARGER weight, so zero is the most
favourable value the term can take. Coercing an infinite F would therefore give
the policy whose outcome is impossible the best possible fit; this is the
arithmetic reason `machineFPi` refuses instead. -/
theorem defaultingInfiniteFIsTheBestScore (lnE gOverTau : ℝ) :
    (⊤ : EReal).toReal = 0 ∧
    ∀ f : ℝ, 0 < f → Real.exp (lnE - gOverTau - f)
      < Real.exp (lnE - gOverTau - (⊤ : EReal).toReal) := by
  refine ⟨EReal.toReal_top, fun f hf => ?_⟩
  rw [EReal.toReal_top]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- F(π) as `softmaxWithFPi` needs it, or the policy whose F is infinite. -/
def machineFPi (F : PolicyIndex → EReal) (policies : List PolicyIndex) :
    Except (Absence PolicyIndex) (PolicyIndex → ℝ) :=
  match firstInfinite F policies with
  | some π => .error (.infiniteFreeEnergy π)
  | none => .ok fun π => (F π).toReal

/-! ## The instantiation -/

/-- **The machine's policy posterior**: `softmaxWithFPi` at `machineTemperature`'s
τ and at `variationalFreeEnergy`'s F, or the first absence that stopped it. The
`Except` is the whole point — there is no arm of this definition that returns a
list of weights built on a substituted value. -/
def machinePosterior (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) (hhabit : ∀ π, 0 < habit π)
    (hne : policies ≠ []) (hnodup : policies.Nodup) :
    Except (Absence PolicyIndex) (List ℝ) :=
  match machineTau opts with
  | .error a => .error (.tau a)
  | .ok t =>
    match machineFPi F policies with
    | .error a => .error a
    | .ok f =>
      .ok (PolicyPosterior.softmaxWithFPi habit grade f t.val policies hhabit t.prop hne hnodup)

/-- **W1's lemma.** On the ok arm the machine's posterior IS `softmaxWithFPi`, at
the τ the machine supplied and at the machine's own F. -/
theorem machinePosterior_eq_softmax (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) (hhabit : ∀ π, 0 < habit π)
    (hne : policies ≠ []) (hnodup : policies.Nodup)
    (t : ℝ) (ht : 0 < t)
    (hok : MachineTemperature.machineTemperature opts = .ok t)
    (hfin : firstInfinite F policies = none) :
    machinePosterior habit grade F opts policies hhabit hne hnodup
      = .ok (PolicyPosterior.softmaxWithFPi habit grade (fun π => (F π).toReal) t
          policies hhabit ht hne hnodup) := by
  simp [machinePosterior, machineTau, machineFPi, hok, ht, hfin]

/-- So on the ok arm it is a probability distribution: the weights are
nonnegative and sum to one, inherited from the carrier. -/
theorem machinePosterior_isDistribution (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) (hhabit : ∀ π, 0 < habit π)
    (hne : policies ≠ []) (hnodup : policies.Nodup) (weights : List ℝ)
    (hrun : machinePosterior habit grade F opts policies hhabit hne hnodup = .ok weights) :
    (∀ x ∈ weights, 0 ≤ x) ∧ weights.sum = 1 := by
  unfold machinePosterior at hrun
  cases htau : machineTau opts with
  | error a => rw [htau] at hrun; exact absurd hrun (by simp)
  | ok t =>
    rw [htau] at hrun
    cases hf : machineFPi F policies with
    | error a => rw [hf] at hrun; exact absurd hrun (by simp)
    | ok f =>
      rw [hf] at hrun
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact ⟨PolicyPosterior.softmaxWithFPi_nonneg habit grade f t.val policies hhabit
          t.prop hne hnodup,
        PolicyPosterior.softmaxWithFPi_sum_eq_one habit grade f t.val policies hhabit
          t.prop hne hnodup⟩

/-- **R14→R6 closed at the variational arm.** With a positive β the temperature
half cannot refuse, so the only absence left is F's. -/
theorem variationalPosteriorNeedsOnlyFiniteF (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (tauMin spread gain beta : ℝ) (hbeta : 0 < beta)
    (policies : List PolicyIndex) (hhabit : ∀ π, 0 < habit π)
    (hne : policies ≠ []) (hnodup : policies.Nodup)
    (hfin : firstInfinite F policies = none) :
    machinePosterior habit grade F
        ⟨.variationalBetaGamma, tauMin, spread, gain, some (.finite beta)⟩
        policies hhabit hne hnodup
      = .ok (PolicyPosterior.softmaxWithFPi habit grade (fun π => (F π).toReal) beta
          policies hhabit hbeta hne hnodup) :=
  machinePosterior_eq_softmax habit grade F _ policies hhabit hne hnodup beta hbeta
    (by simp [MachineTemperature.machineTemperature, hbeta]) hfin

/-- With F identically zero the machine's posterior is the frozen `Holes.softmax`
carrier at the machine's τ: the `F_π` term is an addition to the closed-by-record
object, not a replacement for it (`PolicyPosterior.softmaxWithFPi_zero`). -/
theorem machinePosterior_zeroF (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (opts : MachineTemperature.TemperatureOpts) (policies : List PolicyIndex)
    (hhabit : ∀ π, 0 < habit π) (hne : policies ≠ []) (hnodup : policies.Nodup)
    (t : ℝ) (ht : 0 < t)
    (hok : MachineTemperature.machineTemperature opts = .ok t) :
    machinePosterior habit grade (fun _ => 0) opts policies hhabit hne hnodup
      = .ok (Holes.softmax Real.exp Real.log habit grade t policies) := by
  rw [machinePosterior_eq_softmax habit grade (fun _ => 0) opts policies hhabit hne hnodup
    t ht hok (firstInfinite_eq_none _ _ (fun π _ => ⟨by simp, by simp⟩))]
  simp only [EReal.toReal_zero]
  rw [PolicyPosterior.softmaxWithFPi_zero habit grade t policies hhabit ht hne hnodup]

/-! ## The refusals are reachable

Each `Except` arm above is only worth having if the machine can actually reach
it. These two exhibit the inputs that do. -/

/-- **The τ refusal fires.** The variational arm with no β is
`machineTemperature`'s own `invalidVariationalBeta`
(`MachineTemperature.missingBetaNeverFallsBack`), and it reaches the caller as a
named absence rather than as a fallback temperature. -/
theorem missingBetaIsRefused (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (π₀ : PolicyIndex) (hhabit : ∀ π, 0 < habit π)
    (tauMin spread gain : ℝ) :
    machinePosterior habit grade F ⟨.variationalBetaGamma, tauMin, spread, gain, none⟩
        [π₀] hhabit (by simp) (by simp)
      = .error (.tau (.refused .invalidVariationalBeta)) := by
  simp [machinePosterior, machineTau, MachineTemperature.machineTemperature]

/-- **The non-positive-τ refusal fires**, on an arm that `machineTemperature`
itself accepts: the degenerate floor of `degenerateFloorIsRefused`, carried
through the posterior. -/
theorem degenerateFloorRefusesThePosterior (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (π₀ : PolicyIndex) (hhabit : ∀ π, 0 < habit π) :
    machinePosterior habit grade F ⟨.selectionGainOnly, 0, 0, 0, none⟩
        [π₀] hhabit (by simp) (by simp)
      = .error (.tau (.nonPositive 0)) := by
  simp [machinePosterior, degenerateFloorIsRefused]

/-- **The infinite-F refusal fires**, and names the policy. τ is supplied here
(a positive β), so this is F's absence alone: the posterior refuses rather than
scoring the impossible policy at `EReal.toReal ⊤ = 0`. -/
theorem infiniteFIsRefused (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (π₀ : PolicyIndex) (hhabit : ∀ π, 0 < habit π)
    (tauMin spread gain beta : ℝ) (hbeta : 0 < beta) :
    machinePosterior habit grade (fun _ => ⊤)
        ⟨.variationalBetaGamma, tauMin, spread, gain, some (.finite beta)⟩
        [π₀] hhabit (by simp) (by simp)
      = .error (.infiniteFreeEnergy π₀) := by
  simp [machinePosterior, machineTau, MachineTemperature.machineTemperature, hbeta,
    machineFPi, firstInfinite]

#print axioms missingBetaIsRefused
#print axioms degenerateFloorRefusesThePosterior
#print axioms infiniteFIsRefused
#print axioms machineTau
#print axioms variationalOkIsPositive
#print axioms variationalMachineTau
#print axioms gainOnlyOkIsZeroAtDegenerateFloor
#print axioms degenerateFloorIsRefused
#print axioms gainOnlyOkPositiveOfFloor
#print axioms spreadOkPositiveOfFloor
#print axioms firstInfinite
#print axioms firstInfinite_eq_none
#print axioms defaultingInfiniteFIsTheBestScore
#print axioms machineFPi
#print axioms machinePosterior
#print axioms machinePosterior_eq_softmax
#print axioms machinePosterior_isDistribution
#print axioms variationalPosteriorNeedsOnlyFiniteF
#print axioms machinePosterior_zeroF

end

end DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
