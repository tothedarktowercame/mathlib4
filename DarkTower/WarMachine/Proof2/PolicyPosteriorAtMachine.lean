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
  needs a real, and `EReal.toReal ⊤ = 0` — which is the BEST attainable F, so
  coercing would turn "this policy's outcome is impossible" into "this policy
  fits perfectly" and RAISE its posterior weight
  (`defaultingInfiniteFIsTheBestScore`). Coercion is therefore not the answer.
  But refusing the whole posterior is not the answer either, and W1's first
  version did: see below. A ⊤ policy's WEIGHT is `exp(−∞) = 0`, which is
  perfectly defined, and the posterior over the rest exists as long as one
  policy has finite F. That is what `machineWeights` does.
  Only `⊥` is refused by name, and only as a fact about the TYPE: a free energy
  of −∞ would be an infinitely good fit, and `variationalFreeEnergy` cannot
  produce one (`variationalFreeEnergyNeverBot`), so the arm exists because
  `EReal` admits it and not because the machine can reach it.

## W1b: why the infinite-F arm gives weight zero rather than refusing

W1's first version refused the WHOLE posterior when any policy's F was ⊤. That
was stricter than the definition, than the running code, and than this model's
own sibling law, and all three were checked before it was changed
(claude-8's review, `PROOF-2a-PLAN` ⟨2⟩1d):

* **The definition.** Parr 2022 B.9 is `π = σ(ln E − F − G)`. The softmax needs
  the WEIGHT, not F; the weight of a policy with `F = +∞` is `exp(−∞) = 0`,
  which is defined, and the distribution over the remainder exists whenever one
  policy has finite F.
* **This model already says so for the sibling term.**
  `PolicySelection.selectionWeight_top` gives a `G = ⊤` candidate weight zero and
  `PolicySelection.selectionPosterior_finite` normalises over the finite
  candidates only — over an EXTENDED `G` with a real `F`. Extending `F` is the
  same algebra. The earlier refusal made this module disagree with
  `PolicySelection` about the same construction.
* **The code.** `futon2:src/futon2/aif/cascade_selection.clj` `selection-posterior`
  ADMITS a candidate typed `:f-status :zero-support` with `:f nil`, puts it in the
  `infinite` set and gives it probability exactly `0.0`, normalising the rest
  among themselves; it refuses (`:no-admissible-candidate`) only when NO candidate
  is finite, and `:invalid-free-energy` only for an UNTYPED numeric `##Inf`. Its
  own docstring cites `PolicySelection.selectionPosterior_finite`.
* **SPEC-F** (`futon2:holes/labs/wm-contract/proof2/packets/SPEC-F.md`) does not
  ask for the refusal. What it forbids is exact and narrower: "The real-valued
  selection input requires a proved finite value; never use `EReal.toReal` to turn
  ⊤ into 0." That is the coercion `defaultingInfiniteFIsTheBestScore` refuses, and
  it is kept. SPEC-F treats impossible evidence as a TYPED ADMITTED case —
  "impossible evidence retains `:zero-support`, distinct from missing history" —
  not as grounds to refuse the decision.

So the guard went, as an unjustified guard should. What survives as a refusal is
what is genuinely undefined: no finite-F policy at all, hence no normaliser.

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
Each arm NAMES what is missing; none of them stands a value in for it. A policy
whose F is `⊤` is NOT here: it has weight zero and the others normalise without
it (see the W1b section above). -/
inductive Absence (PolicyIndex : Type*) where
  | tau (a : TauAbsence)
  /-- No policy has a finite F, so there is no normaliser and no distribution. -/
  | allFreeEnergiesInfinite
  /-- `F π = ⊥`: an infinitely GOOD fit, which is not a free energy.
  `variationalFreeEnergyNeverBot` shows the machine cannot reach this. -/
  | freeEnergyBot (π : PolicyIndex)

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

/-! ## F(π) at the machine: `⊤` weighs nothing, `⊥` is refused -/

/-- `F π` is a real number. -/
def FiniteF (F : PolicyIndex → EReal) (π : PolicyIndex) : Prop := F π ≠ ⊤ ∧ F π ≠ ⊥

instance (F : PolicyIndex → EReal) (π : PolicyIndex) : Decidable (FiniteF F π) := by
  unfold FiniteF; infer_instance

/-- The policies the posterior normalises over. -/
def finitePolicies (F : PolicyIndex → EReal) (policies : List PolicyIndex) : List PolicyIndex :=
  policies.filter fun π => decide (FiniteF F π)

/-- The first policy whose F is `⊥`, if any. -/
def firstBot (F : PolicyIndex → EReal) : List PolicyIndex → Option PolicyIndex
  | [] => none
  | π :: rest => if F π = ⊥ then some π else firstBot F rest

/-- A list on which no free energy is `⊥` has no first `⊥`. -/
theorem firstBot_eq_none (F : PolicyIndex → EReal) (policies : List PolicyIndex)
    (h : ∀ π ∈ policies, F π ≠ ⊥) : firstBot F policies = none := by
  induction policies with
  | nil => rfl
  | cons a as ih =>
    simp only [firstBot]
    rw [if_neg (h a (by simp))]
    exact ih fun π hπ => h π (by simp [hπ])

/-- `variationalFreeEnergy` returns `⊤` or a coerced real, never `⊥`
(`PolicyVariationalFreeEnergy.lean:42-50`). So `Absence.freeEnergyBot` exists
because `EReal` admits the value, not because the machine can produce it — which
is the whole of the reason `⊥` stays a refusal while `⊤` does not. -/
theorem variationalFreeEnergyNeverBot {S : Type*} [Fintype S] (lik prior q : S → ℝ) :
    PolicyVariationalFreeEnergy.variationalFreeEnergy lik prior q ≠ ⊥ := by
  unfold PolicyVariationalFreeEnergy.variationalFreeEnergy
  split
  · exact top_ne_bot
  · exact EReal.coe_ne_bot _

/-- `EReal.toReal ⊤ = 0`, and by `softmaxWithFPi`'s weight
`exp (ln E − G/τ − F_π)` a SMALLER `F_π` is a LARGER weight, so zero is the most
favourable value the term can take. Coercing an infinite F would therefore give
the policy whose outcome is impossible the best possible fit. That is why
`machineWeights` gives it weight ZERO — `exp (−∞)`, the value the definition
assigns — rather than the weight `EReal.toReal` would produce. -/
theorem defaultingInfiniteFIsTheBestScore (lnE gOverTau : ℝ) :
    (⊤ : EReal).toReal = 0 ∧
    ∀ f : ℝ, 0 < f → Real.exp (lnE - gOverTau - f)
      < Real.exp (lnE - gOverTau - (⊤ : EReal).toReal) := by
  refine ⟨EReal.toReal_top, fun f hf => ?_⟩
  rw [EReal.toReal_top]
  exact Real.exp_lt_exp.mpr (by linarith)

/-! ## The weights -/

/-- One policy's unnormalised softmax weight, at the machine's τ and F. This is
`softmaxWithFPi`'s own summand with `fPi π = (F π).toReal`. -/
def weight (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (tau : ℝ) (π : PolicyIndex) : ℝ :=
  Real.exp (Real.log (habit π) - (grade π).value / tau - (F π).toReal)

/-- The normaliser: the total weight of the FINITE-F policies only, which is
what `PolicySelection.selectionPosterior_finite` normalises over. -/
def normaliser (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (tau : ℝ) (policies : List PolicyIndex) : ℝ :=
  ((finitePolicies F policies).map (weight habit grade F tau)).foldl (· + ·) 0

/-- **The machine's posterior weights**, aligned with `policies`: `exp (−∞) = 0`
at an infinite F, and the normalised softmax weight otherwise. -/
def machineWeights (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (tau : ℝ) (policies : List PolicyIndex) : List ℝ :=
  policies.map fun π =>
    if FiniteF F π then weight habit grade F tau π / normaliser habit grade F tau policies else 0

/-- A list of `if p then w/c else 0` sums to the filtered total over `c`. -/
theorem sum_map_ite_div (F : PolicyIndex → EReal) (w : PolicyIndex → ℝ) (c : ℝ)
    (l : List PolicyIndex) :
    (l.map fun π => if FiniteF F π then w π / c else 0).sum
      = ((l.filter fun π => decide (FiniteF F π)).map w).sum / c := by
  induction l with
  | nil => simp
  | cons a as ih =>
    by_cases h : FiniteF F a
    · simp only [List.map_cons, List.sum_cons, if_pos h, List.filter_cons,
        decide_eq_true_eq, ih]
      rw [add_div]
    · simp only [List.map_cons, List.sum_cons, if_neg h, List.filter_cons,
        decide_eq_true_eq, ih, zero_add]

/-- The normaliser is strictly positive as soon as one policy has finite F. -/
theorem normaliser_pos (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (tau : ℝ) (policies : List PolicyIndex)
    (hfin : finitePolicies F policies ≠ []) :
    0 < normaliser habit grade F tau policies := by
  unfold normaliser
  cases hl : finitePolicies F policies with
  | nil => exact absurd hl hfin
  | cons a as =>
    simp only [List.map_cons, List.foldl_cons]
    refine PolicyPosterior.foldl_add_pos_of_pos (by unfold weight; positivity) ?_
    intro x hx
    obtain ⟨π, _, hπ⟩ := List.mem_map.mp hx
    subst hπ
    unfold weight
    exact Real.exp_pos _

/-! ## The instantiation -/

/-- **The machine's policy posterior**: `softmaxWithFPi`'s weights at
`machineTemperature`'s τ and at `variationalFreeEnergy`'s F, with a `⊤` policy
at weight zero and the rest normalised among themselves. The `Except` carries
only what is genuinely undefined. -/
def machinePosterior (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) :
    Except (Absence PolicyIndex) (List ℝ) :=
  match machineTau opts with
  | .error a => .error (.tau a)
  | .ok t =>
    match firstBot F policies with
    | some π => .error (.freeEnergyBot π)
    | none =>
      if finitePolicies F policies = [] then .error .allFreeEnergiesInfinite
      else .ok (machineWeights habit grade F t.val policies)

/-- **W1's lemma, kept for the all-finite case.** When every policy has a finite
F the machine's posterior IS `softmaxWithFPi`, at the τ the machine supplied and
at the machine's own F: no policy is excluded and the normaliser is the carrier's
own. -/
theorem machinePosterior_eq_softmax (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) (hhabit : ∀ π, 0 < habit π)
    (hne : policies ≠ []) (hnodup : policies.Nodup)
    (t : ℝ) (ht : 0 < t)
    (hok : MachineTemperature.machineTemperature opts = .ok t)
    (hall : ∀ π ∈ policies, FiniteF F π) :
    machinePosterior habit grade F opts policies
      = .ok (PolicyPosterior.softmaxWithFPi habit grade (fun π => (F π).toReal) t
          policies hhabit ht hne hnodup) := by
  have hfilter : finitePolicies F policies = policies := by
    unfold finitePolicies
    exact List.filter_eq_self.mpr fun π hπ => by simpa using hall π hπ
  have hbot : firstBot F policies = none := firstBot_eq_none F policies fun π hπ => (hall π hπ).2
  have hnil : ¬ (finitePolicies F policies = []) := by rw [hfilter]; exact hne
  have hw : machineWeights habit grade F t policies
      = PolicyPosterior.softmaxWithFPi habit grade (fun π => (F π).toReal) t policies
          hhabit ht hne hnodup := by
    unfold machineWeights normaliser PolicyPosterior.softmaxWithFPi weight
    rw [hfilter, List.map_map]
    exact List.map_congr_left fun π hπ => if_pos (hall π hπ)
  simp only [machinePosterior, machineTau, hok, dif_pos ht, hbot, if_neg hnil, hw]

/-- Generic form: in a list of `if p then _ else 0`, the entries at the policies
where `p` fails are zero. Stated over an arbitrary normaliser `c`, because the
normaliser depends on the WHOLE list and so cannot be carried through an
induction on it. -/
theorem zip_map_ite_zero (F : PolicyIndex → EReal) (w : PolicyIndex → ℝ) (c : ℝ)
    (l : List PolicyIndex) :
    ∀ p ∈ l.zip (l.map fun π => if FiniteF F π then w π / c else 0),
      ¬ FiniteF F p.1 → p.2 = 0 := by
  induction l with
  | nil => simp
  | cons a as ih =>
    intro p hp hfin
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact if_neg hfin
    · exact ih p hp hfin

/-- **A `⊤` policy's weight is zero, at its own position.** Paired with the
policy list, every entry whose F is not finite is exactly `0` — which is
`exp (−∞)`, the value Parr B.9 gives it, not a substituted number. -/
theorem infiniteFHasZeroWeight (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (tau : ℝ) (policies : List PolicyIndex) :
    ∀ p ∈ policies.zip (machineWeights habit grade F tau policies),
      ¬ FiniteF F p.1 → p.2 = 0 :=
  zip_map_ite_zero F (weight habit grade F tau) (normaliser habit grade F tau policies) policies

/-- **And the rest still sum to one.** The weights are nonnegative and total one
whenever some policy has finite F — the infinite ones contributing exactly zero.
This is `PolicySelection.selectionPosterior_finite`'s statement for this carrier:
normalised over the finite candidates only. -/
theorem machineWeights_isDistribution (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (tau : ℝ) (policies : List PolicyIndex)
    (hfin : finitePolicies F policies ≠ []) :
    (∀ x ∈ machineWeights habit grade F tau policies, 0 ≤ x) ∧
    (machineWeights habit grade F tau policies).sum = 1 := by
  have hpos := normaliser_pos habit grade F tau policies hfin
  constructor
  · intro x hx
    obtain ⟨π, _, rfl⟩ := List.mem_map.mp hx
    by_cases h : FiniteF F π
    · rw [if_pos h]
      exact div_nonneg (by unfold weight; positivity) hpos.le
    · rw [if_neg h]
  · unfold machineWeights
    rw [sum_map_ite_div F (weight habit grade F tau) _ policies]
    have : ((policies.filter fun π => decide (FiniteF F π)).map
        (weight habit grade F tau)).sum = normaliser habit grade F tau policies := by
      unfold normaliser finitePolicies
      rw [PolicyPosterior.foldl_add_eq, zero_add]
    rw [this]
    exact div_self hpos.ne'

/-- **The posterior itself is a distribution on its ok arm.** -/
theorem machinePosterior_isDistribution (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) (weights : List ℝ)
    (hrun : machinePosterior habit grade F opts policies = .ok weights) :
    (∀ x ∈ weights, 0 ≤ x) ∧ weights.sum = 1 := by
  unfold machinePosterior at hrun
  cases htau : machineTau opts with
  | error a => simp only [htau] at hrun; exact absurd hrun (by simp)
  | ok t =>
    cases hbot : firstBot F policies with
    | some π => simp only [htau, hbot] at hrun; exact absurd hrun (by simp)
    | none =>
      by_cases hnil : finitePolicies F policies = []
      · simp only [htau, hbot, if_pos hnil] at hrun; exact absurd hrun (by simp)
      · simp only [htau, hbot, if_neg hnil, Except.ok.injEq] at hrun
        subst hrun
        exact machineWeights_isDistribution habit grade F t.val policies hnil

/-- **R14→R6 closed at the variational arm.** With a positive β the temperature
half cannot refuse, so the posterior stands as long as one policy has finite F. -/
theorem variationalPosteriorNeedsOnlyOneFiniteF (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (tauMin spread gain beta : ℝ) (hbeta : 0 < beta)
    (policies : List PolicyIndex)
    (hbot : firstBot F policies = none) (hfin : finitePolicies F policies ≠ []) :
    machinePosterior habit grade F
        ⟨.variationalBetaGamma, tauMin, spread, gain, some (.finite beta)⟩ policies
      = .ok (machineWeights habit grade F beta policies) := by
  simp [machinePosterior, machineTau, MachineTemperature.machineTemperature, hbeta,
    hbot, hfin]

/-- With F identically zero the machine's posterior is the frozen `Holes.softmax`
carrier at the machine's τ: the `F_π` term is an addition to the closed-by-record
object, not a replacement for it (`PolicyPosterior.softmaxWithFPi_zero`). -/
theorem machinePosterior_zeroF (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (opts : MachineTemperature.TemperatureOpts) (policies : List PolicyIndex)
    (hhabit : ∀ π, 0 < habit π) (hne : policies ≠ []) (hnodup : policies.Nodup)
    (t : ℝ) (ht : 0 < t)
    (hok : MachineTemperature.machineTemperature opts = .ok t) :
    machinePosterior habit grade (fun _ => 0) opts policies
      = .ok (Holes.softmax Real.exp Real.log habit grade t policies) := by
  rw [machinePosterior_eq_softmax habit grade (fun _ => 0) opts policies hhabit hne hnodup
    t ht hok (fun π _ => ⟨by simp, by simp⟩)]
  simp only [EReal.toReal_zero]
  rw [PolicyPosterior.softmaxWithFPi_zero habit grade t policies hhabit ht hne hnodup]

/-! ## A fixture: one impossible policy beside one possible one

The general theorems above say a `⊤` policy weighs nothing and the rest
normalise. This exhibits it on two policies, so the claim is not only about
shapes no input produces. -/

section Fixture

/-- Two policies: `true`'s free energy is `0`, `false`'s is `⊤` (its approximate
posterior puts mass where the joint is zero). -/
def fixtureF : Bool → EReal := fun b => if b then 0 else ⊤

/-- Unit habit mass and zero expected free energy, so the arithmetic is the
`F_π` term alone. -/
def fixtureHabit : Bool → ℝ := fun _ => 1

/-- Zero grade, so `G/τ` contributes nothing. -/
def fixtureGrade : Bool → Holes.ExpectedFreeEnergyValue := fun _ => ⟨0⟩

/-- **The impossible policy takes probability exactly zero and the possible one
takes all of it.** No refusal, and the two weights are a distribution. This is
what `cascade_selection.clj`'s `selection-posterior` does with a `:zero-support`
candidate, and what `PolicySelection.selectionPosterior_finite` states. -/
theorem fixtureWeights :
    machineWeights fixtureHabit fixtureGrade fixtureF 1 [true, false] = [1, 0] := by
  norm_num [machineWeights, normaliser, finitePolicies, FiniteF, weight,
    fixtureF, fixtureHabit, fixtureGrade]

end Fixture

/-! ## The refusals are reachable

Each `Except` arm above is only worth having if the machine can actually reach
it. These exhibit the inputs that do — and the fourth shows that the arm W1b
REMOVED is not reached, because a single infinite F no longer stops anything. -/

/-- **The τ refusal fires.** The variational arm with no β is
`machineTemperature`'s own `invalidVariationalBeta`
(`MachineTemperature.missingBetaNeverFallsBack`), and it reaches the caller as a
named absence rather than as a fallback temperature. -/
theorem missingBetaIsRefused (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (π₀ : PolicyIndex) (tauMin spread gain : ℝ) :
    machinePosterior habit grade F ⟨.variationalBetaGamma, tauMin, spread, gain, none⟩ [π₀]
      = .error (.tau (.refused .invalidVariationalBeta)) := by
  simp [machinePosterior, machineTau, MachineTemperature.machineTemperature]

/-- **The non-positive-τ refusal fires**, on an arm that `machineTemperature`
itself accepts: the degenerate floor of `degenerateFloorIsRefused`. -/
theorem degenerateFloorRefusesThePosterior (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (π₀ : PolicyIndex) :
    machinePosterior habit grade F ⟨.selectionGainOnly, 0, 0, 0, none⟩ [π₀]
      = .error (.tau (.nonPositive 0)) := by
  simp [machinePosterior, degenerateFloorIsRefused]

/-- **`allInfiniteIsRefused`: the one F refusal that survives, and it fires.**
Every policy at `⊤` leaves no normaliser, so there is no distribution to state —
this is a genuine absence, not a guard. -/
theorem allInfiniteIsRefused (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (π₀ : PolicyIndex) (tauMin spread gain beta : ℝ) (hbeta : 0 < beta) :
    machinePosterior habit grade (fun _ => ⊤)
        ⟨.variationalBetaGamma, tauMin, spread, gain, some (.finite beta)⟩ [π₀]
      = .error .allFreeEnergiesInfinite := by
  simp [machinePosterior, machineTau, MachineTemperature.machineTemperature, hbeta,
    firstBot, finitePolicies, FiniteF]

/-- **And `⊥` fires**, though `variationalFreeEnergyNeverBot` says the machine
cannot produce the input. -/
theorem botIsRefused (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (π₀ : PolicyIndex) (tauMin spread gain beta : ℝ) (hbeta : 0 < beta) :
    machinePosterior habit grade (fun _ => ⊥)
        ⟨.variationalBetaGamma, tauMin, spread, gain, some (.finite beta)⟩ [π₀]
      = .error (.freeEnergyBot π₀) := by
  simp [machinePosterior, machineTau, MachineTemperature.machineTemperature, hbeta, firstBot]

#print axioms machineTau
#print axioms variationalOkIsPositive
#print axioms variationalMachineTau
#print axioms gainOnlyOkIsZeroAtDegenerateFloor
#print axioms degenerateFloorIsRefused
#print axioms gainOnlyOkPositiveOfFloor
#print axioms spreadOkPositiveOfFloor
#print axioms FiniteF
#print axioms finitePolicies
#print axioms firstBot
#print axioms firstBot_eq_none
#print axioms variationalFreeEnergyNeverBot
#print axioms defaultingInfiniteFIsTheBestScore
#print axioms weight
#print axioms normaliser
#print axioms machineWeights
#print axioms sum_map_ite_div
#print axioms normaliser_pos
#print axioms machinePosterior
#print axioms machinePosterior_eq_softmax
#print axioms zip_map_ite_zero
#print axioms infiniteFHasZeroWeight
#print axioms fixtureF
#print axioms fixtureWeights
#print axioms machineWeights_isDistribution
#print axioms machinePosterior_isDistribution
#print axioms variationalPosteriorNeedsOnlyOneFiniteF
#print axioms machinePosterior_zeroF
#print axioms missingBetaIsRefused
#print axioms degenerateFloorRefusesThePosterior
#print axioms allInfiniteIsRefused
#print axioms botIsRefused

end

end DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
