import DarkTower.WarMachine.PolicyHorizon
import DarkTower.WarMachine.OutcomeRiskKL
import DarkTower.WarMachine.PolicyVariationalFreeEnergy

/-!
# AIF term census — declared formalism and fundamental terms

Commissioned by Joe, 2026-09-18: "I don't see how equations could be defined
if the terms that they contain are not defined. ... this is a matter of
getting the theory down and what the types are in the theory. ... we need to
declare that here and now, and then the implementation in Clojure will be
mapped to that so we can validate whether or not it's an implementation of
AIF or a made-up implementation of something else."

This module is the census: every fundamental AIF term either DEFINED here or
IDENTIFIED here, by name, with the audited declaration that carries it
(`futon2:holes/labs/wm-contract/aif-equations.edn` Leg A,
`AUDIT-lean-aif-equations-2026-09-16.md`). A term absent from this module is
a finding, not an oversight — the census is what makes "risk is never
computed in Clojure" a visible defect instead of folklore.

## Declared formalism

**Finite discrete active inference**: state, outcome and action spaces are
`Fintype`s; the generative model's components are row-stochastic matrices
over `ℝ` with their normalisation facts carried as structure fields
(`ForwardModel`, after Da Costa et al. 2020 Table 2,
`refs/dacosta2020.txt:316–322`; Parr, Pezzulo & Friston 2022's discrete-time
treatment). Divergences take values in `EReal`, so an impossible-outcome
risk is `⊤` — a typed fact, not an approximation. This matches the discrete
formulation the registry's equations cite and the finite-support
`ProbabilityKernel` repair (mathlib4 `480a666ad2`).

Markov categories were considered as the ambient formalism and are NOT
adopted now: the registry's Leg-A audit verdicts all bind concrete
stochastic-matrix statements, and a categorical reformulation would re-open
all 18 rows for no new checkable content at the current scope. The upgrade
path (states/outcomes as objects, `A`/`B` as Kleisli morphisms of the finite
distribution monad) is compatible with everything declared here; adopting it
is an operator decision, recorded here when taken.

## The census

Verified against the pinned book text
(`futon2:holes/labs/wm-contract/refs/parr2022.txt`, Parr–Pezzulo–Friston
2022) on 2026-09-18. The book's base discrete model has **four** key
ingredients, not five (its own words, `parr2022.txt:3801`): likelihood (A),
transitions (B), prior beliefs about observations (C), initial-state prior
(D) — eqs. 4.5–4.6, with the base policy posterior `π = σ(−G−F)` (eq. 4.14)
carrying **no habit term**. E is the habit *extension* (book ch. 4's
"habitual and goal-directed drives"; Friston et al. 2016 eq. 7), entering
as `σ(ln E − F − G)`:
- **A** (likelihood `P(o|s)`, eq. 4.5)   — `ForwardModel.A`, identified as `likelihood`.
- **B** (transition `P(s'|s,u)`, eq. 4.6) — `ForwardModel.B`, identified as `transition`.
- **C** (prior beliefs about observations, eq. 4.10 `P(oτ|C) = Cat(Cτ)`,
  `parr2022.txt:3764`) — DEFINED here (`Preference`), the T-C task:
  previously only `Holes.lean` `def C … := sorry`, a type with no definition.
- **D** (initial-state prior, eq. 4.6)   — `ForwardModel.q₀`, identified as
  `initialBelief`; consumed at `t = 0` by
  `ExactBeliefTrajectory.exactBeliefAt` (audited 2026-09-18).
- **E** (habit prior over policies, extension) — DEFINED here (`Habit`);
  previously a bare function argument of `policyWeight`.

Predictions and functionals:
- `Q(s_τ|π)` — `PolicyRollout.rolloutState`; `Q(o_τ|π)` — `PolicyRollout.predictedOutcome`.
- risk — `PolicyHorizon.stepRisk`; ambiguity — `PolicyHorizon.stepAmbiguity`;
  **G** — `PolicyHorizon.horizonEFE = Σₙ (stepRisk + stepAmbiguity)`, wrapped
  here as `expectedFreeEnergy` over a `Preference`.
- policy posterior — TWO theory-legitimate laws (census correction
  2026-09-18, T2): the base `σ(ln E − F − G)` (eq. 4.14 + habit;
  `OutcomeRiskKL.policyPosterior`, wrapped here) and the
  precision-tempered `σ(ln E − F − γG)`, `γ = 1/β` (book B.2.4;
  `PolicySelection.selectionPosterior`, wrapped in `AIF.Selection`).
  **Production implements the tempered law.** The first census cut bound
  only the base law; comparisons against production must use
  `AIF.Selection.temperedPolicyPosterior`.

Bound this pass (2026-09-18, second sitting):
- **F** (per-policy variational free energy, book eqs. B.1–B.2 / discrete
  form eq. 4.11) — `PolicyVariationalFreeEnergy.variationalFreeEnergy`,
  identified as `variationalFreeEnergy` below. (The registry's
  `:free-energy` row is the Buckley continuous form; the per-policy
  discrete F is `:policy-free-energy`.)
- **ζ** (likelihood precision: Gibbs inverse temperature on A, book B.2.4 —
  `parr2022.txt:12738` exponential prior, `:12779` normaliser
  `Z(ζ)ⱼ = Σᵢ (Aᵢⱼ)^ζ`) — DEFINED here (`temperedLikelihood`); this was the
  census's last OPEN Lean row among declared terms.

Census pointers not re-bound in this module (their audited carriers):
- **β/γ** (policy precision, book B.2.4 `parr2022.txt:12720`ff) — registry
  `:temperature`.

On C's second half (Joe, 2026-09-17, `futon2:holes/NOTE-joes-view-of-C.md`
§1): preference over *how* outcomes are pursued, regulated by institutions
(Ostrom deontics). That is a claim about trajectory- or policy-grain
preference and does NOT type as `Preference O` below. Whether it fits inside
AIF (as trajectory-grain C, as the habit prior E, as guards outside C), fits
partially, or cannot fit, is exactly the adjudication this census exists to
make decidable; it is OPEN and owed a typed answer, not prose.
-/

namespace DarkTower.AIF

open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.PolicyHorizon

variable {S O U : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-! ## A, B, D — identified with their audited carriers -/

/-- **A**, the likelihood `P(o|s)` (Da Costa 2020 Table 2). -/
def likelihood (M : ForwardModel S O U) : S → O → ℝ := M.A

theorem likelihood_nonneg (M : ForwardModel S O U) (s : S) (o : O) :
    0 ≤ likelihood M s o := M.A_nonneg s o

theorem likelihood_sum (M : ForwardModel S O U) (s : S) :
    ∑ o : O, likelihood M s o = 1 := M.A_colsum s

/-- **B**, the transition `P(s'|s,u)` (Da Costa 2020 Table 2). -/
def transition (M : ForwardModel S O U) : U → S → S → ℝ := M.B

theorem transition_nonneg (M : ForwardModel S O U) (u : U) (s s' : S) :
    0 ≤ transition M u s s' := M.B_nonneg u s s'

theorem transition_rowsum (M : ForwardModel S O U) (u : U) (s : S) :
    ∑ s' : S, transition M u s s' = 1 := M.B_rowsum u s

/-- **D**, the prior over initial hidden states (Da Costa 2020 Table 2). -/
def initialBelief (M : ForwardModel S O U) : S → ℝ := M.q₀

theorem initialBelief_nonneg (M : ForwardModel S O U) (s : S) :
    0 ≤ initialBelief M s := M.q₀_nonneg s

theorem initialBelief_sum (M : ForwardModel S O U) :
    ∑ s : S, initialBelief M s = 1 := M.q₀_sum

/-! ## C — the preference term, defined (T-C)

An admissible **C** is a step-indexed family of log-preferences over
outcomes: `log τ o` is the log-preference weight of outcome `o` at step `τ`,
read by `stepRisk` at each horizon step.

**Book-verification correction (2026-09-18):** the canonical C of the book
is NOT an unnormalised potential. Eq. 4.10 (`parr2022.txt:3764`) declares
`P(oτ | C) = Cat(Cτ)` — at every step, C parameterises a categorical
*distribution* over outcomes, and risk is the KL against it (eq. 4.9). The
log-form carrier below matches `stepRisk`'s reading; `IsCanonical` is the
book's admissibility. Working with an unnormalised family shifts each
step's risk by that step's log-normaliser — policy-independent, so rankings
survive, but the *value* of G is only the book's G when C is canonical;
any unnormalised use is a declared reduction, not a convention. Every
*ruled content* for C (masses, provenance, the discovery process) lives
outside the definition, in the operator's registry
(`futon2:holes/NOTE-joes-view-of-C.md`). -/

/-- **C**: a step-indexed family `C_τ` of log-preferences over outcomes. -/
structure Preference (O : Type*) where
  /-- `log τ o`: log-preference for outcome `o` at horizon step `τ`. -/
  log : ℕ → O → ℝ

/-- Book-canonical admissibility (eq. 4.10, `parr2022.txt:3764`): at every
step the preferences exponentiate to a probability distribution,
`P(oτ|C) = Cat(Cτ)`. -/
def Preference.IsCanonical (C : Preference O) : Prop :=
  ∀ τ : ℕ, ∑ o : O, Real.exp (C.log τ o) = 1

/-- The constant family: one log-preference vector declared at every step.
This is the reduction production currently runs (`horizon-g-sparse` with
`:spec`) — a declared special case, not a claim that `C_τ` is constant. -/
def Preference.constant (c : O → ℝ) : Preference O := ⟨fun _ => c⟩

omit [Fintype O] [DecidableEq O] in
@[simp] theorem Preference.constant_log (c : O → ℝ) (τ : ℕ) :
    (Preference.constant c).log τ = c := rfl

/-! ## E — the habit prior, defined -/

/-- **E**: the habit prior over policies — nonnegative weights, read by the
policy posterior as `σ(ln E − F − G)` (Friston et al. 2016 eq. 7;
`OutcomeRiskKL.policyWeight`). Not necessarily normalised: only ratios
survive the softmax. -/
structure Habit (P : Type*) where
  /-- Habit weight of policy `p`. -/
  weight : P → ℝ
  nonneg : ∀ p, 0 ≤ weight p

/-- The uniform habit (`E = 1`): the declared-neutral input production
passes today. Recorded as a named reduction precisely because the operator
is dubious of it (Joe, 2026-09-18) — a census name makes it auditable. -/
def Habit.uniform (P : Type*) : Habit P := ⟨fun _ => 1, fun _ => zero_le_one⟩

/-! ## G and the policy posterior, over the census types -/

/-- **G**: expected free energy of a depth-`T` policy against a preference
family — `Σₙ (risk against C_n + ambiguity)`, delegating to the audited
`PolicyHorizon.horizonEFE`. -/
noncomputable def expectedFreeEnergy (M : ForwardModel S O U) {T : ℕ}
    (hT : 0 < T) (π : Fin T → U) (C : Preference O) : EReal :=
  horizonEFE M hT π C.log

theorem expectedFreeEnergy_def (M : ForwardModel S O U) {T : ℕ} (hT : 0 < T)
    (π : Fin T → U) (C : Preference O) :
    expectedFreeEnergy M hT π C = horizonEFE M hT π C.log := rfl

/-- The BASE policy posterior `σ(ln E − F − G)` over a `Habit`, delegating
to the audited `OutcomeRiskKL.policyPosterior`. The book's base model
(eq. 4.14, no habit) is recovered at `Habit.uniform`. Production runs the
γ-tempered law instead — see `AIF.Selection.temperedPolicyPosterior`
(census correction 2026-09-18). -/
noncomputable def policyPosterior {P : Type*} [Fintype P] (E : Habit P)
    (F : P → ℝ) (G : P → EReal) (π : P) : ENNReal :=
  DarkTower.WarMachine.OutcomeRiskKL.policyPosterior E.weight F G π

/-! ## F — per-policy variational free energy, identified -/

/-- **F(π)** (book eqs. B.1–B.2, discrete form eq. 4.11): the per-policy
variational free energy, delegating to the audited carrier. `lik s = P(o|s)`
for the fixed observed outcome, `prior s = P(s|π)`, `q s = Q(s|π)`. -/
noncomputable def variationalFreeEnergy (lik prior q : S → ℝ) : EReal :=
  DarkTower.WarMachine.PolicyVariationalFreeEnergy.variationalFreeEnergy lik prior q

/-! ## ζ — likelihood precision, defined

Book B.2.4 (`parr2022.txt:12738`, `:12779`): the likelihood is tempered by
an inverse temperature `ζ`, `oτ^ζ = σ(ζ ln A) sτ`, i.e. each state's
outcome row of `A` is raised to `ζ` and renormalised by
`Z(ζ)ⱼ = Σᵢ (Aᵢⱼ)^ζ`. `ζ = 1` recovers `A`; `ζ → 0` flattens toward
uniform (imprecise likelihood); large `ζ` sharpens. -/

/-- The `ζ`-tempered likelihood `A^ζ / Z(ζ)` (book B.2.4). -/
noncomputable def temperedLikelihood (M : ForwardModel S O U) (ζ : ℝ)
    (s : S) (o : O) : ℝ :=
  M.A s o ^ ζ / ∑ o' : O, M.A s o' ^ ζ

/-- Some outcome has positive likelihood at every state (from `A`'s
normalisation), so the tempering normaliser is meaningful. -/
theorem exists_likelihood_pos (M : ForwardModel S O U) (s : S) :
    ∃ o : O, 0 < M.A s o := by
  by_contra h
  push Not at h
  have hzero : ∀ o : O, M.A s o = 0 :=
    fun o => le_antisymm (h o) (M.A_nonneg s o)
  have := M.A_colsum s
  simp only [hzero, Finset.sum_const_zero] at this
  exact zero_ne_one this

/-- The tempered likelihood is a distribution whenever the normaliser is
nonzero. -/
theorem temperedLikelihood_sum (M : ForwardModel S O U) (ζ : ℝ) (s : S)
    (hZ : (∑ o' : O, M.A s o' ^ ζ) ≠ 0) :
    ∑ o : O, temperedLikelihood M ζ s o = 1 := by
  simp only [temperedLikelihood]
  rw [← Finset.sum_div, div_self hZ]

/-- `ζ = 1` recovers the likelihood `A` exactly. -/
theorem temperedLikelihood_one (M : ForwardModel S O U) (s : S) (o : O) :
    temperedLikelihood M 1 s o = M.A s o := by
  simp only [temperedLikelihood, Real.rpow_one, M.A_colsum s, div_one]

end DarkTower.AIF
