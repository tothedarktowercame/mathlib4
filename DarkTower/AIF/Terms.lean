import DarkTower.WarMachine.PolicyHorizon
import DarkTower.WarMachine.OutcomeRiskKL

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

Generative-model quintet (Parr–Pezzulo–Friston 2022; Da Costa 2020 Table 2):
- **A** (likelihood `P(o|s)`)   — `ForwardModel.A`, identified as `likelihood`.
- **B** (transition `P(s'|s,u)`) — `ForwardModel.B`, identified as `transition`.
- **C** (outcome preference)    — DEFINED here (`Preference`), the T-C task:
  previously only `Holes.lean` `def C … := sorry`, a type with no definition.
- **D** (initial-state prior)   — `ForwardModel.q₀`, identified as `initialBelief`.
- **E** (habit prior over policies) — DEFINED here (`Habit`); previously a
  bare function argument of `policyWeight`.

Predictions and functionals:
- `Q(s_τ|π)` — `PolicyRollout.rolloutState`; `Q(o_τ|π)` — `PolicyRollout.predictedOutcome`.
- risk — `PolicyHorizon.stepRisk`; ambiguity — `PolicyHorizon.stepAmbiguity`;
  **G** — `PolicyHorizon.horizonEFE = Σₙ (stepRisk + stepAmbiguity)`, wrapped
  here as `expectedFreeEnergy` over a `Preference`.
- policy posterior `σ(ln E − F − G)` — `OutcomeRiskKL.policyPosterior`,
  wrapped here over a `Habit`.

Census pointers not re-bound in this module (their audited carriers):
- **F** (variational free energy) — registry `:free-energy`, MATCHES 09-16
  (Buckley eq. 45 reduction); carrier per registry row.
- **β/γ** (policy precision) — registry `:temperature`.
- **ζ** (likelihood precision, Gibbs inverse temperature on A) — registry
  `:likelihood-precision`, declared futon2 `fe55a1a0`; Lean row still OPEN.

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
read by `stepRisk` at each horizon step. Log-preferences are potentials, not
probabilities — no normalisation is required by the theory (Parr–Pezzulo–
Friston 2022 treat `C` as log prior preference), which is why the only
structure field is the family itself; every *ruled content* for C (masses,
provenance, the discovery process) lives outside the definition, in the
operator's registry (`futon2:holes/NOTE-joes-view-of-C.md`). -/

/-- **C**: a step-indexed family `C_τ` of log-preferences over outcomes. -/
structure Preference (O : Type*) where
  /-- `log τ o`: log-preference for outcome `o` at horizon step `τ`. -/
  log : ℕ → O → ℝ

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

/-- The policy posterior `σ(ln E − F − G)` over a `Habit`, delegating to the
audited `OutcomeRiskKL.policyPosterior`. -/
noncomputable def policyPosterior {P : Type*} [Fintype P] (E : Habit P)
    (F : P → ℝ) (G : P → EReal) (π : P) : ENNReal :=
  DarkTower.WarMachine.OutcomeRiskKL.policyPosterior E.weight F G π

end DarkTower.AIF
