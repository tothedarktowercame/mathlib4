import DarkTower.AIF.Terms

/-!
# Run certificates — certifying nondeterministic runtime computations

Commissioned by Joe, 2026-09-18: "the implemented Clojure code should be
able to give us data that we can certify using exactly this Lean
specification ... even though the computations themselves are
non-deterministic. The outlines and shapes and data types and results
should match. And we should be able to detect whether or not risk has been
computed."

A **certificate** is a typed per-run record the producer emits and Lean
checks. Three design rules, each answering one of Joe's requirements:

1. **Nondeterminism**: the certificate binds *this run's* recorded inputs
   and outputs; validity is a functional relation on the recorded values
   (shapes, types, arithmetic within a declared float tolerance — the
   row-12 IEEE-correspondence precedent), never trajectory reproducibility.
2. **Presence is structural.** No specified quantity is optional: a
   certificate without a per-step risk value does not elaborate. "Computed,
   value 0", "identically 0 by a named reduction", and "neutral by
   declaration" are *distinct constructors* (`QuantityStatus`), because
   today they are indistinguishable in the emitted record — verified on the
   live path 2026-09-18 (claude-4): per-τ risk in `horizon-g-sparse` is a
   local summed and discarded; zero-rate ambiguity is identically 0 by the
   identity-A reduction, so "computed 0" and "never computed" emit the same
   bytes.
3. **Declared reductions are recorded, not assumed.** The constant-C form,
   the zero-rates precondition, the caller-declared β, the neutral E and F
   — each is a certificate field, so the certified claim is exactly the
   reduced law that ran, and a run under constant C can never be mistaken
   for a witness of the step-indexed law.

The exemplar is `GCertificate` — the G-over-cascades computation, Joe's
named example and the production decision path. The same pattern extends
per equation row. The Clojure emission that fills this shape is a
follow-on work item (the certifiable surface today is one scalar G per
candidate); this module is the specification that emission must meet.
-/

namespace DarkTower.AIF

/-- How a specified quantity came to its recorded value. The distinction
between these constructors is the absence-detection requirement: a value
of `0` alone cannot carry it. -/
inductive QuantityStatus
  | /-- The producer executed the defining computation. -/
    computed
  | /-- A named, declared reduction makes the value identically zero on
    this run's inputs (e.g. ambiguity under identity-A at zero rates). -/
    reducedIdenticallyZero (reduction : String)
  | /-- The term was supplied as a declared-neutral input (e.g. `E = 1`,
    `F = 0`), not computed. -/
    declaredNeutral
  | /-- Computed, found non-finite under a declared degenerate
    configuration, and deliberately NOT attached to the law (WIRE-2
    review, 2026-09-18: under identity-A every producing cascade has
    `P(o|π) = 0`, so `F = ∞`; attaching it drove the posterior to NaN
    for every candidate). The ℝ-typed certificate field then records the
    neutral value that DID enter the law; the non-finite computed value
    stays in the run record, whose Lean home is `horizonEFE_eq_top_iff`,
    not finite arithmetic. The term starts flowing on its own when the
    degenerate configuration ends — a declared current limitation, not
    theory. -/
    computedNotAttached (reason : String)
  deriving DecidableEq, Repr

/-- Which preference form supplied C on this run: the declared constant
spec, or a genuinely step-indexed family. A constant-C run certifies only
the constant-case reduction. -/
inductive CForm
  | constantSpec
  | stepIndexed
  deriving DecidableEq, Repr

/-- One horizon step of a G computation: risk and ambiguity as distinct
recorded values, each with its status. Today's producer computes this pair
and discards it into the running sum; the certificate makes each step a
recorded fact. -/
structure GStep where
  risk : ℝ
  riskStatus : QuantityStatus
  ambiguity : ℝ
  ambiguityStatus : QuantityStatus

/-- The per-candidate certificate for a G-over-cascades computation.
Every field is mandatory — absence of a specified quantity is an
elaboration failure, not a silent default. -/
structure GCertificate where
  /-- Declared horizon `T`. -/
  horizon : ℕ
  /-- The steps actually iterated (length is checked against `horizon`). -/
  steps : List GStep
  /-- The emitted total G. -/
  total : ℝ
  /-- Which C form ran. -/
  cForm : CForm
  /-- The zero-adjudication-rates precondition, as observed on this run. -/
  ratesAllZero : Bool
  /-- Size of the token universe the computation ranged over. -/
  universeSize : ℕ

/-- Validity of a G certificate at float tolerance `ε`: the shape, the
arithmetic, and the honesty conditions. This is the specification the
emission must meet; a producer that never computed per-step risk cannot
fabricate a passing certificate without asserting `computed` falsely —
which moves the failure from undetectable to a lie in a checked record. -/
def GCertificate.valid (ε : ℝ) (c : GCertificate) : Prop :=
  -- shape: the steps actually iterated match the declared horizon
  c.steps.length = c.horizon ∧ 0 < c.horizon ∧
  -- arithmetic: the emitted total is the sum of the recorded steps
  |c.total - (c.steps.map (fun s => s.risk + s.ambiguity)).sum| ≤ ε ∧
  -- honesty: a named zero-reduction must actually record zero
  (∀ s ∈ c.steps, ∀ r, s.ambiguityStatus = .reducedIdenticallyZero r →
    s.ambiguity = 0) ∧
  -- the zero-rate reduction is admissible only if the precondition held
  ((∃ s ∈ c.steps, ∃ r, s.ambiguityStatus = .reducedIdenticallyZero r) →
    c.ratesAllZero = true)

/-- **Correction record (WIRE-1 review, 2026-09-18).** The first cut of
`GCertificate` carried `betaDeclared`, `habit` and `f`. The census (D2)
located β on the cascade problem, read at the SELECTION seam — it is not
an input of the G computation, and the emission slice could not fill it
truthfully at the G seam. The spec now follows the term structure: the
G certificate carries the computation's fields; `SelectionCertificate`
carries the selection law's inputs, assembled where they live. -/
structure SelectionCertificate where
  /-- Caller-declared β (no default exists in production; a certificate
  with β requires it positive). -/
  betaDeclared : ℝ
  /-- Habit input and how it arose. -/
  habit : ℝ
  habitStatus : QuantityStatus
  /-- Per-policy F input and how it arose. -/
  f : ℝ
  fStatus : QuantityStatus

/-- Validity of a selection certificate: β positive (PolicyTemperature's
own constraint), declared-neutral statuses honest about their values, and
a computed-not-attached F honest that the value which entered the law was
the neutral one (the non-finite computed value lives in the run record,
not in this ℝ field). -/
def SelectionCertificate.valid (c : SelectionCertificate) : Prop :=
  0 < c.betaDeclared ∧
  (c.habitStatus = .declaredNeutral → c.habit = 1) ∧
  (c.fStatus = .declaredNeutral → c.f = 0) ∧
  (∀ r, c.fStatus = .computedNotAttached r → c.f = 0)

/-- A certificate whose every step's risk is `computed` witnesses that risk
was computed at every step — Joe's detectability example, as a predicate. -/
def GCertificate.riskComputedThroughout (c : GCertificate) : Prop :=
  ∀ s ∈ c.steps, s.riskStatus = .computed

/-! ## The identity-A reduction: a conditional, not an endorsement

**Status: KNOWN-FAILING relative to the full theory (Joe, 2026-09-18).**
The theorems below prove a conditional: IF the likelihood is
deterministic, THEN ambiguity vanishes identically. They exist so that a
certificate claiming the `"identity-A-zero-rates"` reduction commits the
checker only to the premise, never to unverified arithmetic — without
them, a false reduction claim would be accepted. They do NOT prove the
production behaviour realises the theory. The theory (book eq. 4.9) has
`G = risk + ambiguity`; under the current deterministic-A configuration
the epistemic half is identically inert, so this is a known-failing test
against the full decomposition — held in the same spirit as any
known-failing test: honestly red, with the passing condition not yet
fully specified. REFINED by the D3/T3 census round (2026-09-18): the
non-degenerate forms are BUILT — `token-likelihood` with error rates
(matching Lean `TokenObservation`), `observation-rates` (real rates from
admitted-label error counts), `likelihood-precision`'s `temper-a` (this
module's `temperedLikelihood`, R7's shape) — and none has a live
consumer; the live call site constructs identity rates itself and the
sparse evaluator refuses non-zero rates as
`:judgement-rates-not-supported-at-scale`. What makes this pass is
therefore a SCALABLE non-degenerate evaluation path plus wiring the
built producers — an engineering sequencing matter on the closure DAG,
not new modeling. This is a theory-conformance fact, not a matter of
operator opinion. -/

section IdentityReduction

open DarkTower.WarMachine.PolicyRollout DarkTower.WarMachine.PolicyHorizon

variable {S O U : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- A deterministic likelihood row (every entry 0 or 1) has zero entropy. -/
theorem rowEntropy_of_deterministic (M : ForwardModel S O U) (s : S)
    (h : ∀ o, M.A s o = 0 ∨ M.A s o = 1) : rowEntropy M s = 0 := by
  simp only [rowEntropy]
  rw [Finset.sum_eq_zero, neg_zero]
  intro o _
  rcases h o with h0 | h1
  · rw [h0, zero_mul]
  · rw [h1, Real.log_one, mul_zero]

/-- The identity-A reduction: with a deterministic likelihood, ambiguity is
identically zero at every horizon step — "the live G is the risk half only"
as a theorem rather than a remark. -/
theorem stepAmbiguity_eq_zero_of_deterministic (M : ForwardModel S O U)
    (h : ∀ s o, M.A s o = 0 ∨ M.A s o = 1) (σ : ℕ → U) (n : ℕ) :
    stepAmbiguity M σ n = 0 := by
  simp only [stepAmbiguity]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [rowEntropy_of_deterministic M s (h s), mul_zero]

end IdentityReduction

end DarkTower.AIF
