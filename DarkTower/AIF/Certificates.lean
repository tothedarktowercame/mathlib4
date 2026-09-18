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
  /-- Caller-declared β (there is deliberately no default in production). -/
  betaDeclared : ℝ
  /-- Habit input and how it arose. -/
  habit : ℝ
  habitStatus : QuantityStatus
  /-- Per-policy F input and how it arose. -/
  f : ℝ
  fStatus : QuantityStatus
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

/-- A certificate whose every step's risk is `computed` witnesses that risk
was computed at every step — Joe's detectability example, as a predicate. -/
def GCertificate.riskComputedThroughout (c : GCertificate) : Prop :=
  ∀ s ∈ c.steps, s.riskStatus = .computed

end DarkTower.AIF
