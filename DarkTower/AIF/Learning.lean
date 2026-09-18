import DarkTower.AIF.Institutions
import DarkTower.WarMachine.DirichletLearning

/-!
# Learning — the slow loop, defined (not a hole)

Commissioned by Joe, 2026-09-18, by the same principle that settled C:
learning is a key part of AIF and its *definition* cannot be recorded as a
hole, even though its ruled content is harder to settle. Left blank and
unpointed, it either stays blank forever or someone invents a non-AIF
"learning module". This module defines what learning IS in the declared
formalism and types the targets Joe named, so every future learning design
lands somewhere specific.

## The doctrine (book, ch. 7; Da Costa 2020 eq. 21)

Learning is **slow inference**: the generative model's parameters are
themselves random variables, updated on a slower schedule than action.
The agent acts by active inference; outcomes accrue; parameters accumulate
outcome statistics — "we learn which kinds of actions align with our
preferences, or further our preferences, and which ones don't" (Joe,
2026-09-18). Three timescales, typed below as `Timescale`:

- **inference** — per-tick state estimation (the equation rows
  `:state-belief-update` etc.);
- **learning** — parameter accumulation (Dirichlet counts over A, and by
  the same pattern E; the audited carrier is
  `DirichletLearning.accumulate`, Da Costa eq. 21);
- **structural** — slowest: revision of the model's *structure*, evaluated
  by Bayesian model reduction (`ModelReduction.modelReductionDecision`).

## The ruled design shape (Joe, 2026-09-09, E-C-realization 22nd sitting)

Any actual learning design must state: the learned variable, its
**evidence**, its **update equation/objective**, its **schedule**, its
**persistent state**, and its **NEXT CONSUMER**, distinguishing the three
timescales. `LearnedVariable` below is that ruling as a type: a learning
proposal that cannot instantiate it is not admissible. LR1–LR7 are
reference material, not designs (same sitting).

## The stack's named structural targets (Joe, 2026-09-18)

"The development of new institutions, recording new design patterns,
updating links between design patterns, changing how cascades are formed,
or updating other parts of the model." `StructuralMove` types this list.
Per Joe's computational-social-creativity line — **the creation of new
institutions is effectively a repository for learning** — the codomain of
structural learning literally contains `Monitor` and
`InstitutionalStatement` (`Institutions.lean`): what the slow loop learns
is *stored as* institutions, which then bind future work through the
operational-level channels already typed there.

## Learning C — the constitutional constraint

AIF permits Dirichlet-learning the preference parameters. In this stack
that is deliberately split (C591 "discovery, not invention"; the
Institutions verdict's constitutional level): the model may GENERATE
`PreferenceProposal`s from evidence, and this module intentionally defines
**no** `adopt : PreferenceProposal → Preference`. Adoption is the
operator's ruling — the absence of that function is the specification,
not an omission.

## Implementation evidence (why these types and not others)

Surveyed 2026-09-18: parameter learning of A exists and is audited
(`DirichletLearning`, registry `:dirichlet-accumulation`); BMR exists
(`ModelReduction`, registry `:model-reduction`); the habit/E lane has four
partially-rejected Clojure takes (`beta_habit`, `habit_prior`,
`strategic_habit`, `intrinsic_values` — R12/R14 history), which is exactly
the "this way and that way" churn a typed `LearnedVariable` target is
meant to end. Registry `:learning` remains unruled; this module gives the
ruling a typed proposal to accept, amend, or reject.

**The cautionary precedent for `reformCascade` (Joe, 2026-09-18):** the
GFlowNets "slush" line (`futon2:holes/labs/slush-demo/`,
`futon2:holes/E-gflownets-fold.md`) attempted exactly this move — learning
how cascades reform for reuse in a later run — and its slice-2 was a
facade: the GFN was never actually trained (12 gradient steps at batch 1
against a known-working 3000; the evaluated "policy" was its
zero-initialised feature ranking — `futon2:holes/TN-gflownets-fable-review.md`
F1, 2026-07-10). The lesson is the module's charter in miniature: a
learning lane that cannot exhibit its `LearnedVariable` instance —
evidence, update actually applied on its schedule, persistent state that
moved, a consumer that read it — is a facade regardless of its
architecture.

## Lineage

- Institutions as learning's repository: Joe's institutional-computing
  paper, https://metameso.org/~joe/papers/corneli2016institutional.pdf
  (IAD/Ostrom lineage).
- The domain-general frame — learning through design patterns as a move
  beyond AlphaZero's game-locked self-play — is
  `futon2:docs/futonzero-alphazero.md` (2026-06-09, Fable with claude-1, -3, -4;
  includes Fable's honest caveat that v1 was architecture, not the closed
  loop). GFlowNets entered as Fable's suggestion in that early line; the
  specific suggestion has not panned out (above), the frame stands.
-/

namespace DarkTower.AIF

open DarkTower.WarMachine

/-! ## Timescales and the ruled design shape -/

/-- The three AIF timescales: per-tick state inference, slower parameter
learning, slowest structure revision. -/
inductive Timescale
  | inference
  | learning
  | structural
  deriving DecidableEq, Repr

/-- Joe's ruled design shape (2026-09-09) as a type. A learned variable is:
persistent state `Θ`, evidence `Ev`, an update law, a schedule (the ticks
at which it fires — the slow loop is `schedule ⊂` every tick), and the
next consumer's read `consume : Θ → Out` (a learned state nothing reads is
not a learned variable). -/
structure LearnedVariable (Θ Ev Out : Type*) where
  timescale : Timescale
  update : Θ → Ev → Θ
  schedule : ℕ → Prop
  consume : Θ → Out

/-! ## Parameter learning: A (audited carrier) and E (defined here) -/

/-- Likelihood learning as a `LearnedVariable`: persistent state = Dirichlet
concentrations over (outcome, state); evidence = one nonneg trial; update =
the audited `DirichletLearning.accumulate` (Da Costa eq. 21); consumer =
the normalised concentration read (the next trial's A). The schedule is a
parameter: it is a *ruling*, not a law of the maths. -/
def likelihoodLearning (O S : Type*) (schedule : ℕ → Prop) :
    LearnedVariable (DirichletLearning.DirichletParams O S)
      {t : DirichletLearning.Trial O S // DirichletLearning.TrialNonneg t}
      (O → S → ℝ) where
  timescale := .learning
  update := fun a t => DirichletLearning.accumulate a t.1 t.2
  schedule := schedule
  consume := fun a => a.conc

/-- Habit accumulation (the E analogue of eq. 21): fold the tick's policy
posterior into the habit weights. Nonnegativity is preserved by
construction. -/
def Habit.accumulate {P : Type*} (E : Habit P) (post : P → ℝ)
    (h : ∀ p, 0 ≤ post p) : Habit P :=
  ⟨fun p => E.weight p + post p, fun p => add_nonneg (E.nonneg p) (h p)⟩

@[simp] theorem Habit.accumulate_weight {P : Type*} (E : Habit P)
    (post : P → ℝ) (h : ∀ p, 0 ≤ post p) (p : P) :
    (E.accumulate post h).weight p = E.weight p + post p := rfl

/-- Accumulation never weakens a habit: decay/normalisation, if wanted, is
a further modeling decision to be ruled, not an accident of the update. -/
theorem Habit.le_accumulate {P : Type*} (E : Habit P) (post : P → ℝ)
    (h : ∀ p, 0 ≤ post p) (p : P) :
    E.weight p ≤ (E.accumulate post h).weight p :=
  le_add_of_nonneg_right (h p)

/-! ## Learning C: proposals only, adoption is constitutional -/

/-- An evidence-derived preference proposal (C591's extractor output shape:
the proposal plus the evidence it derives from). There is deliberately no
`adopt` function in this module — adoption of preference content is the
operator's ruling (Institutions verdict, constitutional level). -/
structure PreferenceProposal (O Ev : Type*) where
  proposal : Preference O
  evidence : Ev

/-! ## Structural learning: the named targets, typed -/

/-- The codomain of structure-level learning, per Joe's named list
(2026-09-18). `Pat` is the design-pattern type (abstract here; the stack's
pattern library instantiates it). New institutions are learning's
repository: `newMonitor` and `newStatement` land in `Institutions.lean`'s
operational machinery and bind future work. Every move is a *proposal*
whose acceptance is evaluated by Bayesian model reduction
(`ModelReduction.modelReductionDecision`) or by ruling. -/
inductive StructuralMove (S O U M Pat : Type*)
  | newMonitor (mon : Monitor S M)
  | newStatement (stmt : InstitutionalStatement S U)
  | newPattern (p : Pat)
  | linkPatterns (from_ to_ : Pat)
  | reformCascade (precedence : List Pat)

end DarkTower.AIF
