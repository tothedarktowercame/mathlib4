import Mathlib
import DarkTower.MetaCAExample

/-!
# A validation kernel for Baldwin experiments on MetaCA

`MetaCAExample` records the shared update architecture and its dynamic
occupants.  This file adds the smaller contract needed before an evolutionary
run can count as a Baldwin experiment.  It deliberately leaves the rule type,
fitness evaluator, and genetic accessibility relation as parameters: those are
empirical or implementation-specific inputs, not facts that the design layer
should silently invent.

The first obligations captured here are:

* a held locus keeps its inherited rule during rewriting;
* horizontal transfer moves a rule and its held status from the same donor;
* a completed Baldwin claim supplies a high-function accessible path to a
  static endpoint, rather than merely a falling proxy;
* the mutation-only baseline reflects a lifecycle in which half the population
  survives unchanged and only the offspring half is mutated.
-/

namespace DarkTower

namespace BaldwinDesign

/--
The heritable part of the minimal experiment.  `field i` is the rule inherited
at locus `i`; `held i = true` says that the rule is fixed for the whole
evaluation.
-/
structure Genome (ι : Type*) (Rule : Type*) where
  field : ι → Rule
  held : ι → Bool

namespace Genome

variable {ι Rule : Type*}

/-- Make every locus fixed without changing any inherited rule. -/
def holdAll (g : Genome ι Rule) : Genome ι Rule where
  field := g.field
  held := fun _ => true

/-- A genome is static when every inherited rule is held. -/
def IsStatic (g : Genome ι Rule) : Prop :=
  ∀ i, g.held i = true

/-- Holding every locus produces a static genome. -/
theorem holdAll_isStatic (g : Genome ι Rule) : (holdAll g).IsStatic := by
  intro i
  rfl

/-- `holdAll` changes no inherited rule. -/
@[simp]
theorem holdAll_field (g : Genome ι Rule) (i : ι) :
    (holdAll g).field i = g.field i :=
  rfl

/--
One genotype-rewrite step.  The candidate rewrite may inspect the whole
genome, but a held locus ignores it and retains its inherited rule.
-/
def rewriteStep (rewrite : ι → Genome ι Rule → Rule)
    (g : Genome ι Rule) : Genome ι Rule where
  field := fun i => if g.held i then g.field i else rewrite i g
  held := g.held

/-- The held flag itself is invariant under a within-evaluation rewrite. -/
@[simp]
theorem rewriteStep_held (rewrite : ι → Genome ι Rule → Rule)
    (g : Genome ι Rule) (i : ι) :
    (rewriteStep rewrite g).held i = g.held i :=
  rfl

/-- A held locus keeps exactly its inherited rule during a rewrite step. -/
theorem rewriteStep_fixed (rewrite : ι → Genome ι Rule → Rule)
    (g : Genome ι Rule) (i : ι) (hi : g.held i = true) :
    (rewriteStep rewrite g).field i = g.field i := by
  simp [rewriteStep, hi]

/--
Linked horizontal transfer.  At every locus, both the rule and its held status
come from the donor selected at that locus.
-/
def linkedHGT (chooseLeft : ι → Prop) [DecidablePred chooseLeft]
    (left right : Genome ι Rule) : Genome ι Rule where
  field := fun i => if chooseLeft i then left.field i else right.field i
  held := fun i => if chooseLeft i then left.held i else right.held i

/--
The linkage obligation exposed pointwise: the child cannot inherit a rule from
one donor and the corresponding held flag from the other.
-/
theorem linkedHGT_sameDonor (chooseLeft : ι → Prop) [DecidablePred chooseLeft]
    (left right : Genome ι Rule) (i : ι) :
    ((linkedHGT chooseLeft left right).field i = left.field i ∧
        (linkedHGT chooseLeft left right).held i = left.held i) ∨
      ((linkedHGT chooseLeft left right).field i = right.field i ∧
        (linkedHGT chooseLeft left right).held i = right.held i) := by
  by_cases h : chooseLeft i
  · left
    simp [linkedHGT, h]
  · right
    simp [linkedHGT, h]

end Genome

/--
The declarations that turn the generic genome into one proposed experiment.
Performance is raw functional performance, before any plasticity cost.
Accessibility is the actual one-generation genetic transition relation.
-/
structure ExperimentalDesign (ι : Type*) (Rule : Type*) where
  performance : Genome ι Rule → ℝ
  plasticDependence : Genome ι Rule → ℝ
  threshold : ℝ
  accessible : Genome ι Rule → Genome ι Rule → Prop

namespace ExperimentalDesign

variable {ι Rule : Type*}

/-- Raw function clears the experiment's declared threshold. -/
def Successful (d : ExperimentalDesign ι Rule) (g : Genome ι Rule) : Prop :=
  d.threshold ≤ d.performance g

/-- A supplied endpoint certificate, not an inference from a declining cost. -/
structure StaticEndpoint (d : ExperimentalDesign ι Rule) where
  genome : Genome ι Rule
  static : genome.IsStatic
  successful : d.Successful genome

/--
A completed Baldwin claim is a certificate with `n` genetic transitions.

Every intermediate retains raw function, every transition is admitted by the
declared genetic operators, dependence on within-evaluation rewriting never
increases and falls strictly overall, and the final inherited field still
works when every locus is held.
-/
structure BaldwinWitness (d : ExperimentalDesign ι Rule) (n : Nat) where
  path : Fin (n + 1) → Genome ι Rule
  accessibleStep :
    ∀ i : Fin n, d.accessible (path i.castSucc) (path i.succ)
  highFunction :
    ∀ i, d.Successful (path i)
  dependenceStep :
    ∀ i : Fin n,
      d.plasticDependence (path i.succ) ≤
        d.plasticDependence (path i.castSucc)
  strictAssimilation :
    d.plasticDependence (path (Fin.last n)) <
      d.plasticDependence (path 0)
  finalStatic :
    (path (Fin.last n)).IsStatic
  inheritedFunction :
    d.Successful ((path (Fin.last n)).holdAll)

/-- Every completed Baldwin witness contains a certified static endpoint. -/
def BaldwinWitness.endpoint {d : ExperimentalDesign ι Rule} {n : Nat}
    (w : d.BaldwinWitness n) : d.StaticEndpoint where
  genome := (w.path (Fin.last n)).holdAll
  static := Genome.holdAll_isStatic _
  successful := w.inheritedFunction

end ExperimentalDesign

/--
A MetaCA experiment chooses one of the already formalized dynamic occupants
and supplies the experimental declarations above.  This is the explicit seam
where a later executable evaluator can instantiate the generic design.
-/
structure MetaCAExperiment (ι : Type*) (Rule : Type*)
    extends ExperimentalDesign ι Rule where
  occupant : MetaCAExample.DynamicOccupant


/-! ## Tape alignment (I1)

The most repeated implementation failure on this substrate, three times, was a
damage measurement in which the two branches of a perturbation fork consumed
different numbers of random draws.  A gate reading the phenotype fires at
different loci in the two branches, so if a closed gate skips its draw the tapes
desynchronise and the divergence that follows is an artefact rather than a causal
effect.  Once it produced an order-of-magnitude spurious result that survived
review.

The formal content is that the *draw schedule* must not depend on the evaluation
state.  A `LooseEvaluator` is one that is permitted to consult the state; tape
alignment is the proposition that it does not.
-/

/-- An evaluator whose per-locus draw count may depend on the branch state. -/
structure LooseEvaluator (ι State : Type*) where
  draws : Nat → ι → State → Nat

namespace LooseEvaluator

variable {ι State : Type*}

/-- The draw schedule ignores the state: both branches consume the same tape. -/
def TapeAligned (e : LooseEvaluator ι State) : Prop :=
  ∀ t i s s', e.draws t i s = e.draws t i s'

/-- Under alignment, two branches in any states agree locus by locus. -/
theorem draws_eq_of_aligned {e : LooseEvaluator ι State}
    (h : e.TapeAligned) (t : Nat) (i : ι) (s s' : State) :
    e.draws t i s = e.draws t i s' := h t i s s'

/-- Under alignment the totals over any finite locus set agree, which is the
statement the fork actually needs. -/
theorem sum_draws_eq_of_aligned [DecidableEq ι] {e : LooseEvaluator ι State}
    (h : e.TapeAligned) (t : Nat) (S : Finset ι) (s s' : State) :
    (S.sum fun i => e.draws t i s) = S.sum fun i => e.draws t i s' :=
  Finset.sum_congr rfl fun i _ => h t i s s'

/-- An evaluator that never consults the state is aligned by construction.  This
is the discipline the fixed implementation adopts: draw unconditionally, then
decide how to use the draw. -/
theorem tapeAligned_of_stateIndependent (f : Nat → ι → Nat) :
    (LooseEvaluator.mk fun t i _ => f t i : LooseEvaluator ι State).TapeAligned :=
  fun _ _ _ _ => rfl

end LooseEvaluator

/-! ## Non-degeneracy of the selected axis (I6)

Twice an experiment was run in which the quantity under selection could not vary
in a way the score could see: once because the band score was zero for the entire
population from the first generation, so ranking was driven wholly by the cost
term and arms at different costs produced byte-identical trajectories; once
because the band score is exactly zero for every gain below one, making gradual
retreat impossible at any cost below about five.

A completed Baldwin claim requires plastic dependence to *fall strictly*.  So if
that quantity is constant across genomes, no witness of any length exists.  This
is the pre-flight the runs lacked.
-/

namespace ExperimentalDesign

variable {ι Rule : Type*}

/-- Plastic dependence takes the same value at every genome. -/
def DependenceDegenerate (d : ExperimentalDesign ι Rule) : Prop :=
  ∀ g g' : Genome ι Rule, d.plasticDependence g = d.plasticDependence g'

/-- A degenerate dependence axis admits no Baldwin witness, of any length.
Checking this before running is cheaper than discovering it afterwards. -/
theorem no_witness_of_degenerate {d : ExperimentalDesign ι Rule} {n : Nat}
    (hdeg : d.DependenceDegenerate) : IsEmpty (d.BaldwinWitness n) := by
  refine ⟨fun w => ?_⟩
  have hlt := w.strictAssimilation
  rw [hdeg (w.path (Fin.last n)) (w.path 0)] at hlt
  exact lt_irrefl _ hlt

/-- Contrapositive, as the pre-flight is actually used: exhibiting a witness
certifies that the axis was not degenerate. -/
theorem not_degenerate_of_witness {d : ExperimentalDesign ι Rule} {n : Nat}
    (w : d.BaldwinWitness n) : ¬ d.DependenceDegenerate :=
  fun hdeg => (no_witness_of_degenerate (n := n) hdeg).false w

end ExperimentalDesign


/-! ## Layering fidelity (I2)

Every extension of the measured substrate must reduce to the published
measurement when its new machinery sits in the neutral position.  This caught a
real defect: injecting a heritable genotype left the random tape un-advanced by
the draws the original construction made, and the reference value moved from
`12.3875` to `11.0083` while still reproducing byte-for-byte.  Determinism is not
fidelity.

The obligation is carried as a field, so an extension cannot be stated without
discharging it.
-/

/-- An extension of a reference measurement, carrying its own agreement proof. -/
structure Extension (ι : Type*) (Rule : Type*) where
  design : ExperimentalDesign ι Rule
  Neutral : Genome ι Rule → Prop
  reference : Genome ι Rule → ℝ
  agrees : ∀ g, Neutral g → design.performance g = reference g

namespace Extension

variable {ι Rule : Type*}

/-- On neutral genomes an extension is indistinguishable from its reference. -/
theorem performance_eq_reference (e : Extension ι Rule) {g : Genome ι Rule}
    (hg : e.Neutral g) : e.design.performance g = e.reference g := e.agrees g hg

/-- Extensions agreeing with the same reference agree with each other where both
are neutral, so a chain of extensions cannot drift. -/
theorem agree_of_shared_reference (e₁ e₂ : Extension ι Rule)
    (href : e₁.reference = e₂.reference) {g : Genome ι Rule}
    (h₁ : e₁.Neutral g) (h₂ : e₂.Neutral g) :
    e₁.design.performance g = e₂.design.performance g := by
  rw [e₁.agrees g h₁, e₂.agrees g h₂, href]

end Extension

/-! ## Mutation reachability (I4)

A gene whose values the operator cannot reach looks present and is not.  If the
assimilated endpoint requires a value outside the reachable set, no witness can
exist however long the run.
-/

/-- Reflexive transitive closure of a one-step genetic operator. -/
inductive Reaches {α : Type*} (step : α → α → Prop) : α → α → Prop
  | refl (a : α) : Reaches step a a
  | tail {a b c : α} : Reaches step a b → step b c → Reaches step a c

namespace Reaches

variable {α : Type*} {step : α → α → Prop}

theorem single {a b : α} (h : step a b) : Reaches step a b :=
  .tail (.refl a) h

theorem trans {a b c : α} (hab : Reaches step a b) : Reaches step b c → Reaches step a c := by
  intro hbc
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact .tail ih hstep

end Reaches

/-- Every value of `gene` in `domain` is attainable from `start`. -/
def GeneReachable {ι Rule V : Type*} (step : Genome ι Rule → Genome ι Rule → Prop)
    (gene : Genome ι Rule → V) (domain : Set V) (start : Genome ι Rule) : Prop :=
  ∀ v ∈ domain, ∃ g, Reaches step start g ∧ gene g = v

/-- If the operator cannot reach the value the endpoint needs, there is no path
to it, so no run length rescues the experiment. -/
theorem no_path_of_unreachable {ι Rule V : Type*}
    {step : Genome ι Rule → Genome ι Rule → Prop} {gene : Genome ι Rule → V}
    {start target : Genome ι Rule}
    (hne : ∀ g, Reaches step start g → gene g ≠ gene target) :
    ¬ Reaches step start target :=
  fun h => hne target h rfl

/-! ## Treatments must separate (I9)

Four cost arms once produced byte-identical trajectories.  That is not a robust
result; it says the treatment never reached selection.  The mechanism is exact:
selection sees only the ORDER of scores, so a term that shifts every genome by
the same amount is invisible.  When the population had converged in gain, the
cost `c * gamma` was such a constant.
-/

namespace ExperimentalDesign

variable {ι Rule : Type*}

/-- Two designs induce the same selection order. -/
def RankingEquivalent (d₁ d₂ : ExperimentalDesign ι Rule) : Prop :=
  ∀ g g' : Genome ι Rule,
    d₁.performance g ≤ d₁.performance g' ↔ d₂.performance g ≤ d₂.performance g'

/-- Subtracting a constant from every genome preserves the selection order, so a
cost term that is uniform across the population cannot act. -/
theorem rankingEquivalent_sub_const (d : ExperimentalDesign ι Rule) (k : ℝ) :
    d.RankingEquivalent { d with performance := fun g => d.performance g - k } := by
  intro g g'
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Ranking equivalence is reflexive; identical arms are expected to coincide and
their coincidence is therefore not evidence of anything. -/
theorem rankingEquivalent_refl (d : ExperimentalDesign ι Rule) :
    d.RankingEquivalent d := fun _ _ => Iff.rfl

end ExperimentalDesign

/-! ## The mutation-only baseline for the current elitist lifecycle -/

/--
Expected held fraction among offspring after independent symmetric flips with
probability `μ`, given parental held fraction `q`.
-/
def symmetricFlipOffspring (μ q : ℝ) : ℝ :=
  q * (1 - μ) + (1 - q) * μ

/--
One mutation-only population step when half the population survives unchanged
and the other half consists of mutated offspring.
-/
noncomputable def elitistHalfStep (μ q : ℝ) : ℝ :=
  (q + symmetricFlipOffspring μ q) / 2

/-- Only mutating the offspring half changes the linear rate from `1 - 2μ` to `1 - μ`. -/
theorem elitistHalfStep_eq (μ q : ℝ) :
    elitistHalfStep μ q = (1 - μ) * q + μ / 2 := by
  simp only [elitistHalfStep, symmetricFlipOffspring]
  ring

/-- Mutation-only expectation starting from an entirely unheld population. -/
noncomputable def mutationOnlyHeld (μ : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => elitistHalfStep μ (mutationOnlyHeld μ n)

/-- Closed form for the lifecycle-aware mutation-only baseline. -/
theorem mutationOnlyHeld_closedForm (μ : ℝ) (n : Nat) :
    mutationOnlyHeld μ n = (1 - (1 - μ) ^ n) / 2 := by
  induction n with
  | zero =>
      simp [mutationOnlyHeld]
  | succ n ih =>
      rw [mutationOnlyHeld, elitistHalfStep_eq, ih, pow_succ]
      ring

end BaldwinDesign

end DarkTower
