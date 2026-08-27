/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# War Machine commitment temperature

This standalone outline states the temperature-out face of R14.  The required
channel is behavioural: for some fixed ranking, changing commitment
temperature changes the selected action.  Merely copying the temperature into
a record is explicitly weaker and is refused below.

The enacting path modelled here is the live
`:selection-boundary :strategic-recommendation` path.  Its selected action is
the first controller entry (`policy.clj:238`) and is later installed from
`strategic-action` (`war_machine.clj:4476,4527`); temperature changes reported
scores but not that action.  The default argmax branch has the same invariance.
The habit-prior branch has nonzero capacity because its score is
`-G + τL`; three records under that mode exist in `futon2/data/wm-trace/`, but
whether they are live decisions or shadow calculations is not established.

`G` is an opaque ordered controller score.  Nothing here defines or validates
`G(π)`.  The selector is deterministic; sampling from `P(π)`, one proposed
repair, is not modelled.  This file states no emitter, Clojure contract,
mutation test, or running-system repair.

The `Temperature` value `t : Nat` encodes the positive integer temperature
`t + 1`.  Thus all score comparisons use integer arithmetic and never divide.
This continues `GainChain.gainAdvances`: repairing the incoming gain cannot
alter an action while the final temperature-to-action edge remains constant.

## Fixture polarities

* accepting — `habit_prior_governs`
* refusing-broken — `live_selector_does_not_govern`
* refusing-plausible-fix — `record_sensitivity_is_not_governance` (making the
  emitted record move with τ looks like restoring governance and does not)

## Vocabulary

This module defines its own vocabulary (`Selector`, `governs`,
`factorsThroughDiscard`) rather than adapting to a `GainChain` family, because
its subject is a selector's dependence on a parameter rather than the presence,
domain, or durability of a fold occurrence.  Its contract entry is family 8,
which has no APM source.
-/

namespace DarkTower.WarMachine.CommitmentTemperature

structure Action where
  id : String
  deriving DecidableEq, Repr

structure Entry where
  action : Action
  g : Int
  l : Int
  deriving DecidableEq, Repr

/-- `t` represents the strictly positive integer temperature `t + 1`. -/
abbrev Temperature := Nat

abbrev Selector := Temperature → List Entry → Option Action

/-- R14's uncompromised requirement.  For a deterministic selector this is the
finite behavioural form of positive information from temperature to the
selected action: the channel is not constant.

Stated precisely, since the informal reading is easy to overclaim:
non-constancy is equivalent to the *existence* of a temperature distribution
under which the mutual information is positive, not to its being positive under
every input law.  A constant channel carries zero bits under every law, which is
the direction this file uses. -/
def governs (s : Selector) : Prop :=
  ∃ entries τ₁ τ₂, s τ₁ entries ≠ s τ₂ entries

/-- A selection record can mention temperature even when its action is
temperature-independent.  `reportedScores` stands for the live record's
`:controller-ranking` scores, which are literally `-G/τ`, and for
`:softmax-weights`: quantities computed from τ, written down, and then not
used to choose. -/
structure SelectionRecord where
  temperature : Temperature
  reportedScores : List Int
  action : Option Action
  deriving DecidableEq, Repr

abbrev RecordEmitter := Temperature → List Entry → SelectionRecord

/-- The weakening to refuse: temperature changes the record, with no
requirement that it change the selected action. -/
def governsTheRecord (r : RecordEmitter) : Prop :=
  ∃ entries τ₁ τ₂, r τ₁ entries ≠ r τ₂ entries

/-- The positive integer represented by a temperature code. -/
def temperatureValue (τ : Temperature) : Int := Int.ofNat (τ + 1)

/-- The habit-prior comparison after multiplying the divided score by the
positive temperature: `-G + τL`. -/
def commitmentScore (τ : Temperature) (entry : Entry) : Int :=
  -entry.g + temperatureValue τ * entry.l

/-- Stable left-biased argmax for an integer score. -/
def argmaxBy (score : Entry → Int) : List Entry → Option Entry
  | [] => none
  | entry :: entries =>
      some (entries.foldl
        (fun best candidate => if score best < score candidate then candidate else best)
        entry)

/-- The live strategic-recommendation boundary: choose the first entry. -/
def modeOnly : Selector :=
  fun _ entries => entries.head?.map Entry.action

/-- The default single-term argmax.  It deliberately goes through the
temperature-bearing score formula after setting every habit prior to zero, so
its invariance is the algebraic fact `τ * 0 = 0`. -/
def argmaxScore : Selector := fun τ entries =>
  (argmaxBy (fun entry => commitmentScore τ { entry with l := 0 }) entries).map
    Entry.action

/-- The only modelled branch in which temperature can change the winner. -/
def habitPrior : Selector := fun τ entries =>
  (argmaxBy (commitmentScore τ) entries).map Entry.action

def cautiousAction : Action := ⟨"cautious"⟩
def habitualAction : Action := ⟨"habitual"⟩

/-- At encoded temperature `0` (actual temperature 1), cautious scores `0`
and habitual scores `-1`; at encoded temperature `2` (actual temperature 3),
habitual scores `1` and wins. -/
def switchingEntries : List Entry :=
  [ { action := cautiousAction, g := 0, l := 0 },
    { action := habitualAction, g := 2, l := 1 } ]

/-- The live trace record computes and reports the temperature-scaled scores,
even though `modeOnly` does not let them govern the action. -/
def liveRecord : RecordEmitter := fun τ entries =>
  { temperature := τ
    reportedScores := entries.map (commitmentScore τ)
    action := modeOnly τ entries }

/-- A selector is constant in temperature for every fixed ranking. -/
def temperatureInvariant (s : Selector) : Prop :=
  ∀ τ₁ τ₂ entries, s τ₁ entries = s τ₂ entries

theorem mode_only_ignores_temperature :
    ∀ τ₁ τ₂ entries, modeOnly τ₁ entries = modeOnly τ₂ entries := by
  intro τ₁ τ₂ entries
  rfl

/-- The headline finding: the live selector does not satisfy R14. -/
theorem live_selector_does_not_govern : ¬ governs modeOnly := by
  rintro ⟨entries, τ₁, τ₂, h⟩
  exact h (mode_only_ignores_temperature τ₁ τ₂ entries)

theorem commitmentScore_zero_prior (τ : Temperature) (entry : Entry) :
    commitmentScore τ { entry with l := 0 } = -entry.g := by
  simp [commitmentScore]

/-- With one score term and zero habit prior, multiplication by temperature
vanishes before argmax; this is not merely an unused selector argument. -/
theorem argmax_score_temperature_invariant : temperatureInvariant argmaxScore := by
  intro τ₁ τ₂ entries
  simp only [argmaxScore, commitmentScore_zero_prior]

theorem single_term_argmax_annihilates_temperature : ¬ governs argmaxScore := by
  rintro ⟨entries, τ₁, τ₂, h⟩
  exact h (argmax_score_temperature_invariant τ₁ τ₂ entries)

/-- Deterministic data processing at the R8/R14 seam: if the final selector is
temperature-invariant, changing any two gains (and hence their effective
temperatures) changes no selected action. -/
theorem repairing_r8_changes_no_action
    (s : Selector) (hs : temperatureInvariant s)
    (effectiveTemperature : Nat → Temperature)
    (g₁ g₂ : Nat) (entries : List Entry) :
    s (effectiveTemperature g₁) entries =
      s (effectiveTemperature g₂) entries :=
  hs _ _ _

/-- The scheduling result applied to the live selector rather than to an
arbitrary invariant one.  No repair to the incoming gain — R8's slices 4 and 5
included — can move a selected action on this path. -/
theorem live_gain_repair_changes_no_action
    (effectiveTemperature : Nat → Temperature) (g₁ g₂ : Nat) (entries : List Entry) :
    modeOnly (effectiveTemperature g₁) entries =
      modeOnly (effectiveTemperature g₂) entries :=
  repairing_r8_changes_no_action modeOnly
    (fun τ₁ τ₂ es => mode_only_ignores_temperature τ₁ τ₂ es)
    effectiveTemperature g₁ g₂ entries

/-- The same for the default argmax branch, where the invariance is algebraic
rather than syntactic. -/
theorem default_branch_gain_repair_changes_no_action
    (effectiveTemperature : Nat → Temperature) (g₁ g₂ : Nat) (entries : List Entry) :
    argmaxScore (effectiveTemperature g₁) entries =
      argmaxScore (effectiveTemperature g₂) entries :=
  repairing_r8_changes_no_action argmaxScore argmax_score_temperature_invariant
    effectiveTemperature g₁ g₂ entries

/-- The reading is perfect and the action channel is severed: the live record
is temperature-sensitive while the live selector fails R14.  The witness is a
non-empty ranking, so the sensitivity is in the scores rather than in the bare
presence of a temperature field. -/
theorem record_sensitivity_is_not_governance :
    governsTheRecord liveRecord ∧ ¬ governs modeOnly := by
  constructor
  · refine ⟨switchingEntries, 0, 2, ?_⟩
    decide
  · exact live_selector_does_not_govern

/-- The finding in one statement, on one fixed ranking: the reported scores
move with temperature and the selected action does not.  This is what
"computed, recorded, and then discarded at the final step" means formally. -/
theorem scores_move_action_does_not :
    (liveRecord 0 switchingEntries).reportedScores ≠
      (liveRecord 2 switchingEntries).reportedScores ∧
    (liveRecord 0 switchingEntries).action =
      (liveRecord 2 switchingEntries).action := by
  constructor <;> decide

/-- Non-vacuity: the habit-prior branch has a ranking whose winner genuinely
changes with temperature. -/
theorem habit_prior_governs : governs habitPrior := by
  refine ⟨switchingEntries, 0, 2, ?_⟩
  decide

/-!
## The Markov-category form of the requirement

In a Markov category every object carries a commutative comonoid — copy `Δ` and
discard `ε` — and a morphism is independent of an input exactly when it
**factors through that input's discard**.  Stated that way, R14's requirement
needs no probability measure on τ at all, which is what the `governs` docstring
above has to caveat.

This section states the finite, dependency-free case.  `Mathlib`'s
`Probability/Kernel/Category/Stoch.lean` carries the measure-theoretic version
(`Δ[X]`, `ε[X]`, `Deterministic`); it is not imported here because this file is
deliberately standalone.  The trigger for reaching for it is repair option (a),
sampling `P(π)`, which is a genuine stochastic morphism.  The determinism
distinction is the one that matters there: the softmax is a stochastic morphism
and `argmax` is a deterministic one that forgets it.
-/

/-- A selector **factors through the discard of the temperature** when it equals
a morphism that never receives τ.  This is `ε_τ` in the finite case, with the
witness `c` exhibited. -/
def factorsThroughDiscard (s : Selector) : Prop :=
  ∃ c : List Entry → Option Action, ∀ τ entries, s τ entries = c entries

/-- The categorical form is not a weaker gloss on the operational one: factoring
through discard and temperature-invariance are the same condition. -/
theorem factorsThroughDiscard_iff_temperatureInvariant (s : Selector) :
    factorsThroughDiscard s ↔ temperatureInvariant s := by
  constructor
  · rintro ⟨c, hc⟩ τ₁ τ₂ entries
    rw [hc, hc]
  · intro h
    exact ⟨fun entries => s 0 entries, fun τ entries => h τ 0 entries⟩

/-- **R14's requirement, restated:** the temperature governs exactly when the
selector does *not* factor through the discard of τ. -/
theorem not_governs_iff_factorsThroughDiscard (s : Selector) :
    ¬ governs s ↔ factorsThroughDiscard s := by
  rw [factorsThroughDiscard_iff_temperatureInvariant]
  constructor
  · intro h τ₁ τ₂ entries
    exact Classical.byContradiction fun hne => h ⟨entries, τ₁, τ₂, hne⟩
  · rintro h ⟨entries, τ₁, τ₂, hne⟩
    exact hne (h τ₁ τ₂ entries)

/-- **Data processing as the counit law.**  A discard absorbs everything
upstream of it — `f ; ε = ε` — so if the selector factors through the discard of
τ, the whole chain `g → τ_eff → action` factors through the discard of `g`.
This is `repairing_r8_changes_no_action` obtained structurally, by composition,
rather than by instantiating an invariance hypothesis. -/
theorem discard_absorbs_upstream
    (s : Selector) (h : factorsThroughDiscard s)
    (effectiveTemperature : Nat → Temperature) :
    ∃ c : List Entry → Option Action,
      ∀ g entries, s (effectiveTemperature g) entries = c entries := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun g entries => hc _ entries⟩

/-- The live selector, in the categorical vocabulary. -/
theorem live_selector_factors_through_discard : factorsThroughDiscard modeOnly :=
  (factorsThroughDiscard_iff_temperatureInvariant modeOnly).mpr
    (fun τ₁ τ₂ entries => mode_only_ignores_temperature τ₁ τ₂ entries)

#print axioms factorsThroughDiscard_iff_temperatureInvariant
#print axioms not_governs_iff_factorsThroughDiscard
#print axioms discard_absorbs_upstream
#print axioms live_selector_factors_through_discard
#print axioms mode_only_ignores_temperature
#print axioms live_selector_does_not_govern
#print axioms single_term_argmax_annihilates_temperature
#print axioms repairing_r8_changes_no_action
#print axioms live_gain_repair_changes_no_action
#print axioms default_branch_gain_repair_changes_no_action
#print axioms record_sensitivity_is_not_governance
#print axioms scores_move_action_does_not
#print axioms habit_prior_governs

end DarkTower.WarMachine.CommitmentTemperature
