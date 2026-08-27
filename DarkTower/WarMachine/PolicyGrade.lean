/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# When a run earns the name policy grade

This module formalises two naming conditions for `G(π)`.  S-G2 refuses an
action sequence that only repeats one action.  S-G4 requires the score to
change under some alternative wiring of the same policy components.

The model contains no probability, no preferences `C`, and no expected free
energy.  S-G1 is also out of scope: it concerns the provenance of a predicted
distribution, whereas this module concerns naming discipline over a finished
run.

Two limitations, recorded rather than repaired.  `Wiring` does not itself
witness that its values are re-orderings of the *same* components; that a family
really is one policy under two wirings is an obligation on whoever builds it,
discharged here by the two orders having been measured on one collection.  And a
score that no re-wiring moves may belong to a robust policy rather than a
degenerate one.  S-G4 refuses the *name* in both cases, because the measurement
supplies no evidence that the wiring produced the number — a condition on the
measurement, not a verdict on the policy.

## Fixture polarities

* accepting — `pattern_driven_g4_snatcher_earns_policy_grade`
* refusing-broken — `grim_trigger_sharer_refused_by_sg2`
* refusing-plausible-fix — `grim_trigger_snatcher_passes_sg2_fails_sg4` (making
  the actions differ is the obvious way to satisfy S-G2 and is not enough)

## Vocabulary

This module defines its own vocabulary deliberately: it is naming discipline
over a finished run, not a requirement about a fold occurrence, so it adapts to
no `GainChain` family and imports nothing.
-/

namespace DarkTower.WarMachine.PolicyGrade

/-- The observations relevant to policy-grade naming after a finished run. -/
structure Run (Action Score : Type) where
  actions : List Action
  score : Score
  deriving Repr

/-- S-G2's refused case: every action observed in the run is identical. -/
def sustainedSingleAction {Action Score : Type}
    (run : Run Action Score) : Prop :=
  ∀ a ∈ run.actions, ∀ b ∈ run.actions, a = b

/-- S-G4: at least one change of wiring changes the resulting score. -/
def wiringSensitive {Wiring Score : Type} [DecidableEq Score]
    (scoreUnder : Wiring → Score) : Prop :=
  ∃ wiring₁ wiring₂, scoreUnder wiring₁ ≠ scoreUnder wiring₂

/-- **S-G4 forces a policy space with more than one point.**  A score cannot be
sensitive to a choice of wiring that does not exist. -/
theorem wiringSensitive_needs_two_wirings {Wiring Score : Type} [DecidableEq Score]
    (scoreUnder : Wiring → Score) (h : wiringSensitive scoreUnder) :
    ∃ wiring₁ wiring₂ : Wiring, wiring₁ ≠ wiring₂ := by
  have ⟨wiring₁, wiring₂, hne⟩ := h
  exact ⟨wiring₁, wiring₂, fun hEq => hne (congrArg scoreUnder hEq)⟩

/-- Consequently a singleton-indexed family fails S-G4 whatever it scores.  This
is what carries the hardcoded cases below: the modelling commitment is that a
hardcoded policy admits exactly one wiring, and the refusal is then a theorem
rather than a second commitment. -/
theorem singleton_wiring_fails_sg4 {Score : Type} [DecidableEq Score]
    (scoreUnder : Unit → Score) : ¬ wiringSensitive scoreUnder := by
  intro h
  have ⟨wiring₁, wiring₂, hne⟩ := wiringSensitive_needs_two_wirings scoreUnder h
  cases wiring₁; cases wiring₂; exact hne rfl

/-- A finished run earns policy grade only when it passes both S-G2 and S-G4. -/
def earnsPolicyGrade {Action Wiring Score : Type} [DecidableEq Score]
    (run : Run Action Score) (observedWiring : Wiring)
    (scoreUnder : Wiring → Score) : Prop :=
  scoreUnder observedWiring = run.score ∧
  ¬ sustainedSingleAction run ∧ wiringSensitive scoreUnder

inductive Action where
  | offer
  | abstain
  | denounce
  | stop
  deriving DecidableEq, Repr

/-- Measured G1 run against a sharer. -/
def grimTriggerSharer : Run Action Int :=
  ⟨[.offer, .offer, .offer, .offer, .offer], 5⟩

/-- The measured score under grim trigger's sole, hardcoded wiring. -/
def hardcodedSharerScore : Unit → Int := fun _ => 5

/-- S-G2 refuses the measured `+5`: the run repeats `offer` throughout. -/
theorem grim_trigger_sharer_refused_by_sg2 :
    grimTriggerSharer.score = 5 ∧
    sustainedSingleAction grimTriggerSharer ∧
    ¬ earnsPolicyGrade grimTriggerSharer () hardcodedSharerScore := by
  constructor
  · rfl
  constructor
  · simp [sustainedSingleAction, grimTriggerSharer]
  · simp [earnsPolicyGrade, sustainedSingleAction, grimTriggerSharer]

/-- Measured G1 run against a snatcher. -/
def grimTriggerSnatcher : Run Action Int :=
  ⟨[.offer, .abstain, .abstain, .abstain, .abstain], -1⟩

/-- A hardcoded policy has exactly one wiring, so this family is constant. -/
def hardcodedSnatcherScore : Unit → Int := fun _ => -1

/-- S-G2 alone is insufficient: this run contains two actions, but its
hardcoded policy admits no score-changing rewiring. -/
theorem grim_trigger_snatcher_passes_sg2_fails_sg4 :
    grimTriggerSnatcher.score = -1 ∧
    ¬ sustainedSingleAction grimTriggerSnatcher ∧
    ¬ wiringSensitive hardcodedSnatcherScore ∧
    ¬ earnsPolicyGrade grimTriggerSnatcher () hardcodedSnatcherScore := by
  constructor
  · rfl
  constructor
  · intro h
    have same := h .offer (by simp [grimTriggerSnatcher])
      .abstain (by simp [grimTriggerSnatcher])
    cases same
  constructor
  · exact singleton_wiring_fails_sg4 hardcodedSnatcherScore
  · intro h
    exact singleton_wiring_fails_sg4 hardcodedSnatcherScore h.2.2

/-- The two measured precedence orders of the same twelve patterns. -/
inductive PatternWiring where
  | observed
  | onePromoted
  deriving DecidableEq, Repr

/-- Measured G4 run of the pattern-driven policy against a snatcher. -/
def patternDrivenSnatcher : Run Action Int :=
  ⟨[.offer, .denounce, .offer, .denounce, .offer], 3⟩

/-- Scores measured under the observed order and the one-pattern promotion. -/
def patternScoreUnder : PatternWiring → Int
  | .observed => 3
  | .onePromoted => -5

/-- Non-vacuity: two actions occur and promoting one pattern moves `+3` to
`-5`, so the finished run earns the policy-grade name. -/
theorem pattern_driven_g4_snatcher_earns_policy_grade :
    patternDrivenSnatcher.score = 3 ∧
    patternScoreUnder .onePromoted = -5 ∧
    earnsPolicyGrade patternDrivenSnatcher .observed patternScoreUnder := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro h
    have same := h .offer (by simp [patternDrivenSnatcher])
      .denounce (by simp [patternDrivenSnatcher])
    cases same
  · exact ⟨.observed, .onePromoted, by decide⟩

#print axioms wiringSensitive_needs_two_wirings
#print axioms singleton_wiring_fails_sg4
#print axioms grim_trigger_sharer_refused_by_sg2
#print axioms grim_trigger_snatcher_passes_sg2_fails_sg4
#print axioms pattern_driven_g4_snatcher_earns_policy_grade

end DarkTower.WarMachine.PolicyGrade
