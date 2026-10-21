import DarkTower.WarMachine.R15FocusDistance

/-!
# R15: a distance to the focus estimated from predicted outcomes

In plain terms: a target is near the focus when working on it changes what we
expect to see about the focus. A repair that makes the focused work
finishable changes that expectation completely; unrelated work leaves it as
it was.

`R15FocusDistance` takes the distance as given. This module says how to
compute it from predictions, and proves the properties the class reading
needs without assuming any data exists. Two predicted distributions over
observations about the focus are compared: one for a round that works on the
target, one for a round that does not. Their total variation is the target's
influence on the focus, between 0 and 1. The distance is one minus the
influence.

Total variation is used rather than the KL divergence because it is bounded
and stays in `ℚ`, which keeps the class reading decidable. The two orderings
agree where it matters here: by Pinsker's inequality (Cover and Thomas,
*Elements of Information Theory*, 2nd ed., Lemma 11.6.1) total variation is
bounded by the square root of half the KL divergence, so a target with zero
KL influence has zero total-variation influence, and conversely total
variation is zero only for identical distributions.

What this does not settle: where the two predictions come from. The intended
source is the M40 valid-time history, comparing rounds that touched the target
with rounds that did not; until those records exist the estimator returns
`none`, and `unknown_distance_unscored` leaves the target unscored. That is a
question about data for the runtime. The model, and the theorems below, do
not depend on it.
-/

namespace DarkTower.WarMachine.R15FocusInfluence

open DarkTower.WarMachine.CTauClassPreference
open DarkTower.WarMachine.R15StrategicTarget
open DarkTower.WarMachine.R15FocusDistance

variable {Obs : Type} [Fintype Obs]

/-- A predicted distribution over observations about the focus. -/
abbrev Prediction (Obs : Type) := Obs → ℚ

def IsProbability (p : Prediction Obs) : Prop :=
  (∀ o, 0 ≤ p o) ∧ ∑ o, p o = 1

/-- Total variation between two predictions. -/
def totalVariation (p q : Prediction Obs) : ℚ :=
  (∑ o, |p o - q o|) / 2

theorem totalVariation_nonneg (p q : Prediction Obs) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  have : 0 ≤ ∑ o, |p o - q o| := Finset.sum_nonneg fun o _ => abs_nonneg _
  linarith

theorem totalVariation_le_one (p q : Prediction Obs)
    (hp : IsProbability p) (hq : IsProbability q) : totalVariation p q ≤ 1 := by
  unfold totalVariation
  have bound : ∑ o, |p o - q o| ≤ ∑ o, (p o + q o) :=
    Finset.sum_le_sum fun o _ => by
      rw [abs_sub_le_iff]
      have := hp.1 o
      have := hq.1 o
      constructor <;> linarith
  rw [Finset.sum_add_distrib, hp.2, hq.2] at bound
  linarith

theorem totalVariation_self (p : Prediction Obs) : totalVariation p p = 0 := by
  simp [totalVariation]

/-- For each focus and target, the predicted observations about the focus in a
round that works on the target and in one that does not. `none` means no such
pair has been recorded. -/
abbrev InfluenceRecords (Obs : Type) :=
  Target → Target → Option (Prediction Obs × Prediction Obs)

/-- The influence of the target on the focus. -/
def influence (records : InfluenceRecords Obs) (focus target : Target) : Option ℚ :=
  (records focus target).map fun pair => totalVariation pair.1 pair.2

/-- The estimated distance: one minus the influence. -/
def estimatedDistance (records : InfluenceRecords Obs) : TargetDistance :=
  fun focus target => (influence records focus target).map fun i => 1 - i

/-- Recorded predictions that are probability distributions give a distance
between 0 and 1. -/
theorem estimatedDistance_mem_unit (records : InfluenceRecords Obs)
    (focus target : Target) (w wo : Prediction Obs)
    (recorded : records focus target = some (w, wo))
    (hw : IsProbability w) (hwo : IsProbability wo) :
    ∃ d, estimatedDistance records focus target = some d ∧ 0 ≤ d ∧ d ≤ 1 := by
  refine ⟨1 - totalVariation w wo, ?_, ?_, ?_⟩
  · simp [estimatedDistance, influence, recorded]
  · linarith [totalVariation_le_one w wo hw hwo]
  · linarith [totalVariation_nonneg w wo]

/-- Work that changes nothing about the focus is at distance 1, so for any
radius below 1 it is scored `unrelated`. -/
theorem no_influence_is_unrelated (radius : ℚ) (lt : radius < 1)
    (records : InfluenceRecords Obs) (focus target : Target) (ne : focus ≠ target)
    (p : Prediction Obs) (recorded : records focus target = some (p, p)) :
    outcomeClass focus (relationOfDistance radius (estimatedDistance records))
      (some target) = some .unrelated := by
  have far : ¬ (1 : ℚ) ≤ radius := not_le.mpr lt
  simp [outcomeClass, relationOfDistance, estimatedDistance, influence, recorded, ne,
    totalVariation_self, far, scorerClass]

/-- Work that fully changes what is expected about the focus is at distance 0,
so for any nonnegative radius it is scored `related`. -/
theorem full_influence_is_related (radius : ℚ) (nonneg : 0 ≤ radius)
    (records : InfluenceRecords Obs) (focus target : Target) (ne : focus ≠ target)
    (w wo : Prediction Obs) (recorded : records focus target = some (w, wo))
    (full : totalVariation w wo = 1) :
    outcomeClass focus (relationOfDistance radius (estimatedDistance records))
      (some target) = some .related := by
  simp [outcomeClass, relationOfDistance, estimatedDistance, influence, recorded, ne,
    full, nonneg, scorerClass]

/-- No recorded predictions, no class: the target stays unscored. -/
theorem unrecorded_is_unscored (radius : ℚ) (records : InfluenceRecords Obs)
    (focus target : Target) (ne : focus ≠ target) (none : records focus target = none) :
    outcomeClass focus (relationOfDistance radius (estimatedDistance records))
      (some target) = Option.none :=
  unknown_distance_unscored radius _ focus target ne (by
    simp [estimatedDistance, influence, none])

/-- More influence on the focus never lowers the terminal preference. -/
theorem more_influence_preferred (radius : ℚ) (records : InfluenceRecords Obs)
    (focus t₁ t₂ horizon : Nat) (ne₁ : focus ≠ t₁) (ne₂ : focus ≠ t₂)
    (i₁ i₂ : ℚ) (known₁ : influence records focus t₁ = some i₁)
    (known₂ : influence records focus t₂ = some i₂) (more : i₂ ≤ i₁) :
    ∃ p₁ p₂, tacticalPreference focus (relationOfDistance radius (estimatedDistance records))
        horizon horizon (some t₁) = some p₁ ∧
      tacticalPreference focus (relationOfDistance radius (estimatedDistance records))
        horizon horizon (some t₂) = some p₂ ∧
      p₂ ≤ p₁ :=
  nearer_preferred radius (1 - i₁) (1 - i₂) _ focus t₁ t₂ horizon ne₁ ne₂
    (by simp [estimatedDistance, known₁]) (by simp [estimatedDistance, known₂])
    (by linarith)

/-- The categorical reading is the special case of all-or-nothing influence.
If every recorded pair has influence 1 exactly where the target repairs the
focus and 0 elsewhere, and the radius lies in `[0, 1)`, the estimated distance
classifies every target as `repairDistance` does, hence (by
`categorical_is_special_case`) as `withRepairs unblocks focusOrElsewhere`. -/
theorem all_or_nothing_is_categorical (radius : ℚ) (nonneg : 0 ≤ radius) (lt : radius < 1)
    (unblocks : Target → Option Target) (records : InfluenceRecords Obs)
    (allOrNothing : ∀ focus target, ∃ w wo, records focus target = some (w, wo) ∧
      totalVariation w wo = if unblocks target = some focus then 1 else 0)
    (focus target : Target) (notSelfRepair : unblocks focus ≠ some focus) :
    relationOfDistance radius (estimatedDistance records) focus target =
      withRepairs unblocks focusOrElsewhere focus target := by
  rw [← categorical_is_special_case radius unblocks focus target notSelfRepair]
  obtain ⟨w, wo, recorded, tv⟩ := allOrNothing focus target
  have far : ¬ (1 : ℚ) ≤ radius := not_le.mpr lt
  have far' : ¬ radius + 1 ≤ radius := by linarith
  by_cases eq : focus = target
  · simp [relationOfDistance, eq]
  · by_cases r : unblocks target = some focus
    · simp [relationOfDistance, estimatedDistance, influence, repairDistance, recorded,
        tv, r, eq, nonneg]
    · simp [relationOfDistance, estimatedDistance, influence, repairDistance, recorded,
        tv, r, eq, far, far']

/-! ## Controls -/

/-- Two observations about the focus: finished or not. -/
abbrev FocusObs := Bool

def finishes : Prediction FocusObs := fun o => if o then 1 else 0
def stalls : Prediction FocusObs := fun o => if o then 0 else 1
def even : Prediction FocusObs := fun _ => 1 / 2

/-- Focus 7. Target 8 is a repair (stalled → finishes), target 9 changes
nothing, target 10 shifts half the mass, target 11 is unrecorded. -/
def exampleRecords : InfluenceRecords FocusObs := fun _ target =>
  if target = 8 then some (finishes, stalls)
  else if target = 9 then some (stalls, stalls)
  else if target = 10 then some (finishes, even)
  else none

theorem repair_is_related :
    outcomeClass 7 (relationOfDistance (1 / 4) (estimatedDistance exampleRecords))
      (some 8) = some .related := by
  norm_num [outcomeClass, relationOfDistance, estimatedDistance, influence, exampleRecords,
    totalVariation, finishes, stalls, scorerClass]

theorem unchanged_is_unrelated :
    outcomeClass 7 (relationOfDistance (1 / 4) (estimatedDistance exampleRecords))
      (some 9) = some .unrelated := by
  norm_num [outcomeClass, relationOfDistance, estimatedDistance, influence, exampleRecords,
    totalVariation, stalls, scorerClass]

/-- Influence 1/2 gives distance 1/2: unrelated at radius 1/4, related at
radius 1/2. The radius is a model parameter, and this is where it bites. -/
theorem half_influence_depends_on_radius :
    outcomeClass 7 (relationOfDistance (1 / 4) (estimatedDistance exampleRecords))
        (some 10) = some .unrelated ∧
      outcomeClass 7 (relationOfDistance (1 / 2) (estimatedDistance exampleRecords))
        (some 10) = some .related := by
  norm_num [outcomeClass, relationOfDistance, estimatedDistance, influence, exampleRecords,
    totalVariation, finishes, even, scorerClass]

theorem unrecorded_target_unscored :
    outcomeClass 7 (relationOfDistance (1 / 4) (estimatedDistance exampleRecords))
      (some 11) = none := by
  norm_num [outcomeClass, relationOfDistance, estimatedDistance, influence, exampleRecords]
  rfl

end DarkTower.WarMachine.R15FocusInfluence
