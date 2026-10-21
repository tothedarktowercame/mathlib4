import DarkTower.WarMachine.R15StrategicTarget

/-!
# R15: the target class read from a distance to the focus

In plain terms: the declared focus orders the outer choice. First finish the
work in hand; otherwise take work near it; if nothing near it can be finished,
the focused work is injured, ordinary dispatch stops and repair begins. A small
remainder of preference stays on everything else.

`R15StrategicTarget` reads each target's class from a relation supplied by the
runtime (`classify-target`), with repairs placed by `withRepairs`. This module
replaces that relation with a distance from the focus and a radius:

* distance known and the target is the focus: `focus`, scored `focused`;
* distance known and at most the radius: `associated`, scored `related`;
* distance known and beyond the radius: `usefulElsewhere`, scored `unrelated`;
* distance unknown: `other`, unscored, as before.

The C schedule (`CTauClassPreference.terminalPreference`, 55/35/5/5) is
unchanged. Only the source of the class changes. The source for C over a
product of outcome factors is Parr, Pezzulo and Friston (2022), *Active
Inference*, ch. 7: preferences are log-probabilities over outcomes, and over
independent outcome factors they add. Here the factors are the reached target
and its class. (Page reference still to be pinned against the book.)

The third tier is not a third weight. Joe, 2026-10-21: being "not well adapted
to its niche" is the condition under which an injury is declared, and the
injury blocks ordinary dispatch. `injuryDeclared` states that condition: no
candidate within the radius of the focus can be finished.

What the distance is: two targets are near when work on one changes what is
expected to be observed about the other. The intended estimator is a
divergence between predicted outcome distributions, recorded round by round in
the M40 valid-time history; the mined unblocks edges and text similarity can
seed it. Nothing here assumes such an estimate exists or has signal. This
module only fixes how a distance, once supplied, sets the class, and shows
that the categorical reading of `R15StrategicTarget` is the special case of a
distance with three values.
-/

namespace DarkTower.WarMachine.R15FocusDistance

open DarkTower.WarMachine.CTauClassPreference
open DarkTower.WarMachine.R15StrategicTarget

/-- Distance from the focus to a target. `none` means no estimate. -/
abbrev TargetDistance := Target → Target → Option ℚ

/-- The relation a distance assigns, for a given radius. The focus itself is
`focus`; an unknown distance stays unscored. -/
def relationOfDistance (radius : ℚ) (distance : TargetDistance)
    (focus target : Target) : TargetRelation :=
  if focus = target then .focus
  else match distance focus target with
    | none => .other 0
    | some d => if d ≤ radius then .associated else .usefulElsewhere

/-- A target at known distance within the radius is scored `related`. -/
theorem within_radius_is_related (radius d : ℚ) (distance : TargetDistance)
    (focus target : Target) (ne : focus ≠ target)
    (known : distance focus target = some d) (near : d ≤ radius) :
    outcomeClass focus (relationOfDistance radius distance) (some target) =
      some .related := by
  simp [outcomeClass, relationOfDistance, ne, known, near, scorerClass]

/-- A target with no distance estimate is unscored, not given a class. -/
theorem unknown_distance_unscored (radius : ℚ) (distance : TargetDistance)
    (focus target : Target) (ne : focus ≠ target)
    (unknown : distance focus target = none) :
    outcomeClass focus (relationOfDistance radius distance) (some target) = none := by
  simp [outcomeClass, relationOfDistance, ne, unknown, scorerClass]

/-- Moving closer never lowers the terminal preference: of two off-focus
targets at known distances, the nearer one gets at least the mass of the
farther one. -/
theorem nearer_preferred (radius d₁ d₂ : ℚ) (distance : TargetDistance)
    (focus t₁ t₂ horizon : Nat) (ne₁ : focus ≠ t₁) (ne₂ : focus ≠ t₂)
    (known₁ : distance focus t₁ = some d₁) (known₂ : distance focus t₂ = some d₂)
    (closer : d₁ ≤ d₂) :
    ∃ p₁ p₂, tacticalPreference focus (relationOfDistance radius distance)
        horizon horizon (some t₁) = some p₁ ∧
      tacticalPreference focus (relationOfDistance radius distance)
        horizon horizon (some t₂) = some p₂ ∧
      p₂ ≤ p₁ := by
  by_cases h₁ : d₁ ≤ radius <;> by_cases h₂ : d₂ ≤ radius
  · exact ⟨35 / 100, 35 / 100, by
      simp [tacticalPreference, outcomeClass, relationOfDistance, ne₁, ne₂,
        known₁, known₂, h₁, h₂, scorerClass, classPreference, terminalPreference]⟩
  · exact ⟨35 / 100, 5 / 100, by
      simp [tacticalPreference, outcomeClass, relationOfDistance, ne₁, ne₂,
        known₁, known₂, h₁, h₂, scorerClass, classPreference, terminalPreference]
      norm_num⟩
  · exact absurd (le_trans closer h₂) h₁
  · exact ⟨5 / 100, 5 / 100, by
      simp [tacticalPreference, outcomeClass, relationOfDistance, ne₁, ne₂,
        known₁, known₂, h₁, h₂, scorerClass, classPreference, terminalPreference]⟩

/-- The distance that reproduces `withRepairs unblocks focusOrElsewhere`: a
repair of the focused work sits at the radius, everything else beyond it. -/
def repairDistance (radius : ℚ) (unblocks : Target → Option Target) :
    TargetDistance :=
  fun focus target => if unblocks target = some focus then some radius else some (radius + 1)

/-- The categorical reading of `R15StrategicTarget` is a special case: with
`repairDistance`, the distance relation agrees with `withRepairs` over
`focusOrElsewhere` on every target. The one exception is a focus listed as
repairing itself, which `withRepairs` would demote to `associated`. -/
theorem categorical_is_special_case (radius : ℚ) (unblocks : Target → Option Target)
    (focus target : Target) (notSelfRepair : unblocks focus ≠ some focus) :
    relationOfDistance radius (repairDistance radius unblocks) focus target =
      withRepairs unblocks focusOrElsewhere focus target := by
  by_cases eq : focus = target
  · subst eq
    cases h : unblocks focus with
    | none => simp [relationOfDistance, withRepairs, focusOrElsewhere, h]
    | some unblocked =>
      have u : unblocked ≠ focus := fun e => notSelfRepair (by rw [h, e])
      simp [relationOfDistance, withRepairs, focusOrElsewhere, h, u]
  · cases h : unblocks target with
    | none =>
      simp [relationOfDistance, repairDistance, withRepairs, focusOrElsewhere, eq, h]
    | some unblocked =>
      by_cases u : unblocked = focus
      · subst u
        simp [relationOfDistance, repairDistance, withRepairs, eq, h]
      · simp [relationOfDistance, repairDistance, withRepairs, focusOrElsewhere, eq, h, u]

/-- A candidate is near the focus when it is the focus or its distance is
known and within the radius. -/
def near (radius : ℚ) (distance : TargetDistance) (focus target : Target) : Bool :=
  decide (focus = target) ||
    match distance focus target with
    | none => false
    | some d => decide (d ≤ radius)

/-- The injury condition: no candidate near the focus can be finished. Under
it, ordinary dispatch is blocked and repair begins. Read it over the ordinary
candidates only: a finishable repair of the focus is itself near the focus
and makes the condition false (`R15InjuryTier.finishable_repair_cancels_gate`).
`R15InjuryTier` replaces this switch with one comparison of G. -/
def injuryDeclared (radius : ℚ) (distance : TargetDistance)
    (finishable : Target → Bool) (focus : Target) (candidates : List Target) : Bool :=
  !candidates.any fun target => near radius distance focus target && finishable target

/-- Ordinary dispatch runs exactly when no injury is declared. -/
def dispatchAllowed (radius : ℚ) (distance : TargetDistance)
    (finishable : Target → Bool) (focus : Target) (candidates : List Target) : Bool :=
  !injuryDeclared radius distance finishable focus candidates

/-- If the focus itself is a finishable candidate, there is no injury. -/
theorem finishable_focus_no_injury (radius : ℚ) (distance : TargetDistance)
    (finishable : Target → Bool) (focus : Target) (candidates : List Target)
    (member : focus ∈ candidates) (done : finishable focus = true) :
    injuryDeclared radius distance finishable focus candidates = false := by
  simp only [injuryDeclared, Bool.not_eq_false', List.any_eq_true]
  exact ⟨focus, member, by simp [near, done]⟩

/-- Control: unfinishable work far from the focus does not declare an injury
while a near candidate can be finished. Focus 7, target 8 near and finishable,
target 9 far and stuck. -/
theorem far_stuck_work_is_not_an_injury :
    injuryDeclared 1 (fun _ t => if t = 8 then some 1 else some 5)
      (fun t => t ≠ 9 && t ≠ 7) 7 [7, 8, 9] = false := by
  decide

/-- Control: when the focus and everything near it are stuck, an injury is
declared even though a far candidate could be finished. -/
theorem stuck_neighbourhood_is_an_injury :
    injuryDeclared 1 (fun _ t => if t = 8 then some 1 else some 5)
      (fun t => t = 9) 7 [7, 8, 9] = true := by
  decide

end DarkTower.WarMachine.R15FocusDistance
