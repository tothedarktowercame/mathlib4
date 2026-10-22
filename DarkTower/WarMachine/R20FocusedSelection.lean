import DarkTower.WarMachine.R20Certificate
import DarkTower.WarMachine.R15InjuryTier

/-!
# R20: the outer choice scored against a C that depends on the focus

In plain terms: the certificate already checks that the strategic row sets C
and that the class-preference row reports the risk of selection's predicted
class distribution against that C. It does not check that the prediction was
classified under the focus the strategic row reports, nor that the outer
choice among targets was made by that risk. This module adds both, so a
certified click carries one chain: focus → class of each candidate → risk of
each candidate → the chosen candidate → the prediction the class row scored.

The C over targets is `terminalPreference (class focus target)`, which
`R15StrategicTarget.tacticalPreference` already states; the focus enters only
through the class (`preference_depends_on_focus_only_through_class`). The risk
of a candidate is `R15InjuryTier.risk_eq`: `log 20 - value class reach`. The
outer choice is a single comparison of that value over every candidate, with
no injury branch. Joe decided on 2026-10-21 that where this comparison and the
runtime injury branch disagree, the comparison stands.

`relation` is the model's target relation (for example
`withRepairs unblocks focusOrElsewhere`). The strategic row records, for each
candidate, the relation it used; `OuterSelectionConforms` requires that to be
`relation focus target` at the focus the row reports. A classification made
under an earlier focus is therefore refused (`staleFocus_refused`).

Results:

* `certified_prediction`: in a focus-certified click, the class row's
  predicted distribution is `candidatePrediction k reach` for the chosen
  candidate, with `k` its class under the strategic row's focus;
* `certified_terminal_risk`: at the horizon, the class row's reported risk is
  `log 20 - value k reach` of the chosen candidate;
* `certified_selects_repair`: if every other candidate is stuck, the chosen
  candidate is the repair of the focus;
* `prediction_depends_on_focus`: the same choice under focus 7 and under focus
  8 yields different predicted class distributions.

Controls: the runtime branch's choice when the focus is still finishable
(`branchChoice_refused`), a classification made under the previous focus
(`staleFocus_refused`), and a candidate with no scored class
(`unscored_refused`). `stuckFocus_conforms` shows the conditions can be met.
-/

namespace DarkTower.WarMachine.R20FocusedSelection

open DarkTower.WarMachine.CTauClassPreference
open DarkTower.WarMachine.R15StrategicTarget
open DarkTower.WarMachine.R15InjuryTier
open DarkTower.WarMachine.R20Certificate
open Real

noncomputable section
variable {Policy : Type} [Fintype Policy] [Nonempty Policy]
attribute [local instance] Classical.propDecidable

/-- The outer choice: the candidates scored and the one taken. -/
structure OuterSelection where
  candidates : List Candidate
  selected : Candidate

/-- The strategic row recorded, for this target, the model's relation to the
focus it reports. -/
def ClassifiedAtFocus (relation : Target → Target → TargetRelation)
    (tick : StrategicTickRecord) (t : Target) : Prop :=
  ∃ receipt ∈ tick.candidates,
    receipt.target = t ∧ receipt.recordedRelation = relation tick.focus t

/-- The chosen candidate is among those scored; every candidate was
classified under the strategic row's focus and has a scored class; and no
candidate has a higher value (lower risk) than the one chosen. -/
def OuterSelectionConforms (relation : Target → Target → TargetRelation)
    (tick : StrategicTickRecord) (σ : OuterSelection) : Prop :=
  σ.selected ∈ σ.candidates ∧
  (∀ c ∈ σ.candidates, ClassifiedAtFocus relation tick c.target ∧
    (candidateValue tick.focus relation c).isSome) ∧
  ∀ c ∈ σ.candidates, ∀ v w, candidateValue tick.focus relation c = some v →
    candidateValue tick.focus relation σ.selected = some w → v ≤ w

/-- Selection's predicted class distribution is that of the chosen candidate,
classified under the strategic row's focus. -/
def SelectionFeedsPrediction (relation : Target → Target → TargetRelation)
    (tick : StrategicTickRecord) (σ : OuterSelection)
    (predicted : Distribution) : Prop :=
  ∃ k, outcomeClass tick.focus relation (some σ.selected.target) = some k ∧
    predicted = candidatePrediction k σ.selected.reach

/-- A click certified by R20 whose outer choice was made by risk under the
strategic row's focus and fed the prediction the class row scored. -/
def FocusCertified (relation : Target → Target → TargetRelation)
    (records : Records Policy) (ports : R20Graph.Ports Policy) (σ : OuterSelection) : Prop :=
  Certified records (certify records) ports ∧
  ∃ s, records .strategicFocus = some s ∧
    OuterSelectionConforms relation s.tick σ ∧
    SelectionFeedsPrediction relation s.tick σ ports.selectionPredicted.value

/-! ## What a focus-certified click says -/

omit [Nonempty Policy] in
/-- The class row scored the chosen candidate's prediction, classified under
the strategic row's focus. -/
theorem certified_prediction (relation : Target → Target → TargetRelation)
    (records : Records Policy) (ports : R20Graph.Ports Policy) (σ : OuterSelection)
    (h : FocusCertified relation records ports σ)
    (s : StrategicFocusRow) (hs : records .strategicFocus = some s)
    (r : ClassPreferenceRow) (hr : records .classPreference = some r) :
    ∃ k, outcomeClass s.tick.focus relation (some σ.selected.target) = some k ∧
      r.predicted = candidatePrediction k σ.selected.reach := by
  obtain ⟨⟨_, wired, reads⟩, s', hs', _, k, hk, feeds⟩ := h
  rw [hs] at hs'
  cases hs'
  refine ⟨k, hk, ?_⟩
  rw [(reads.2.1 r hr).1, wired.predictedRead, feeds]

omit [Nonempty Policy] in
/-- At the horizon, the class row's reported risk is the risk of the chosen
candidate under the focus: `log 20 - value k reach`. -/
theorem certified_terminal_risk (relation : Target → Target → TargetRelation)
    (records : Records Policy) (ports : R20Graph.Ports Policy) (σ : OuterSelection)
    (h : FocusCertified relation records ports σ)
    (s : StrategicFocusRow) (hs : records .strategicFocus = some s)
    (r : ClassPreferenceRow) (hr : records .classPreference = some r)
    (terminal : r.tau = r.horizon) :
    ∃ k, outcomeClass s.tick.focus relation (some σ.selected.target) = some k ∧
      r.reportedRisk = ((log 20 - value k σ.selected.reach : ℝ) : EReal) := by
  obtain ⟨k, hk, predicted⟩ := certified_prediction relation records ports σ h s hs r hr
  refine ⟨k, hk, ?_⟩
  have rowConforms : ClassPreferenceConforms r := by
    obtain ⟨r', hr', c⟩ := ((certified_iff records ports).mp h.1).1 .classPreference
    rw [hr] at hr'
    cases hr'
    exact c
  rw [rowConforms, predicted, terminal, classPreference, if_pos rfl,
    classRisk_eq k (outcomeClass_reached _ _ _ k hk)]

omit [Nonempty Policy] in
/-- If every candidate other than the repair is stuck, a focus-certified
click chose the repair. -/
theorem certified_selects_repair (relation : Target → Target → TargetRelation)
    (records : Records Policy) (ports : R20Graph.Ports Policy) (σ : OuterSelection)
    (h : FocusCertified relation records ports σ)
    (s : StrategicFocusRow) (hs : records .strategicFocus = some s)
    (repair : Candidate) (member : repair ∈ σ.candidates)
    (related : outcomeClass s.tick.focus relation (some repair.target) = some .related)
    (pos : 0 < repair.reach) (le : repair.reach ≤ 1)
    (stuck : ∀ c ∈ σ.candidates, c ≠ repair → c.reach = 0) :
    σ.selected = repair := by
  obtain ⟨_, s', hs', ⟨selMember, scored, best⟩, _⟩ := h
  rw [hs] at hs'
  cases hs'
  by_contra ne
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (scored σ.selected selMember).2
  have repairValue : candidateValue s.tick.focus relation repair =
      some (value .related repair.reach) := by simp [candidateValue, related]
  have selLow := (injury_selects_repair s.tick.focus relation σ.candidates repair
    related pos le stuck).2 σ.selected selMember ne w hw
  have := best repair member _ w repairValue hw
  linarith

/-! ## Controls

Focus 7, as in `R15InjuryTier`: target 3 repairs 7, target 9 is work
elsewhere. -/

def receipt (focus t : Target) : CandidateClassReceipt :=
  ⟨t, relationExample focus t, scorerClass (relationExample focus t)⟩

def tickAt (focus : Target) (targets : List Target) : StrategicTickRecord :=
  ⟨focus, 2, targets.map (receipt focus), classPreference 2⟩

/-- The strategic row of the controls conforms, so they test only the outer
choice. -/
theorem tickAt_conforms (focus : Target) (targets : List Target) :
    StrategicTickConforms (tickAt focus targets) := by
  refine ⟨?_, fun _ _ _ => rfl⟩
  intro c hc
  simp only [tickAt, List.mem_map] at hc
  obtain ⟨t, _, rfl⟩ := hc
  rfl

theorem classified_tickAt (focus t : Target) (targets : List Target) (ht : t ∈ targets) :
    ClassifiedAtFocus relationExample (tickAt focus targets) t :=
  ⟨receipt focus t, List.mem_map.mpr ⟨t, ht, rfl⟩, rfl, rfl⟩

/-- The conditions can be met: the focus is stuck, the repair of it reaches
with probability 1/2 and work elsewhere with 1/2; choosing the repair
conforms. -/
theorem stuckFocus_conforms :
    OuterSelectionConforms relationExample (tickAt 7 [7, 3, 9])
      ⟨[⟨7, 0⟩, ⟨3, 1 / 2⟩, ⟨9, 1 / 2⟩], ⟨3, 1 / 2⟩⟩ := by
  obtain ⟨vFocus, vElse, vRepair, l2, l7, -⟩ := stuck_focus_agrees
  refine ⟨by simp, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨classified_tickAt 7 7 _ (by simp), by simp only [tickAt]; rw [vFocus]; rfl⟩
    · exact ⟨classified_tickAt 7 3 _ (by simp), by simp only [tickAt]; rw [vRepair]; rfl⟩
    · exact ⟨classified_tickAt 7 9 _ (by simp), by simp only [tickAt]; rw [vElse]; rfl⟩
  · intro c hc v w hv hw
    simp only [tickAt] at hv hw
    rw [vRepair] at hw
    cases hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · rw [vFocus] at hv; cases hv; positivity
    · rw [vRepair] at hv; cases hv; exact le_rfl
    · rw [vElse] at hv; cases hv; nlinarith

/-- The branch's choice. The focus is still finishable (reach 1) while a
repair of it is open (reach 1); the runtime branch takes the repair. That
choice does not conform: the focused work has the higher value. -/
theorem branchChoice_refused :
    ¬ OuterSelectionConforms relationExample (tickAt 7 [7, 3])
      ⟨[⟨7, 1⟩, ⟨3, 1⟩], ⟨3, 1⟩⟩ := by
  obtain ⟨vFocus, vRepair, lt, -⟩ := finishable_focus_beats_repair
  rintro ⟨-, -, best⟩
  have := best ⟨7, 1⟩ (by simp) _ _ vFocus vRepair
  linarith

/-- The strategic row reports focus 7, but the candidates were classified
under the previous focus 8. Refused, though the choice would conform under 8. -/
theorem staleFocus_refused :
    ¬ OuterSelectionConforms relationExample
      ⟨7, 2, [receipt 8 7, receipt 8 3, receipt 8 9], classPreference 2⟩
      ⟨[⟨7, 0⟩, ⟨3, 1 / 2⟩, ⟨9, 1 / 2⟩], ⟨3, 1 / 2⟩⟩ := by
  rintro ⟨-, scored, -⟩
  obtain ⟨⟨rc, member, target, recorded⟩, -⟩ := scored ⟨7, 0⟩ (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [receipt, relationExample, withRepairs, unblocksExample, focusOrElsewhere] at target recorded

/-- A candidate whose relation has no scored class cannot be ranked, so a
selection containing it does not conform. -/
theorem unscored_refused :
    ¬ OuterSelectionConforms (fun _ _ => .other 0)
      ⟨7, 2, [⟨7, .other 0, none⟩], classPreference 2⟩
      ⟨[⟨7, 1⟩], ⟨7, 1⟩⟩ := by
  rintro ⟨-, scored, -⟩
  have := (scored ⟨7, 1⟩ (by simp)).2
  simp [candidateValue, outcomeClass, scorerClass] at this

/-- C depends on the focus: the same choice, target 3 with reach 1/2, gives a
different predicted class distribution under focus 7 (related) than under
focus 8 (unrelated), hence a different risk. -/
theorem prediction_depends_on_focus :
    outcomeClass 7 relationExample (some 3) = some .related ∧
    outcomeClass 8 relationExample (some 3) = some .unrelated ∧
    candidatePrediction .related (1 / 2) ≠ candidatePrediction .unrelated (1 / 2) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := congrFun h .related
  norm_num [candidatePrediction] at this
  exact absurd this (by decide)

#print axioms certified_terminal_risk
#print axioms certified_selects_repair
#print axioms branchChoice_refused
#print axioms staleFocus_refused

end
end DarkTower.WarMachine.R20FocusedSelection
