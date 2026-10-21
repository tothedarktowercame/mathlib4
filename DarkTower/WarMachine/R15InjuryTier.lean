import DarkTower.WarMachine.R15FocusDistance
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# R15: the injury tier as one comparison of G

In plain terms: when the focused work is stuck, its rounds are predicted to
end in stop-the-line, so a round that repairs it scores better on the same
objective that ranks ordinary work. No separate branch is needed to choose the
repair.

The runtime has a separate branch. At futon2 `6b2bd34f6`,
`meta_live_outer_selector.clj/select-live` sets `injury?` when any repair
(`:algorithm`) task is present; every ordinary candidate is then excluded with
`:ineligible-reason :machine-injury-active`, and the choice is made among the
repairs by `:machine-injury-repair-cost`, which is 0 for every repair. The
outer-learning scores are computed but recorded as advisory
(`:scores-consumed false`). `branchAdmits` states that rule.

Proposal C (`futon2/holes/labs/wm-contract/PROPOSAL-outer-focus-class-2026-10-21.md`)
is to retire the branch: an injury lowers the predicted chance of reaching the
focused targets, so they score worse and the related repair wins in the same
comparison. This module states that comparison and proves where it agrees with
the branch and where it does not.

The objective is the risk term of the expected free energy,
`D_KL[Q(o | π) ‖ C]`, over the ending classes of `CTauClassPreference`
(Parr, Pezzulo and Friston (2022), *Active Inference*, ch. 2, the
risk-plus-ambiguity form of G; equation number to be pinned against the book).
It is `finiteClassRisk`, the runtime `outcome-risk`. Ambiguity is taken equal
across candidates and left out. A candidate is a target and the predicted
probability `reach` that a round on it reaches the target; the rest of the
mass is stop-the-line, as in `R15StrategicTarget.outcomeClass`. The class of
the target comes from the focus in force through any relation, for example
`withRepairs` or a distance (`R15FocusDistance`, `R15FocusInfluence`).

`risk_eq` reduces the risk to `log 20 - value`, where
`value = H(reach) + reach · log (20 · C(class))` and `H` is the binary
entropy. With the terminal 55/35/5/5 schedule, `20 · C` is 11 for focused,
7 for related and 1 for unrelated, so:

* a stuck candidate (reach 0) has value 0, whatever its class;
* an unrelated candidate has value `H(reach)`, at most `log 2`;
* a related repair with reach `ρ > 0` has value at least `ρ · log 7 > 0`.

Hence (`injury_selects_repair`): if every other candidate is stuck, any
repair of the focus with positive reach has strictly the lowest risk. If the
others are stuck or unrelated, the repair still wins once `log 2 < ρ · log 7`
(`repair_beats_stuck_or_unrelated`). The `H` term is the epistemic part
of the risk. It favours an outcome that is uncertain between two equally
preferred classes, so an unrelated candidate with reach 1/2 can beat a repair
whose reach is small. That is a property of G, not of this encoding. The
replay should look for it.

Where the comparison and the branch disagree (controls below):

* the focused work is still finishable while a repair is open: the branch
  takes the repair, G takes the focused work (`finishable_focus_beats_repair`);
* the repair unblocks a target that is not the focus: it is scored
  `unrelated`, and G prefers ordinary work with an uncertain outcome
  (`off_focus_repair_loses`);
* when the focus is stuck and the repair is for the focus, the two agree
  (`stuck_focus_agrees`).

The gate in `R15FocusDistance`. `injuryDeclared` says that no candidate near
the focus can be finished. A repair of the focus is near it
(`repairDistance` puts it at the radius). So a finishable repair among the
candidates makes `injuryDeclared` false (`finishable_repair_cancels_gate`).
The gate is only coherent when read over the ordinary candidates. Under this
module it is not a switch at all: it is the condition under which
`injury_selects_repair` applies.

What this does not settle: where `reach` comes from. The runtime must predict,
for each candidate, the chance that a round on it reaches the target. An
injury is the observation that lowers it for the focused targets. Nothing
here assumes such predictions exist; a candidate without a class stays
unscored (`candidateValue` is `none`).
-/

namespace DarkTower.WarMachine.R15InjuryTier

open DarkTower.WarMachine.CTauClassPreference
open DarkTower.WarMachine.R15StrategicTarget
open DarkTower.WarMachine.R15FocusDistance
open Real

/-- The predicted ending class of a round on a target of class `k`: the target
is reached with probability `reach`; otherwise the round ends in
stop-the-line. -/
def candidatePrediction (k : EndingClass) (reach : ℚ) : Distribution :=
  fun e => (if e = k then reach else 0) + (if e = .stopTheLine then 1 - reach else 0)

/-- The classes a reached target can be scored in. -/
def ReachedClass (k : EndingClass) : Prop :=
  k = .focused ∨ k = .related ∨ k = .unrelated

/-- `outcomeClass` of a reached target is always a reached class. -/
theorem outcomeClass_reached (focus : Target) (relation : Target → Target → TargetRelation)
    (target : Target) (k : EndingClass)
    (h : outcomeClass focus relation (some target) = some k) : ReachedClass k := by
  unfold outcomeClass at h
  cases hr : relation focus target <;> simp [scorerClass, hr] at h <;> subst h <;>
    simp [ReachedClass]

theorem sum_endingClass (f : EndingClass → ℝ) :
    ∑ e, f e = f .focused + f .related + f .unrelated + f .stopTheLine + f .notYetEvaluated := by
  rw [show (Finset.univ : Finset EndingClass) =
    {.focused, .related, .unrelated, .stopTheLine, .notYetEvaluated} from by decide]
  simp [add_assoc]

/-- One term of `finiteClassRisk`, with its zero case. -/
theorem gibbs_term (x : ℚ) (c : ℝ) (hc : c ≠ 0) :
    (if x = 0 then 0 else (x : ℝ) * log ((x : ℝ) / c)) = x * log x - x * log c := by
  by_cases hx : x = 0
  · simp [hx]
  · have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    simp [hx, log_div hx' hc, mul_sub]

/-- How much better than stopping a candidate is: `log 20` minus its risk. -/
noncomputable def value (k : EndingClass) (reach : ℚ) : ℝ :=
  binEntropy reach + reach * log (20 * terminalPreference k)

/-- The risk of a candidate against the terminal C schedule. -/
theorem risk_eq (k : EndingClass) (hk : ReachedClass k) (reach : ℚ) :
    finiteClassRisk (candidatePrediction k reach) terminalPreference =
      log 20 - value k reach := by
  have h5 : log ((5 : ℝ) / 100) = - log 20 := by
    rw [show (5 : ℝ) / 100 = 20⁻¹ by norm_num, log_inv]
  rcases hk with rfl | rfl | rfl <;>
  · simp only [finiteClassRisk, sum_endingClass, candidatePrediction]
    simp only [reduceCtorEq, if_true, if_false, zero_add, add_zero]
    rw [gibbs_term _ _ (by norm_num [terminalPreference]),
      gibbs_term _ _ (by norm_num [terminalPreference])]
    simp only [value, binEntropy, terminalPreference, log_inv]
    push_cast
    rw [log_mul (by norm_num) (by norm_num), h5]
    ring

/-- The terminal schedule supports every candidate prediction, so the
runtime risk is the finite Gibbs sum, not `:infinite`. -/
theorem candidate_supported (k : EndingClass) (hk : ReachedClass k) (reach : ℚ) :
    ¬ Unsupported (candidatePrediction k reach) terminalPreference := by
  rintro ⟨e, positive, zero⟩
  rcases hk with rfl | rfl | rfl <;> cases e <;>
    simp [candidatePrediction, terminalPreference] at positive zero

theorem classRisk_eq (k : EndingClass) (hk : ReachedClass k) (reach : ℚ) :
    classRisk (candidatePrediction k reach) terminalPreference =
      ((log 20 - value k reach : ℝ) : EReal) := by
  simp [classRisk, candidate_supported k hk, risk_eq k hk]

/-- Lower risk is higher value. -/
theorem risk_lt_iff (k₁ k₂ : EndingClass) (h₁ : ReachedClass k₁) (h₂ : ReachedClass k₂)
    (r₁ r₂ : ℚ) :
    finiteClassRisk (candidatePrediction k₁ r₁) terminalPreference <
        finiteClassRisk (candidatePrediction k₂ r₂) terminalPreference ↔
      value k₂ r₂ < value k₁ r₁ := by
  rw [risk_eq k₁ h₁, risk_eq k₂ h₂]
  constructor <;> intro h <;> linarith

/-! ## Values by class -/

theorem value_focused (r : ℚ) : value .focused r = binEntropy r + r * log 11 := by
  norm_num [value, terminalPreference]

theorem value_related (r : ℚ) : value .related r = binEntropy r + r * log 7 := by
  norm_num [value, terminalPreference]

theorem value_unrelated (r : ℚ) : value .unrelated r = binEntropy r := by
  norm_num [value, terminalPreference]

/-- A stuck candidate is as good as stopping, whatever its class. -/
theorem stuck_value (k : EndingClass) : value k 0 = 0 := by
  simp [value]

/-- An unrelated candidate is worth at most `log 2`, whatever its reach. -/
theorem unrelated_value_le (r : ℚ) : value .unrelated r ≤ log 2 := by
  rw [value_unrelated]; exact binEntropy_le_log_two

/-- A repair with positive reach is worth at least `reach · log 7`, which is
positive. -/
theorem related_value_ge (r : ℚ) (pos : 0 < r) (le : r ≤ 1) :
    (r : ℝ) * log 7 ≤ value .related r := by
  rw [value_related]
  have := binEntropy_nonneg (p := (r : ℝ)) (by exact_mod_cast pos.le) (by exact_mod_cast le)
  linarith

theorem related_value_pos (r : ℚ) (pos : 0 < r) (le : r ≤ 1) : 0 < value .related r := by
  have : 0 < (r : ℝ) * log 7 :=
    mul_pos (by exact_mod_cast pos) (log_pos (by norm_num))
  linarith [related_value_ge r pos le]

/-! ## The injury tier -/

/-- A candidate for the outer choice: a target and the predicted chance that
a round on it reaches the target. -/
structure Candidate where
  target : Target
  reach : ℚ
  deriving DecidableEq, Repr

/-- The candidate's value under the focus in force, or `none` when its class
is unknown. -/
noncomputable def candidateValue (focus : Target) (relation : Target → Target → TargetRelation)
    (c : Candidate) : Option ℝ :=
  (outcomeClass focus relation (some c.target)).map fun k => value k c.reach

/-- If every other candidate is stuck, a repair scored `related` with
positive reach has strictly the highest value, that is the lowest risk. -/
theorem injury_selects_repair (focus : Target) (relation : Target → Target → TargetRelation)
    (candidates : List Candidate) (repair : Candidate)
    (related : outcomeClass focus relation (some repair.target) = some .related)
    (pos : 0 < repair.reach) (le : repair.reach ≤ 1)
    (stuck : ∀ c ∈ candidates, c ≠ repair → c.reach = 0) :
    candidateValue focus relation repair = some (value .related repair.reach) ∧
    ∀ c ∈ candidates, c ≠ repair → ∀ v, candidateValue focus relation c = some v →
      v < value .related repair.reach := by
  refine ⟨by simp [candidateValue, related], ?_⟩
  intro c member ne v hv
  simp only [candidateValue, Option.map_eq_some_iff] at hv
  obtain ⟨k, _, rfl⟩ := hv
  rw [stuck c member ne, stuck_value]
  exact related_value_pos _ pos le

/-- If every other candidate is stuck or unrelated, a related repair with
`log 2 < reach · log 7` still wins. -/
theorem repair_beats_stuck_or_unrelated (focus : Target)
    (relation : Target → Target → TargetRelation)
    (candidates : List Candidate) (repair : Candidate)
    (related : outcomeClass focus relation (some repair.target) = some .related)
    (pos : 0 < repair.reach) (le : repair.reach ≤ 1)
    (enough : log 2 < (repair.reach : ℝ) * log 7)
    (others : ∀ c ∈ candidates, c ≠ repair →
      c.reach = 0 ∨ outcomeClass focus relation (some c.target) = some .unrelated) :
    candidateValue focus relation repair = some (value .related repair.reach) ∧
    ∀ c ∈ candidates, c ≠ repair → ∀ v, candidateValue focus relation c = some v →
      v < value .related repair.reach := by
  refine ⟨by simp [candidateValue, related], ?_⟩
  intro c member ne v hv
  have ge := related_value_ge _ pos le
  rcases others c member ne with zero | unrelated
  · simp only [candidateValue, Option.map_eq_some_iff] at hv
    obtain ⟨k, _, rfl⟩ := hv
    rw [zero, stuck_value]
    linarith [related_value_pos _ pos le]
  · simp only [candidateValue, unrelated, Option.map_some, Option.some.injEq] at hv
    subst hv
    linarith [unrelated_value_le c.reach]

/-- A finishable repair of the focus, at the radius under `repairDistance`,
is near the focus, so `injuryDeclared` is false while it is a candidate. -/
theorem finishable_repair_cancels_gate (radius : ℚ) (unblocks : Target → Option Target)
    (finishable : Target → Bool) (focus repair : Target) (candidates : List Target)
    (member : repair ∈ candidates) (repairs : unblocks repair = some focus)
    (done : finishable repair = true) :
    injuryDeclared radius (repairDistance radius unblocks) finishable focus candidates =
      false := by
  simp only [injuryDeclared, Bool.not_eq_false', List.any_eq_true]
  exact ⟨repair, member, by simp [near, repairDistance, repairs, done]⟩

/-- The runtime branch: when any repair is a candidate, only repairs are
admitted. -/
def branchAdmits (isRepair : Target → Bool) (candidates : List Candidate)
    (c : Candidate) : Bool :=
  if candidates.any (fun d => isRepair d.target) then isRepair c.target else true

/-! ## Controls

Focus 7. Target 3 repairs 7, target 4 repairs 8, target 9 is ordinary work
elsewhere. Classes come from `withRepairs` over `focusOrElsewhere`. -/

def unblocksExample : Target → Option Target :=
  fun t => if t = 3 then some 7 else if t = 4 then some 8 else none

def relationExample : Target → Target → TargetRelation :=
  withRepairs unblocksExample focusOrElsewhere

def isRepairExample (t : Target) : Bool := t = 3 || t = 4

theorem binEntropy_half : binEntropy (1 / 2) = log 2 := by
  rw [one_div]; exact binEntropy_two_inv

/-- Agreement. The focus is stuck, the repair of the focus reaches with
probability 1/2, work elsewhere with 1/2. G ranks the repair first; the branch
admits only the repair. -/
theorem stuck_focus_agrees :
    let focusC : Candidate := ⟨7, 0⟩
    let repairC : Candidate := ⟨3, 1 / 2⟩
    let elsewhereC : Candidate := ⟨9, 1 / 2⟩
    candidateValue 7 relationExample focusC = some 0 ∧
    candidateValue 7 relationExample elsewhereC = some (log 2) ∧
    candidateValue 7 relationExample repairC = some (log 2 + 1 / 2 * log 7) ∧
    0 < log 2 ∧ 0 < log 7 ∧
    branchAdmits isRepairExample [focusC, repairC, elsewhereC] repairC = true ∧
    branchAdmits isRepairExample [focusC, repairC, elsewhereC] focusC = false ∧
    branchAdmits isRepairExample [focusC, repairC, elsewhereC] elsewhereC = false := by
  refine ⟨?_, ?_, ?_, log_pos (by norm_num), log_pos (by norm_num), by decide, by decide,
    by decide⟩ <;>
  norm_num [candidateValue, relationExample, withRepairs, unblocksExample, focusOrElsewhere,
    outcomeClass, scorerClass, value, terminalPreference, binEntropy_half]

/-- Disagreement 1. The focus is still finishable (reach 1) while a repair of
it is open (reach 1). The branch admits only the repair; G prefers the
focused work, since `log 7 < log 11`. -/
theorem finishable_focus_beats_repair :
    let focusC : Candidate := ⟨7, 1⟩
    let repairC : Candidate := ⟨3, 1⟩
    candidateValue 7 relationExample focusC = some (log 11) ∧
    candidateValue 7 relationExample repairC = some (log 7) ∧
    log 7 < log 11 ∧
    branchAdmits isRepairExample [focusC, repairC] focusC = false := by
  refine ⟨?_, ?_, log_lt_log (by norm_num) (by norm_num), by decide⟩ <;>
  norm_num [candidateValue, relationExample, withRepairs, unblocksExample, focusOrElsewhere,
    outcomeClass, scorerClass, value, terminalPreference, binEntropy_half]

/-- Disagreement 2. The only repair (target 4) unblocks target 8, not the
focus, so it is scored `unrelated`. Sure to succeed, it is worth 0; work
elsewhere with reach 1/2 is worth `log 2`. The branch admits only the repair. -/
theorem off_focus_repair_loses :
    let repairC : Candidate := ⟨4, 1⟩
    let elsewhereC : Candidate := ⟨9, 1 / 2⟩
    candidateValue 7 relationExample repairC = some 0 ∧
    candidateValue 7 relationExample elsewhereC = some (log 2) ∧
    0 < log 2 ∧
    branchAdmits isRepairExample [repairC, elsewhereC] elsewhereC = false := by
  refine ⟨?_, ?_, log_pos (by norm_num), by decide⟩ <;>
  norm_num [candidateValue, relationExample, withRepairs, unblocksExample, focusOrElsewhere,
    outcomeClass, scorerClass, value, terminalPreference, binEntropy_half]

/-- The epistemic part of G. A repair of the focus with reach 1/10 is worth
less than work elsewhere with reach 1/2: `H(1/10) + log 7 / 10 < log 2`. -/
theorem weak_repair_loses_to_uncertain_elsewhere :
    value .related (1 / 10) < value .unrelated (1 / 2) := by
  rw [value_related, value_unrelated]
  have half : (((1 / 2 : ℚ)) : ℝ) = 2⁻¹ := by norm_num
  have tenth : (((1 / 10 : ℚ)) : ℝ) = 1 / 10 := by norm_num
  rw [half, binEntropy_two_inv, tenth]
  have entropy : binEntropy (1 / 10) = 1 / 10 * log 10 + 9 / 10 * log (10 / 9) := by
    norm_num [binEntropy]
  -- log 10 + log 7 = log 70 < log 128 = 7 log 2, and log (10/9) ≤ 1/9.
  have seventy : log 10 + log 7 < 7 * log 2 := by
    have pow : (7 : ℝ) * log 2 = log (2 ^ 7) := by rw [log_pow]; norm_num
    rw [← log_mul (by norm_num) (by norm_num), pow]
    exact log_lt_log (by norm_num) (by norm_num)
  have ninth : log ((10 : ℝ) / 9) ≤ 10 / 9 - 1 := log_le_sub_one_of_pos (by norm_num)
  have l2 := log_two_gt_d9
  rw [entropy]
  nlinarith

/-- Construct the gate case: focus 7 stuck, a finishable repair 3 of it.
`injuryDeclared` is false, though the focus is stuck. -/
theorem gate_cancelled_example :
    injuryDeclared 1 (repairDistance 1 unblocksExample) (fun t => t = 3) 7 [7, 3, 9] = false :=
  by decide

end DarkTower.WarMachine.R15InjuryTier
