import DarkTower.WarMachine.R20HabitPrior

/-!
# R20: one click that is certified

In plain terms: every result of the form "in a certified click, ..." is only
as good as the existence of a certified click. This module builds one, on two
policies, with all ten rows present and conforming, every edge of the R20
graph wired, and every consumer row judged on its ports.

The click is the simplest the conditions allow, and every value in it is
computed by the definitions it is checked against:

* class preference at the horizon (`H = τ = 1`), so C is the terminal
  preference and the class G is finite: `-log (55/100)` for both policies
  (`R20Graph.k9_terminal_G_finite_and_sensitive`);
* the precision row's G is the full G selection scores by: that class G plus
  each policy's interoceptive risk (`-log (9/10)` for `a`, `-log (1/10)` for `b`);
* fresh habit counts, so E is `1/2` for each policy;
* the same F for both policies, so the precision row's temperature does not
  move (`PrecisionFromObservation.constant_F_posterior_temperature_iff`);
* the interoception gauge of `R20Certificate.goodInteroception`: policy `a` is
  expected to restore the reading, `b` to leave it in alarm.

Results: `example_certified`; `example_prior_prefers_restoring` (the policy
prior, a softmax of that G, puts more mass on `a`); and, by the general theorems,
`example_E` (E is the habit prior, 1/2) and `example_restoring_scores_lower`
(policy `a` scores lower than `b`, through the interoception edge).

This shows the conditions are jointly satisfiable. It says nothing about the
running system: no value here comes from a recorded click.
-/

namespace DarkTower.WarMachine.R20CertifiedExample

open DarkTower.WarMachine.R20Graph
open DarkTower.WarMachine.R20Certificate
open DarkTower.WarMachine.R15TemporalHierarchy
open DarkTower.WarMachine.R15HabitPrior
open DarkTower.WarMachine.R20HabitPrior
open PrecisionFromObservation (TwoPolicy)

noncomputable section
attribute [local instance] Classical.propDecidable

def run : RunId := 0

/-! ## Habit: fresh counts, one witnessed success of `a` -/

def habitRow : TwoTickRecord TwoPolicy :=
  let outcome : FastOutcome TwoPolicy := ⟨.a, true, true⟩
  ⟨[], outcome, advance [] outcome, advance [] outcome⟩

def habitE : TwoPolicy → ℝ := fun π => (policyHabitPrior ([] : SlowState TwoPolicy) (menu TwoPolicy) π : ℝ)

theorem habitE_half (π : TwoPolicy) : habitE π = 1 / 2 := by
  have total : totalAlpha ([] : SlowState TwoPolicy) (menu TwoPolicy) = 2 := by
    rw [totalAlpha_menu2]; simp [policyAlpha, countsFor, freshCounts]; norm_num
  simp only [habitE, policyHabitPrior, total]
  simp [policyAlpha, countsFor, freshCounts]

/-! ## Precision: E from the counts, G at the terminal C, F the same for both -/

def classG : PolicyExpectedFreeEnergy TwoPolicy := terminalG run

def gValue : ℝ := -Real.log (55 / 100)

def fConst : ℝ := (exampleF run).value .a

theorem exampleF_const : (exampleF run).value = fun _ => fConst := by
  funext π; cases π <;> rfl

/-- Each policy's interoceptive risk under the gauge: `a` is certain to read in
range (`-log (9/10)`), `b` certain to read the alarm (`-log (1/10)`). -/
def riskReal : TwoPolicy → ℝ
  | .a => -Real.log (9 / 10)
  | .b => -Real.log (1 / 10)

theorem reportedRisk_eq (π : TwoPolicy) :
    goodInteroception.reportedRisk π = (riskReal π : EReal) := by
  cases π
  · exact R20Interoception.pointMass_risk_of_positive (C := gauge2) (reading := (0 : Fin 2))
      (by norm_num [gauge2]) |>.trans (by norm_num [gauge2, riskReal])
  · exact R20Interoception.pointMass_risk_of_positive (C := gauge2) (reading := (1 : Fin 2))
      (by norm_num [gauge2]) |>.trans (by norm_num [gauge2, riskReal])

/-- The precision row's G: the class G plus the interoceptive risk. -/
def totalG : TwoPolicy → ℝ := fun π => gValue + riskReal π

def precisionRow : PrecisionFromObservation.TickRecord TwoPolicy :=
  { E := habitE, G := totalG, F := (exampleF run).value
    prior := PrecisionFromObservation.priorPolicy 1 habitE totalG
    posterior := PrecisionFromObservation.posteriorPolicy 1 habitE totalG (exampleF run).value
    betaPrior := 1, betaPosterior := 1 }

theorem precisionRow_conforms : PrecisionFromObservation.Conforms precisionRow := by
  refine ⟨fun π => by simp [precisionRow, habitE_half], by norm_num [precisionRow], ?_, rfl, rfl⟩
  show PrecisionFromObservation.IsPosteriorTemperature 1 1 habitE totalG (exampleF run).value
  rw [exampleF_const]
  exact (PrecisionFromObservation.constant_F_posterior_temperature_iff
    (by norm_num) habitE _ fConst).mpr rfl

/-! ## Class preference and strategic focus at the horizon -/

def focusedPoint : CTauClassPreference.Distribution := fun o => if o = .focused then 1 else 0

def classRow : ClassPreferenceRow :=
  { horizon := 1, tau := 1, predicted := focusedPoint
    reportedRisk := CTauClassPreference.classRisk focusedPoint
      (CTauClassPreference.classPreference 1 1) }

def strategicRow : StrategicFocusRow :=
  ⟨7, ⟨7, 1, [], CTauClassPreference.classPreference 1⟩⟩

theorem strategicRow_conforms : StrategicFocusConforms strategicRow :=
  ⟨by simp [strategicRow], fun _ _ _ => rfl⟩

/-! ## The remaining rows -/

def evidenceRow : EvidenceRow :=
  { prior := fun _ => 1 / 2, likelihood := fun _ _ => 1, observation := true
    posterior := EvidenceFromTheProcess.posterior (fun _ => 1 / 2) (fun _ _ => 1) true }

def liveRow : LiveRow := ⟨0, 1, true⟩

theorem liveRow_conforms : LivenessConforms liveRow := by
  intro tick member _
  simp only [List.mem_singleton] at member
  subst member
  simp [R10ScheduledEntrypoint.ChangedState, liveRow]

def independenceRow : IndependenceRow := ⟨0, 1⟩

/-- Both agents believe agent 0 owns the shared variable. -/
def jointRow : JointRow := fun _ _ => 0

theorem jointRow_conforms : R11JointAction.OneWriter jointRow := by
  intro v; cases v; decide

def costRow : CostRow :=
  { jobs := [⟨true, 1, 1, 2⟩], msThroughSelection := 1, msAfterSelection := 1
    reportedTotalTokens := 2, reportedTokensThroughSelection := 2
    reportedTokensAfterSelection := 0 }

theorem costRow_conforms : CostConforms costRow := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [costRow, totalTokens, tokensWhere]

/-! ## The click -/

def records : Records TwoPolicy
  | .precision => some precisionRow
  | .evidence => some evidenceRow
  | .habit => some habitRow
  | .classPreference => some classRow
  | .strategicFocus => some strategicRow
  | .liveness => some liveRow
  | .independence => some independenceRow
  | .jointAction => some jointRow
  | .cost => some costRow
  | .interoception => some goodInteroception

def ports : Ports TwoPolicy :=
  { runId := run
    habitRowE := ⟨habitE, .node .habit, run⟩
    selectionHabit := ⟨habitE, .selection, run⟩
    precisionHabit := ⟨habitE, .selection, run⟩
    selectionG := classG, precisionG := classG
    inferenceF := exampleF run, precisionF := exampleF run
    strategicPreference := ⟨CTauClassPreference.classPreference 1 1, .node .strategicFocus, run⟩
    classPreference := ⟨CTauClassPreference.classPreference 1 1, .node .strategicFocus, run⟩
    selectionPredicted := ⟨focusedPoint, .selection, run⟩
    classPredicted := ⟨focusedPoint, .selection, run⟩
    precisionBeta := ⟨1, .node .precision, run⟩
    interoceptionRisk := ⟨goodInteroception.reportedRisk, .node .interoception, run⟩
    selectionInteroceptionRisk := ⟨goodInteroception.reportedRisk, .node .interoception, run⟩ }

theorem rows_conform : ∀ node, ∃ r, records node = some r ∧ conforms node r := by
  intro node
  cases node
  · exact ⟨_, rfl, precisionRow_conforms⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, strategicRow_conforms⟩
  · exact ⟨_, rfl, liveRow_conforms⟩
  · exact ⟨_, rfl, by simp [conforms, IndependenceConforms, independenceRow]⟩
  · exact ⟨_, rfl, jointRow_conforms⟩
  · exact ⟨_, rfl, costRow_conforms⟩
  · exact ⟨_, rfl, goodInteroception_conforms⟩

theorem wired : Wired records ports := by
  constructor
  · intro n _; cases n <;> simp [records]
  all_goals rfl

theorem reads : RowsReadPorts records ports := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [records, Option.some.injEq] at hr
    subst hr
    refine ⟨rfl, ?_, rfl⟩
    funext π
    show ((gValue + riskReal π : ℝ) : EReal) =
      (terminalG run).value π + goodInteroception.reportedRisk π
    rw [(k9_terminal_G_finite_and_sensitive run π).1, reportedRisk_eq]
    rfl
  · intro r hr
    simp only [records, Option.some.injEq] at hr
    subst hr
    refine ⟨rfl, rfl, rfl, fun t => ?_⟩
    have bound := t.isLt
    have ticks : ports.selectionG.ticks = 1 := rfl
    have : t.val = 0 := by omega
    simp [ports, classG, terminalG, focusedG, classRow, this]
  · intro s r hs hr
    simp only [records, Option.some.injEq] at hs hr
    subst hs hr
    rfl
  · intro h hh π
    simp only [records, Option.some.injEq] at hh
    subst hh
    rfl
  · intro r hr
    simp only [records, Option.some.injEq] at hr
    subst hr
    rfl

/-- One click satisfies the whole certificate. -/
theorem example_certified : Certified records (certify records) ports :=
  (certified_iff records ports).mpr ⟨rows_conform, wired, reads⟩

/-! ## What the general theorems then say about it -/

/-- E is the habit prior: 1/2 for each policy. -/
theorem example_E (π : TwoPolicy) : ports.selectionHabit.value π = 1 / 2 := by
  rw [selection_E_is_habit example_certified (h := habitRow) rfl π]
  exact habitE_half π

/-- Policy `a`, expected to restore the reading, scores lower than `b`. -/
theorem example_restoring_scores_lower : selectionScore ports .a < selectionScore ports .b := by
  have g := fun π => (k9_terminal_G_finite_and_sensitive run π).1
  exact certified_restoring_policy_scores_lower records ports example_certified
    goodInteroception rfl
    (restored := (show Fin goodInteroception.size from (0 : Fin 2)))
    (outside := (show Fin goodInteroception.size from (1 : Fin 2)))
    (Finset.mem_singleton_self _) (by show (1 : Fin 2) ∉ ({0} : Finset (Fin 2)); simp)
    (by show (0 : ℝ) < gauge2 0; norm_num [gauge2])
    (by show (0 : ℝ) < gauge2 1; norm_num [gauge2])
    rfl rfl gValue (g .a) (g .b)

/-- The policy prior is a softmax of the full G, so with equal E it puts more
mass on `a`, whose interoceptive risk is lower. -/
theorem example_prior_prefers_restoring : precisionRow.prior .b < precisionRow.prior .a := by
  have hlog : Real.log (1 / 10) < Real.log (9 / 10) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hG : totalG .a < totalG .b := by
    simp only [totalG, riskReal]; linarith
  simp only [precisionRow, PrecisionFromObservation.priorPolicy, PrecisionFromObservation.softmax,
    habitE_half, div_one]
  apply div_lt_div_of_pos_right _ (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)
  exact Real.exp_lt_exp.mpr (by linarith)

#print axioms example_prior_prefers_restoring
#print axioms example_certified
#print axioms example_restoring_scores_lower

end
end DarkTower.WarMachine.R20CertifiedExample
