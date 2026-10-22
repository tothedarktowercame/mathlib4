import DarkTower.WarMachine.R20CertifiedExample

/-!
# R20: two clicks that are run-certified

In plain terms: the results of `R20Run` are of the form "in a run whose clicks
are focus-certified and carried, ...". This module builds such a run, two
clicks long, so those results are not about an empty class of runs.

Each click is `R20CertifiedExample`'s click with four rows made to depend on
what the click starts from: its run id, the habit counts it consumes, and the
initial-state counts `d` (Friston et al. 2017, eq. 2.7, :678). `clickAt` states
that click for any such start and `clickAt_focusCertified` certifies it,
including the outer choice (`R20FocusedSelection`): one candidate, the focus
itself, reached with certainty.

* Click 0: run 0, fresh habit counts, `d = (1, 1)`, so the evidence prior is
  `(1/2, 1/2)`. The observation has likelihood `3/4` under state 0 and `1/4`
  under state 1, so the posterior is `(3/4, 1/4)`; policy `a` succeeds.
* Click 1: run 1, the habit counts click 0 handed on, `d = (7/4, 5/4)`, so the
  evidence prior is `(7/12, 5/12)`; E is `(2/3, 1/3)`.

Results: `example_runCertified`; and, by the general theorems,
`example_counts_accumulate` (click 1's `d` is click 0's plus click 0's
posterior, `run_concentration_accumulates`), `example_second_prior` (so the
evidence prior moved to `7/12`), `example_second_E` (click 1's E reads click
0's success, through `selection_E_is_habit`), and `example_focus_kept`
(`run_focus_case`).

Controls, each a second click that is itself focus-certified but not carried,
so the run is refused: habit counts reset (`habitReset_breaks_run`), the d
counts not updated (`countsNotUpdated_breaks_run`), a replayed run id
(`replayedRun_breaks_run`).

Not exercised here (claude-7's review): β never moves, since F is equal
across policies, so the β carry is a constant matching a constant
(`R20Run.posteriorBetaCarried_refused` covers carrying a moved β); the focus
is kept in both clicks, so the `focusChanged` case is not reached; and the
habit row only records a success, so a failure is never carried across a run.

As with `R20CertifiedExample`, this shows the conditions are jointly
satisfiable. No value here comes from a recorded click.
-/

namespace DarkTower.WarMachine.R20RunExample

open DarkTower.WarMachine.R20Graph
open DarkTower.WarMachine.R20Certificate
open DarkTower.WarMachine.R20FocusedSelection
open DarkTower.WarMachine.R20Run
open DarkTower.WarMachine.R15StrategicTarget
open DarkTower.WarMachine.R15TemporalHierarchy
open DarkTower.WarMachine.R15HabitPrior
open DarkTower.WarMachine.R15InjuryTier (relationExample Candidate candidatePrediction candidateValue)
open DarkTower.WarMachine.R20HabitPrior (selection_E_is_habit totalAlpha_menu2)
open DarkTower.WarMachine.R20CertifiedExample
  (gValue riskReal totalG reportedRisk_eq classRow focusedPoint liveRow liveRow_conforms
    independenceRow jointRow jointRow_conforms costRow costRow_conforms)
open PrecisionFromObservation (TwoPolicy)

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## One click, for any start -/

/-! The habit quantities are stated for a general policy type, so they use the
same (classical) decidable equality as `R20Certificate`, whose conditions are
stated for a general policy type. At `TwoPolicy` the derived instance would
otherwise be chosen, and the rows would not be the rows the certificate reads. -/

section
variable {P : Type} [Fintype P]

/-- E: the normalised counts the click starts from. -/
def habitEOf (before : SlowState P) : P → ℝ :=
  fun π => (policyHabitPrior before (menu P) π : ℝ)

/-- The habit row: a witnessed success of `π`, folded into the counts. -/
def habitRowOf (before : SlowState P) (π : P) : TwoTickRecord P :=
  ⟨before, ⟨π, true, true⟩, advance before ⟨π, true, true⟩, advance before ⟨π, true, true⟩⟩

omit [Fintype P] in
theorem habitRowOf_feedback (before : SlowState P) (π : P) :
    TwoTickFeedback (habitRowOf before π) := ⟨rfl, rfl, rfl⟩

omit [Fintype P] in
theorem habitRowOf_moves (before : SlowState P) (π : P) :
    (habitRowOf before π).nextConsumed ≠ before :=
  advance_ne_before before _

end

def habitE (before : SlowState TwoPolicy) : TwoPolicy → ℝ := habitEOf before

/-- Every click's habit row is a success of policy `a`. -/
def habitRow (before : SlowState TwoPolicy) : TwoTickRecord TwoPolicy := habitRowOf before .a

def fConst : ℝ := (exampleF 0).value .a

theorem exampleF_const (run : RunId) : (exampleF run).value = fun _ => fConst := by
  funext π; cases π <;> rfl

/-- The precision row: E from the counts, the full G, F the same for both
policies, so `β` does not move. -/
def precisionRow (run : RunId) (before : SlowState TwoPolicy) :
    PrecisionFromObservation.TickRecord TwoPolicy :=
  { E := habitE before, G := totalG, F := (exampleF run).value
    prior := PrecisionFromObservation.priorPolicy 1 (habitE before) totalG
    posterior := PrecisionFromObservation.posteriorPolicy 1 (habitE before) totalG
      (exampleF run).value
    betaPrior := 1, betaPosterior := 1 }

theorem precisionRow_conforms (run : RunId) (before : SlowState TwoPolicy)
    (positive : ∀ π, 0 < habitE before π) :
    PrecisionFromObservation.Conforms (precisionRow run before) := by
  refine ⟨positive, by norm_num [precisionRow], ?_, rfl, rfl⟩
  · show PrecisionFromObservation.IsPosteriorTemperature 1 1 (habitE before) totalG
      (exampleF run).value
    rw [exampleF_const]
    exact (PrecisionFromObservation.constant_F_posterior_temperature_iff
      (by norm_num) (habitE before) _ fConst).mpr rfl

/-- The observation's likelihood: `3/4` under state 0, `1/4` under state 1. -/
def likelihood : EvidenceFromTheProcess.Likelihood Hidden Observation :=
  fun s o => if o = (s = 0) then 3 / 4 else 1 / 4

/-- The evidence row: the prior is the mean of `Dir(d)`, the posterior is
Bayes on the observation `true`. -/
def evidenceRow (d : Hidden → ℝ) : EvidenceRow :=
  { prior := fun s => d s / ∑ x, d x, likelihood := likelihood, observation := true
    posterior := EvidenceFromTheProcess.posterior (fun s => d s / ∑ x, d x) likelihood true }

/-- Focus 7 at horizon 1, with the focus itself as the only candidate. The
previous focus is 7 as well. -/
def strategicTick : StrategicTickRecord :=
  ⟨7, 1, [receipt 7 7], CTauClassPreference.classPreference 1⟩

def strategicRow : StrategicFocusRow := ⟨7, strategicTick⟩

theorem strategicRow_conforms : StrategicFocusConforms strategicRow := by
  refine ⟨?_, fun _ _ _ => rfl⟩
  intro c hc
  simp only [strategicRow, strategicTick, List.mem_singleton] at hc
  subst hc
  rfl

/-- The outer choice: the focus, reached with certainty. -/
def selection : OuterSelection := ⟨[⟨7, 1⟩], ⟨7, 1⟩⟩

theorem focus_is_focused : outcomeClass 7 relationExample (some 7) = some .focused := by
  decide

theorem selection_conforms : OuterSelectionConforms relationExample strategicTick selection := by
  refine ⟨by simp [selection], ?_, ?_⟩
  · intro c hc
    simp only [selection, List.mem_singleton] at hc
    subst hc
    refine ⟨⟨receipt 7 7, by simp [strategicTick], rfl, rfl⟩, ?_⟩
    simp only [strategicTick, candidateValue]
    rw [focus_is_focused]; rfl
  · intro c hc v w hv hw
    simp only [selection, List.mem_singleton] at hc
    subst hc
    simp only [selection] at hw
    rw [hv] at hw
    cases hw
    exact le_rfl

def records (run : RunId) (before : SlowState TwoPolicy) (d : Hidden → ℝ) :
    Records TwoPolicy
  | .precision => some (precisionRow run before)
  | .evidence => some (evidenceRow d)
  | .habit => some (habitRow before)
  | .classPreference => some classRow
  | .strategicFocus => some strategicRow
  | .liveness => some liveRow
  | .independence => some independenceRow
  | .jointAction => some jointRow
  | .cost => some costRow
  | .interoception => some goodInteroception

def ports (run : RunId) (before : SlowState TwoPolicy) : Ports TwoPolicy :=
  { runId := run
    habitRowE := ⟨habitE before, .node .habit, run⟩
    selectionHabit := ⟨habitE before, .selection, run⟩
    precisionHabit := ⟨habitE before, .selection, run⟩
    selectionG := terminalG run, precisionG := terminalG run
    inferenceF := exampleF run, precisionF := exampleF run
    strategicPreference := ⟨CTauClassPreference.classPreference 1 1, .node .strategicFocus, run⟩
    classPreference := ⟨CTauClassPreference.classPreference 1 1, .node .strategicFocus, run⟩
    selectionPredicted := ⟨focusedPoint, .selection, run⟩
    classPredicted := ⟨focusedPoint, .selection, run⟩
    precisionBeta := ⟨1, .node .precision, run⟩
    interoceptionRisk := ⟨goodInteroception.reportedRisk, .node .interoception, run⟩
    selectionInteroceptionRisk := ⟨goodInteroception.reportedRisk, .node .interoception, run⟩ }

/-- The click that starts from run id `run`, habit counts `before` and
initial-state counts `d`. -/
def clickAt (run : RunId) (before : SlowState TwoPolicy) (d : Hidden → ℝ) : Click TwoPolicy :=
  ⟨records run before d, ports run before, selection, d⟩

theorem clickAt_certified (run : RunId) (before : SlowState TwoPolicy) (d : Hidden → ℝ)
    (positive : ∀ π, 0 < habitE before π) :
    Certified (records run before d) (certify (records run before d)) (ports run before) := by
  refine (certified_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · intro node
    cases node
    · exact ⟨_, rfl, precisionRow_conforms run before positive⟩
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, habitRowOf_feedback before .a⟩
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, strategicRow_conforms⟩
    · exact ⟨_, rfl, liveRow_conforms⟩
    · exact ⟨_, rfl, by simp [conforms, IndependenceConforms, independenceRow]⟩
    · exact ⟨_, rfl, jointRow_conforms⟩
    · exact ⟨_, rfl, costRow_conforms⟩
    · exact ⟨_, rfl, goodInteroception_conforms⟩
  · constructor
    · intro n _; cases n <;> simp [records]
    all_goals rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
      have ticks : (ports run before).selectionG.ticks = 1 := rfl
      have : t.val = 0 := by omega
      simp [ports, terminalG, focusedG, classRow]
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

theorem clickAt_focusCertified (run : RunId) (before : SlowState TwoPolicy) (d : Hidden → ℝ)
    (positive : ∀ π, 0 < habitE before π) :
    FocusCertified relationExample (clickAt run before d).records (clickAt run before d).ports
      (clickAt run before d).selection := by
  refine ⟨clickAt_certified run before d positive, strategicRow, rfl, selection_conforms,
    .focused, focus_is_focused, ?_⟩
  funext e
  simp only [clickAt, ports, selection, focusedPoint, candidatePrediction]
  split_ifs <;> simp_all

theorem clickAt_prior (run : RunId) (before : SlowState TwoPolicy) (d : Hidden → ℝ)
    (pos : ∀ s, 0 < d s) : PriorFromCounts (clickAt run before d) :=
  ⟨pos, fun r hr => by simp only [clickAt, records, Option.some.injEq] at hr; subst hr; rfl⟩

/-! ## The two clicks -/

def d0 : Hidden → ℝ := fun _ => 1

/-- Click 1's counts: click 0's plus click 0's posterior. -/
def d1 : Hidden → ℝ := d0 + (evidenceRow d0).posterior

def before0 : SlowState TwoPolicy := []

/-- The habit counts click 0 hands on: one success of `a`. -/
def before1 : SlowState TwoPolicy := (habitRow before0).nextConsumed

def click0 : Click TwoPolicy := clickAt 0 before0 d0
def click1 : Click TwoPolicy := clickAt 1 before1 d1

/-- The run: click 0, then click 1 from there on. -/
def clicks (second : Click TwoPolicy) : ℕ → Click TwoPolicy
  | 0 => click0
  | _ => second

theorem posterior0 : (evidenceRow d0).posterior = fun s => if s = 0 then 3 / 4 else 1 / 4 := by
  funext s
  simp only [evidenceRow, EvidenceFromTheProcess.posterior, EvidenceFromTheProcess.evidence,
    d0, likelihood, Fin.sum_univ_two]
  fin_cases s <;> norm_num

theorem d1_eq : d1 = fun s => if s = 0 then 7 / 4 else 5 / 4 := by
  funext s
  simp only [d1, d0, Pi.add_apply, posterior0]
  split_ifs <;> norm_num

/-- Fresh counts: E is `1/2` for each policy. -/
theorem habitE0 (π : TwoPolicy) : habitE before0 π = 1 / 2 := by
  simp only [habitE, habitEOf, policyHabitPrior, totalAlpha_menu2]
  simp [policyAlpha, before0, countsFor, freshCounts]
  norm_num

/-- After one success of `a`: E is `(2/3, 1/3)`. -/
theorem habitE1 : habitE before1 = fun | .a => 2 / 3 | .b => 1 / 3 := by
  funext π
  simp only [habitE, habitEOf, policyHabitPrior, totalAlpha_menu2]
  cases π <;> simp [policyAlpha, before1, before0, habitRow, habitRowOf, advance, setCounts,
    countsFor, updatedCounts, freshCounts] <;> norm_num

theorem positive0 (π : TwoPolicy) : 0 < habitE before0 π := by
  rw [habitE0]; norm_num

theorem positive1 (π : TwoPolicy) : 0 < habitE before1 π := by
  rw [habitE1]; cases π <;> norm_num

theorem example_carries : Carries click0 click1 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro ra rb ha hb
    simp only [click0, click1, clickAt, records, Option.some.injEq] at ha hb
    subst ha hb; rfl
  · intro ra ha
    simp only [click0, clickAt, records, Option.some.injEq] at ha
    subst ha; rfl
  · intro ra rb ha hb
    simp only [click0, click1, clickAt, records, Option.some.injEq] at ha hb
    subst ha hb; rfl
  · intro sa sb ha hb
    simp only [click0, click1, clickAt, records, Option.some.injEq] at ha hb
    subst ha hb; rfl

/-- Two clicks, each focus-certified with its prior read from its counts, the
first carried into the second. -/
theorem example_runCertified : RunCertified relationExample (clicks click1) 1 := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact ⟨clickAt_focusCertified 0 before0 d0 positive0,
        clickAt_prior 0 before0 d0 (fun _ => one_pos)⟩
    · refine ⟨clickAt_focusCertified 1 before1 d1 positive1, clickAt_prior 1 before1 d1 ?_⟩
      intro s; rw [d1_eq]; dsimp only; split_ifs <;> norm_num
  · obtain rfl : i = 0 := by omega
    exact example_carries

/-! ## What the general theorems then say about it -/

/-- `run_concentration_accumulates`: click 1's counts are click 0's plus
click 0's posterior. -/
theorem example_counts_accumulate :
    (clicks click1 1).d = d0 + (evidenceRow d0).posterior := by
  have := run_concentration_accumulates example_runCertified
    (fun i => evidenceRow (clicks click1 i).d) (fun i _ => by cases i <;> rfl)
  simpa [clicks, click0, clickAt] using this

/-- So click 1's evidence prior on state 0 is `7/12`, up from `1/2`. -/
theorem example_second_prior : (evidenceRow (clicks click1 1).d).prior 0 = 7 / 12 := by
  rw [example_counts_accumulate, ← d1, d1_eq]
  simp [evidenceRow, Fin.sum_univ_two]
  norm_num

/-- Click 1's E reads click 0's success of `a`: `2/3`, up from `1/2`. -/
theorem example_second_E : (clicks click1 1).ports.selectionHabit.value .a = 2 / 3 := by
  have certified := (clickAt_focusCertified 1 before1 d1 positive1).1
  show (clickAt 1 before1 d1).ports.selectionHabit.value .a = 2 / 3
  exact (selection_E_is_habit certified (h := habitRow before1) rfl .a).trans
    (congrFun habitE1 .a)

/-- `run_focus_case`: click 1 kept click 0's focus. -/
theorem example_focus_kept :
    caseOf (Policy := TwoPolicy) .strategicFocus strategicRow = .strategicFocus .focusKept :=
  (run_focus_case example_runCertified (i := 0) (by omega) strategicRow strategicRow rfl rfl).mpr
    rfl

/-! ## Controls

Each second click is itself focus-certified (`clickAt_focusCertified`); only
the hand-over from click 0 is wrong. -/

/-- Click 1 starts again from fresh habit counts. -/
theorem habitReset_breaks_run :
    ¬ RunCertified relationExample (clicks (clickAt 1 before0 d1)) 1 := by
  intro run
  have := (run.2 0 (by omega)).habit _ _ rfl rfl
  exact habitRowOf_moves before0 .a this.symm

/-- Click 1 starts from click 0's d. -/
theorem countsNotUpdated_breaks_run :
    ¬ RunCertified relationExample (clicks (clickAt 1 before1 d0)) 1 := by
  intro run
  have := congrFun ((run.2 0 (by omega)).counts _ rfl) 0
  have p := congrFun posterior0 0
  simp only [clicks, click0, clickAt, Pi.add_apply] at this p
  simp [d0, p] at this

/-- Click 1 replays click 0's run id. -/
theorem replayedRun_breaks_run :
    ¬ RunCertified relationExample (clicks (clickAt 0 before1 d1)) 1 := by
  intro run
  exact absurd (run.2 0 (by omega)).runAdvances (by decide)

#print axioms example_runCertified
#print axioms example_second_E
#print axioms habitReset_breaks_run

end
end DarkTower.WarMachine.R20RunExample
