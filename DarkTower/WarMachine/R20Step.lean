import DarkTower.WarMachine.R20Run

/-!
# R20 as a computed step function: carried counts

This is slice 1 of the R20 reconstruction.  `step` computes each click and the
state handed to its successor; `run` folds `step` from `init`.  Evidence counts
follow Friston 2017, equation 2.7.  Learned terminal-class preferences follow
the preference-count update described by Smith, Friston & Whyte 2022.

Precision and valence are deliberately absent from `State`; they enter in
slice 2.  `Click` consequently has no outside candidate list, menu, or
selection field.
-/

namespace DarkTower.WarMachine.R20Step

open scoped BigOperators
open R15TemporalHierarchy

abbrev Hidden := R20Certificate.Hidden
abbrev ProcessObservation := R20Certificate.Observation
abbrev EndingClass := CTauClassPreference.EndingClass
abbrev CCounts := CTauClassPreference.Distribution
abbrev PatternIdentity := R20Run.PatternIdentity

variable {Policy : Type} [DecidableEq Policy]

/-- Fixed makeup for one run.  `d₀` is the initial evidence concentration
(Friston 2017, equation 2.7); `κ` is the preference-count strength used by the
Smith, Friston & Whyte 2022 preference update. -/
structure Makeup (Policy : Type) where
  A : EvidenceFromTheProcess.Likelihood Hidden ProcessObservation
  d₀ : Hidden → ℝ
  habit₀ : SlowState Policy
  pattern : PatternIdentity
  theta₀ : SlowState PatternIdentity
  kappa : ℚ
  kappa_pos : 0 < kappa
  initialFocus : Nat

/-- State carried from one click to the next.  `d` is the concentration from
Friston 2017, equation 2.7; `c` is the learned preference concentration from
Smith, Friston & Whyte 2022. -/
structure State (Policy : Type) where
  d : Hidden → ℝ
  habit : SlowState Policy
  theta : SlowState PatternIdentity
  c : CCounts
  previousFocus : Nat
  runId : Nat

/-- Exogenous facts arriving at one click.  Habit and pattern outcomes feed the
existing R15/PatternTheta updates; the ending class feeds the Smith, Friston &
Whyte 2022 preference-count update. -/
structure Observation (Policy : Type) where
  observation : ProcessObservation
  habitOutcome : FastOutcome Policy
  thetaOutcomes : List (FastOutcome PatternIdentity)
  endingClass : EndingClass
  focus : Nat

/-- Rows produced by one computed click.  Evidence uses Friston 2017,
equation 2.7; `C` is the normalized Smith, Friston & Whyte 2022 preference
count. -/
structure Click (Policy : Type) where
  d : Hidden → ℝ
  evidence : R20Certificate.EvidenceRow
  habitBefore : SlowState Policy
  habitAfter : SlowState Policy
  thetaBefore : SlowState PatternIdentity
  thetaAfter : SlowState PatternIdentity
  c : CCounts
  C : CTauClassPreference.Distribution
  previousFocus : Nat
  focus : Nat
  runId : Nat

/-- The 55/35/5/5 prior kit, with no mass on `notYetEvaluated`. -/
def kit : CCounts
  | .focused => 55 / 100
  | .related => 35 / 100
  | .unrelated => 5 / 100
  | .stopTheLine => 5 / 100
  | .notYetEvaluated => 0

/-- Initial learned-preference counts, `κ · (55,35,5,5)/100`, following
Smith, Friston & Whyte 2022. -/
def initialC (m : Makeup Policy) : CCounts := fun ending => m.kappa * kit ending

/-- Add the Smith, Friston & Whyte 2022 unit preference count for a terminal
ending.  `notYetEvaluated` is not a terminal outcome and adds nothing. -/
def addEnding (c : CCounts) (observed : EndingClass) : CCounts := fun ending =>
  c ending + if observed = ending ∧ ending ≠ .notYetEvaluated then 1 else 0

/-- Normalize learned Smith, Friston & Whyte 2022 preference counts. -/
def normalizeC (c : CCounts) : CTauClassPreference.Distribution := fun ending =>
  c ending / CTauClassPreference.totalMass c

/-- A `classPreference`-shaped schedule whose terminal value is learned C. -/
def learnedClassPreference (C : CTauClassPreference.Distribution)
    (horizon tau : Nat) : CTauClassPreference.Distribution :=
  if tau = horizon then C else CTauClassPreference.waitingPreference

/-- Initial carried state.  Evidence concentration follows Friston 2017,
equation 2.7; preference concentration follows Smith, Friston & Whyte 2022. -/
def init (m : Makeup Policy) : State Policy where
  d := m.d₀
  habit := m.habit₀
  theta := m.theta₀
  c := initialC m
  previousFocus := m.initialFocus
  runId := 0

/-- The evidence prior is the mean of the current Friston 2017 equation 2.7
concentration. -/
noncomputable def evidencePrior (s : State Policy) : EvidenceFromTheProcess.Belief Hidden :=
  fun hidden => s.d hidden / ∑ x, s.d x

/-- Compute one click and its successor.  The evidence concentration update is
Friston 2017 equation 2.7; the C-count update is Smith, Friston & Whyte 2022. -/
noncomputable def step (m : Makeup Policy) (s : State Policy) (o : Observation Policy) :
    Click Policy × State Policy :=
  let prior := evidencePrior s
  let posterior := EvidenceFromTheProcess.posterior prior m.A o.observation
  let habitAfter := R15TemporalHierarchy.advance s.habit o.habitOutcome
  let thetaAfter := PatternTheta.advanceWitnessed m.pattern s.theta o.thetaOutcomes
  let cAfter := addEnding s.c o.endingClass
  ({ d := s.d
     evidence := ⟨prior, m.A, o.observation, posterior⟩
     habitBefore := s.habit
     habitAfter := habitAfter
     thetaBefore := s.theta
     thetaAfter := thetaAfter
     c := s.c
     C := normalizeC s.c
     previousFocus := s.previousFocus
     focus := o.focus
     runId := s.runId },
   { d := s.d + posterior
     habit := habitAfter
     theta := thetaAfter
     c := cAfter
     previousFocus := o.focus
     runId := s.runId + 1 })

/-- Fold `step` from a supplied state, returning the computed clicks and final
state.  Its updates are exactly the Friston 2017 and Smith, Friston & Whyte
2022 updates in `step`. -/
noncomputable def runFrom (m : Makeup Policy) : State Policy → List (Observation Policy) →
    List (Click Policy) × State Policy
  | s, [] => ([], s)
  | s, o :: obs =>
      let next := step m s o
      let rest := runFrom m next.2 obs
      (next.1 :: rest.1, rest.2)

/-- Compute a run by folding `step` from `init m` (Friston 2017 equation 2.7;
Smith, Friston & Whyte 2022 preference learning). -/
noncomputable def run (m : Makeup Policy) (obs : List (Observation Policy)) :
    List (Click Policy) := (runFrom m (init m) obs).1

/-- State after a prefix of observations. -/
noncomputable def stateAfter (m : Makeup Policy) (obs : List (Observation Policy)) :
    State Policy := (runFrom m (init m) obs).2

/-- One Smith, Friston & Whyte 2022 preference-count observation. -/
def endingDelta (observed : EndingClass) : CCounts := fun ending =>
  if observed = ending ∧ ending ≠ .notYetEvaluated then 1 else 0

/-- Smith, Friston & Whyte 2022 preference counts contributed by a prefix. -/
def endingCounts : List (Observation Policy) → CCounts
  | [] => 0
  | o :: obs => endingDelta o.endingClass + endingCounts obs

/-- Posteriors generated successively from Friston 2017 equation 2.7 counts. -/
noncomputable def posteriorHistoryFrom (m : Makeup Policy) :
    State Policy → List (Observation Policy) → List (Hidden → ℝ)
  | _, [] => []
  | s, o :: obs =>
      let p := EvidenceFromTheProcess.posterior (evidencePrior s) m.A o.observation
      p :: posteriorHistoryFrom m (step m s o).2 obs

/-- The Friston 2017 equation 2.7 posterior history from `init`. -/
noncomputable def posteriorHistory (m : Makeup Policy) (obs : List (Observation Policy)) :=
  posteriorHistoryFrom m (init m) obs

/-- Pointwise sum used by the Friston 2017 equation 2.7 closed form. -/
def sumBeliefs : List (Hidden → ℝ) → Hidden → ℝ
  | [] => 0
  | p :: ps => p + sumBeliefs ps

theorem addEnding_eq_add (c : CCounts) (ending : EndingClass) :
    addEnding c ending = c + endingDelta ending := by
  rfl

theorem runFrom_append_one (m : Makeup Policy) (s : State Policy)
    (pre : List (Observation Policy)) (o : Observation Policy) :
    (runFrom m s (pre ++ [o])).1 =
      (runFrom m s pre).1 ++ [(step m (runFrom m s pre).2 o).1] := by
  induction pre generalizing s with
  | nil => simp [runFrom]
  | cons x xs ih => simp [runFrom, ih]

theorem stateAfterFrom_c (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.c = obs.foldl (fun c o => addEnding c o.endingClass) s.c := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih => simpa [runFrom, step] using ih (step m s o).2

theorem fold_addEnding (base : CCounts) (obs : List (Observation Policy)) :
    obs.foldl (fun c o => addEnding c o.endingClass) base = base + endingCounts obs := by
  induction obs generalizing base with
  | nil => simp [endingCounts]
  | cons o obs ih =>
      rw [List.foldl_cons, ih]
      simp only [addEnding_eq_add]
      simp only [endingCounts]
      funext ending
      simp [endingDelta]
      ring

theorem stateAfter_c (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).c = initialC m + endingCounts obs := by
  rw [stateAfter, stateAfterFrom_c, fold_addEnding]
  rfl

theorem click_c_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    let click := (step m (stateAfter m pre) o).1
    click.c = initialC m + endingCounts pre ∧ click.C = normalizeC click.c := by
  simp [step, stateAfter_c]

theorem click_zero_C_kit (m : Makeup Policy) (o : Observation Policy) :
    let click := (step m (init m) o).1
    click.c = initialC m ∧ click.C = normalizeC (initialC m) := by
  simp [step, init]

theorem stateAfterFrom_d (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.d = s.d + sumBeliefs (posteriorHistoryFrom m s obs) := by
  induction obs generalizing s with
  | nil => simp [runFrom, posteriorHistoryFrom, sumBeliefs]
  | cons o obs ih =>
      simp only [runFrom]
      rw [ih]
      simp [posteriorHistoryFrom, sumBeliefs, step]
      abel

theorem stateAfter_d (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).d = m.d₀ + sumBeliefs (posteriorHistory m obs) := by
  simpa [stateAfter, posteriorHistory, init] using stateAfterFrom_d m (init m) obs

theorem click_d_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.d =
      m.d₀ + sumBeliefs (posteriorHistory m pre) := by
  simp [step, stateAfter_d]

theorem stateAfterFrom_habit (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.habit =
      obs.foldl (fun habit o => R15TemporalHierarchy.advance habit o.habitOutcome) s.habit := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih => simpa [runFrom, step] using ih (step m s o).2

theorem stateAfter_habit (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).habit =
      obs.foldl (fun habit o => R15TemporalHierarchy.advance habit o.habitOutcome) m.habit₀ := by
  simpa [stateAfter, init] using stateAfterFrom_habit m (init m) obs

theorem click_habit_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.habitBefore =
      pre.foldl (fun habit x => R15TemporalHierarchy.advance habit x.habitOutcome) m.habit₀ := by
  simp [step, stateAfter_habit]

theorem stateAfterFrom_theta (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.theta =
      obs.foldl (fun theta o => PatternTheta.advanceWitnessed m.pattern theta o.thetaOutcomes)
        s.theta := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih => simpa [runFrom, step] using ih (step m s o).2

theorem stateAfter_theta (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).theta =
      obs.foldl (fun theta o => PatternTheta.advanceWitnessed m.pattern theta o.thetaOutcomes)
        m.theta₀ := by
  simpa [stateAfter, init] using stateAfterFrom_theta m (init m) obs

theorem click_theta_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.thetaBefore =
      pre.foldl
        (fun theta x => PatternTheta.advanceWitnessed m.pattern theta x.thetaOutcomes) m.theta₀ := by
  simp [step, stateAfter_theta]

theorem click_evidence_conforms (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy) :
    R20Certificate.EvidenceConforms (step m s o).1.evidence := by
  rfl

theorem run_evidence_conforms (m : Makeup Policy) (obs : List (Observation Policy)) :
    ∀ click ∈ run m obs, R20Certificate.EvidenceConforms click.evidence := by
  intro click present
  unfold run at present
  generalize init m = s at present
  induction obs generalizing s with
  | nil => simp [runFrom] at present
  | cons o obs ih =>
      simp only [runFrom, List.mem_cons] at present
      rcases present with rfl | present
      · exact click_evidence_conforms m s o
      · exact ih (step m s o).2 present

theorem stateAfterFrom_runId (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.runId = s.runId + obs.length := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih =>
      rw [show (runFrom m s (o :: obs)).2 = (runFrom m (step m s o).2 obs).2 by rfl, ih]
      simp [step]
      omega

theorem stateAfter_runId (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).runId = obs.length := by
  simpa [stateAfter, init] using stateAfterFrom_runId m (init m) obs

theorem click_runId_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.runId = pre.length := by
  simp [step, stateAfter_runId]

theorem consecutive_runIds (m : Makeup Policy) (pre : List (Observation Policy))
    (a b : Observation Policy) :
    (step m (stateAfter m pre) a).1.runId <
      (step m (stateAfter m (pre ++ [a])) b).1.runId := by
  simp [click_runId_at]

theorem stateAfterFrom_focus (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.previousFocus =
      obs.foldl (fun _ o => o.focus) s.previousFocus := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih => simpa [runFrom, step] using ih (step m s o).2

theorem click_previousFocus_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.previousFocus =
      pre.foldl (fun _ x => x.focus) m.initialFocus := by
  simp [step, stateAfter, stateAfterFrom_focus, init]

theorem kit_total : CTauClassPreference.totalMass kit = 1 := by
  norm_num [CTauClassPreference.totalMass, kit]

theorem initialC_total (m : Makeup Policy) :
    CTauClassPreference.totalMass (initialC m) = m.kappa := by
  simp [CTauClassPreference.totalMass, initialC, kit]
  ring

theorem normalize_initialC (m : Makeup Policy) : normalizeC (initialC m) = kit := by
  funext ending
  unfold normalizeC
  rw [initialC_total]
  unfold initialC
  field_simp [m.kappa_pos.ne']

theorem click_zero_C_is_kit (m : Makeup Policy) (o : Observation Policy) :
    (step m (init m) o).1.C = kit := by
  simp [step, init, normalize_initialC]

theorem initialC_nonnegative (m : Makeup Policy) :
    CTauClassPreference.Nonnegative (initialC m) := by
  intro ending
  fin_cases ending <;> simp [initialC, kit] <;> nlinarith [m.kappa_pos]

theorem addEnding_nonnegative {c : CCounts} (hc : CTauClassPreference.Nonnegative c)
    (ending : EndingClass) : CTauClassPreference.Nonnegative (addEnding c ending) := by
  intro x
  simp only [addEnding]
  split
  · linarith [hc x]
  · simpa using hc x

theorem fold_addEnding_nonnegative {c : CCounts}
    (hc : CTauClassPreference.Nonnegative c) (obs : List (Observation Policy)) :
    CTauClassPreference.Nonnegative
      (obs.foldl (fun counts o => addEnding counts o.endingClass) c) := by
  induction obs generalizing c with
  | nil => simpa
  | cons o obs ih =>
      simp only [List.foldl_cons]
      exact ih (addEnding_nonnegative hc _)

theorem stateAfter_c_nonnegative (m : Makeup Policy) (obs : List (Observation Policy)) :
    CTauClassPreference.Nonnegative (stateAfter m obs).c := by
  unfold stateAfter
  rw [stateAfterFrom_c]
  exact fold_addEnding_nonnegative (initialC_nonnegative m) obs

theorem addEnding_total (c : CCounts) (ending : EndingClass) :
    CTauClassPreference.totalMass (addEnding c ending) =
      CTauClassPreference.totalMass c + if ending = .notYetEvaluated then 0 else 1 := by
  fin_cases ending <;> simp [CTauClassPreference.totalMass, addEnding] <;> ring

theorem fold_addEnding_total_positive {c : CCounts}
    (hc : 0 < CTauClassPreference.totalMass c) (obs : List (Observation Policy)) :
    0 < CTauClassPreference.totalMass
      (obs.foldl (fun counts o => addEnding counts o.endingClass) c) := by
  induction obs generalizing c with
  | nil => simpa
  | cons o obs ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [addEnding_total]
      split <;> linarith

theorem stateAfter_c_total_positive (m : Makeup Policy) (obs : List (Observation Policy)) :
    0 < CTauClassPreference.totalMass (stateAfter m obs).c := by
  unfold stateAfter
  rw [stateAfterFrom_c]
  apply fold_addEnding_total_positive
  simpa [init, initialC_total] using m.kappa_pos

theorem normalizeC_probability {c : CCounts}
    (nonnegative : CTauClassPreference.Nonnegative c)
    (positive : 0 < CTauClassPreference.totalMass c) :
    CTauClassPreference.ProbabilityDistribution (normalizeC c) := by
  constructor
  · intro ending
    exact div_nonneg (nonnegative ending) positive.le
  · unfold CTauClassPreference.totalMass normalizeC
    rw [show c .focused / CTauClassPreference.totalMass c +
        c .related / CTauClassPreference.totalMass c +
        c .unrelated / CTauClassPreference.totalMass c +
        c .stopTheLine / CTauClassPreference.totalMass c +
        c .notYetEvaluated / CTauClassPreference.totalMass c =
        CTauClassPreference.totalMass c / CTauClassPreference.totalMass c by
          unfold CTauClassPreference.totalMass
          ring]
    exact div_self positive.ne'

theorem click_C_probability (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    CTauClassPreference.ProbabilityDistribution (step m (stateAfter m pre) o).1.C := by
  simp only [step]
  exact normalizeC_probability (stateAfter_c_nonnegative m pre)
    (stateAfter_c_total_positive m pre)

/-! A concrete two-click preference update. -/

/-- Concrete makeup for the Friston 2017 / Smith, Friston & Whyte 2022 example. -/
def exampleMakeup : Makeup Unit where
  A := fun _ _ => 1
  d₀ := fun _ => 1
  habit₀ := []
  pattern := ⟨"pattern/example"⟩
  theta₀ := []
  kappa := 100
  kappa_pos := by norm_num
  initialFocus := 7

/-- One R15 outcome used in the sourced-update example. -/
def exampleOutcome : FastOutcome Unit := ⟨(), true, true⟩

/-- One observation for the Friston 2017 / Smith, Friston & Whyte 2022 example. -/
def exampleObservation (ending : EndingClass) (focus : Nat) : Observation Unit where
  observation := true
  habitOutcome := exampleOutcome
  thetaOutcomes := []
  endingClass := ending
  focus := focus

example :
    let clicks := run exampleMakeup
      [exampleObservation .focused 8, exampleObservation .related 9]
    clicks.map (fun click => click.c .focused) = [55, 56] := by
  have h : CTauClassPreference.EndingClass.focused ≠ .notYetEvaluated := by decide
  norm_num [run, runFrom, step, init, initialC, kit, normalizeC,
    evidencePrior, EvidenceFromTheProcess.posterior, EvidenceFromTheProcess.evidence,
    exampleMakeup, exampleObservation, exampleOutcome, addEnding,
    R15TemporalHierarchy.advance, PatternTheta.advanceWitnessed, h]

#print axioms click_c_at
#print axioms stateAfter_d
#print axioms click_evidence_conforms

end DarkTower.WarMachine.R20Step
