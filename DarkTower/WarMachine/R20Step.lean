import DarkTower.WarMachine.R20Run

/-!
# R20 as a computed step function: carried counts

This module contains slices 1 and 2 of the R20 reconstruction.  `step` computes each click and the
state handed to its successor; `run` folds `step` from `init`.  Evidence counts
follow Friston 2017, equation 2.7.  Learned terminal-class preferences follow
the preference-count update described by Smith, Friston & Whyte 2022.

Precision follows Friston 2017 equation 2.7's fixed-count numerical iteration;
valence follows the update cited by `R20Run` from Hesp et al. 2021, pp. 286–288.
`Click` has no outside candidate list, menu, or selection field.
-/

namespace DarkTower.WarMachine.R20Step

open scoped BigOperators
open R15TemporalHierarchy

abbrev Hidden := R20Certificate.Hidden
abbrev ProcessObservation := R20Certificate.Observation
abbrev EndingClass := CTauClassPreference.EndingClass
abbrev CCounts := CTauClassPreference.Distribution
abbrev PatternIdentity := R20Run.PatternIdentity
abbrev Valence := R20Run.Valence

variable {Policy : Type} [DecidableEq Policy] [Fintype Policy] [Nonempty Policy]

/-- Total rational Beta counts.  Totality makes Smith, Friston & Whyte 2022
§4 Eqs. 34 and 37 forgetting reach keys absent from a finite slow-state list. -/
abbrev RatedCounts (Key : Type) := Key → ℚ × ℚ

/-- Embed the existing integer R15 prior kit into total rational counts. -/
def ofSlowState {Key : Type} [DecidableEq Key]
    (s : R15TemporalHierarchy.SlowState Key) : RatedCounts Key := fun key =>
  ((R15TemporalHierarchy.countsFor s key).alpha,
   (R15TemporalHierarchy.countsFor s key).beta)

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
  /-- Evidence learning rate η_d; Smith, Friston & Whyte 2022 §4 Eq. 34. -/
  etaD : ℝ
  etaD_pos : 0 < etaD
  /-- Evidence forgetting rate ω_d; Smith, Friston & Whyte 2022 §4 Eq. 34. -/
  omegaD : ℝ
  omegaD_pos : 0 < omegaD
  omegaD_le_one : omegaD ≤ 1
  /-- Preference learning rate η_c; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  etaC : ℚ
  etaC_pos : 0 < etaC
  /-- Preference forgetting rate ω_c; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  omegaC : ℚ
  omegaC_pos : 0 < omegaC
  omegaC_le_one : omegaC ≤ 1
  /-- Habit learning rate η_h; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  etaHabit : ℚ
  etaHabit_pos : 0 < etaHabit
  /-- Habit forgetting rate ω_h; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  omegaHabit : ℚ
  omegaHabit_pos : 0 < omegaHabit
  omegaHabit_le_one : omegaHabit ≤ 1
  /-- Pattern learning rate η_θ; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  etaTheta : ℚ
  etaTheta_pos : 0 < etaTheta
  /-- Pattern forgetting rate ω_θ; Smith, Friston & Whyte 2022 §4 Eq. 37. -/
  omegaTheta : ℚ
  omegaTheta_pos : 0 < omegaTheta
  omegaTheta_le_one : omegaTheta ≤ 1
  /-- Affective level used by the Hesp et al. 2021, pp. 286–288 valence update. -/
  L : R20Run.AffectiveLevel
  /-- Initial valence belief for the Hesp et al. 2021, pp. 286–288 update. -/
  q₀ : Valence → ℝ
  /-- Fixed numerical iteration count for Friston 2017 equation 2.7. -/
  precisionIterations : ℕ
  initialFocus : Nat

/-- State carried from one click to the next.  `d` is the concentration from
Friston 2017, equation 2.7; `c` is the learned preference concentration from
Smith, Friston & Whyte 2022. -/
structure State (Policy : Type) where
  d : Hidden → ℝ
  habit : RatedCounts Policy
  theta : RatedCounts PatternIdentity
  c : CCounts
  valence : Valence → ℝ
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
  /-- Habit evidence supplied externally in this slice; deriving it from learned habit is later work. -/
  E : Policy → ℝ
  /-- Expected free energy supplied externally in this slice; model computation is later work. -/
  G : Policy → ℝ
  /-- Free energy supplied externally in this slice; model computation is later work. -/
  F : Policy → ℝ

/-- Rows produced by one computed click.  Evidence uses Friston 2017,
equation 2.7; `C` is the normalized Smith, Friston & Whyte 2022 preference
count. -/
structure Click (Policy : Type) where
  d : Hidden → ℝ
  evidence : R20Certificate.EvidenceRow
  habitBefore : RatedCounts Policy
  habitAfter : RatedCounts Policy
  thetaBefore : RatedCounts PatternIdentity
  thetaAfter : RatedCounts PatternIdentity
  c : CCounts
  C : CTauClassPreference.Distribution
  precision : PrecisionFromObservation.TickRecord Policy
  valence : Valence → ℝ
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

/-- One Smith, Friston & Whyte 2022 preference-count observation. -/
def endingDelta (observed : EndingClass) : CCounts := fun ending =>
  if observed = ending ∧ ending ≠ .notYetEvaluated then 1 else 0

/-- Normalize learned Smith, Friston & Whyte 2022 preference counts. -/
def normalizeC (c : CCounts) : CTauClassPreference.Distribution := fun ending =>
  c ending / CTauClassPreference.totalMass c

/-- A `classPreference`-shaped schedule whose terminal value is learned C. -/
def learnedClassPreference (C : CTauClassPreference.Distribution)
    (horizon tau : Nat) : CTauClassPreference.Distribution :=
  if tau = horizon then C else CTauClassPreference.waitingPreference

/-- Fixed-count numerical iteration of Friston 2017 equation 2.7, matching
SPM's bounded routine without claiming convergence. -/
noncomputable def iteratePrecision (iterations : ℕ) (betaPrior : ℝ) (E G F : Policy → ℝ) : ℝ :=
  (fun beta => PrecisionFromObservation.firstIterate betaPrior beta E G F)^[iterations]
    betaPrior

/-- Decay every total Beta count by ω once.  The rate is the forgetting rate
of Smith, Friston & Whyte 2022 §4 Eqs. 34 and 37. -/
def decayRated {Key : Type} (omega : ℚ) (counts : RatedCounts Key) : RatedCounts Key :=
  fun key => (omega * (counts key).1, omega * (counts key).2)

/-- Add η to one total Beta count after decay.  η is the learning rate of
Smith, Friston & Whyte 2022 §4 Eqs. 34 and 37. -/
def addRated {Key : Type} [DecidableEq Key] (eta : ℚ) (counts : RatedCounts Key)
    (key : Key) (succeeded : Bool) : RatedCounts Key := fun query =>
  if query = key then
    if succeeded then ((counts query).1 + eta, (counts query).2)
    else ((counts query).1, (counts query).2 + eta)
  else counts query

/-- Habit update with explicit Smith, Friston & Whyte 2022 §4 Eqs. 34 and 37
learning η and forgetting ω: decay all policies, then count the observation. -/
def advanceRated {Key : Type} [DecidableEq Key] (eta omega : ℚ)
    (before : RatedCounts Key) (outcome : FastOutcome Key) : RatedCounts Key :=
  addRated eta (decayRated omega before) outcome.policy outcome.succeeded

/-- Pattern update with explicit Smith, Friston & Whyte 2022 §4 Eqs. 34 and 37
rates: decay all keys once, then add η for each witnessed matching outcome in
the same order as `PatternTheta.advanceWitnessed`. -/
def advanceWitnessedRated (eta omega : ℚ) (pattern : PatternIdentity)
    (before : RatedCounts PatternIdentity) (outcomes : List (FastOutcome PatternIdentity)) :
    RatedCounts PatternIdentity :=
  (PatternTheta.witnessedOutcomes pattern outcomes).foldl
    (fun counts succeeded => addRated eta counts pattern succeeded)
    (decayRated omega before)

/-- Preference update with explicit Smith, Friston & Whyte 2022 §4 Eqs. 34
and 37 learning η and forgetting ω. -/
def advanceC (eta omega : ℚ) (before : CCounts) (ending : EndingClass) : CCounts :=
  omega • before + eta • endingDelta ending

/-- Initial carried state.  Evidence concentration follows Friston 2017,
equation 2.7; preference concentration follows Smith, Friston & Whyte 2022. -/
def init (m : Makeup Policy) : State Policy where
  d := m.d₀
  habit := ofSlowState m.habit₀
  theta := ofSlowState m.theta₀
  c := initialC m
  valence := m.q₀
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
  let habitAfter := advanceRated m.etaHabit m.omegaHabit s.habit o.habitOutcome
  let thetaAfter := advanceWitnessedRated m.etaTheta m.omegaTheta m.pattern s.theta o.thetaOutcomes
  let cAfter := advanceC m.etaC m.omegaC s.c o.endingClass
  let betaPrior := R20Run.descend m.L s.valence
  let betaPosterior := iteratePrecision m.precisionIterations betaPrior o.E o.G o.F
  let precision : PrecisionFromObservation.TickRecord Policy :=
    { E := o.E, G := o.G, F := o.F
      prior := PrecisionFromObservation.priorPolicy betaPosterior o.E o.G
      posterior := PrecisionFromObservation.posteriorPolicy betaPosterior o.E o.G o.F
      betaPrior := betaPrior, betaPosterior := betaPosterior }
  let valenceAfter := R20Run.predict m.L
    (R20Run.valenceUpdate m.L s.valence betaPrior betaPosterior)
  ({ d := s.d
     evidence := ⟨prior, m.A, o.observation, posterior⟩
     habitBefore := s.habit
     habitAfter := habitAfter
     thetaBefore := s.theta
     thetaAfter := thetaAfter
     c := s.c
     C := normalizeC s.c
     precision := precision
     valence := s.valence
     previousFocus := s.previousFocus
     focus := o.focus
     runId := s.runId },
   { d := m.omegaD • s.d + m.etaD • posterior
     habit := habitAfter
     theta := thetaAfter
     c := cAfter
     valence := valenceAfter
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

omit [Nonempty Policy] in
theorem posteriorHistoryFrom_length (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (posteriorHistoryFrom m s obs).length = obs.length := by
  induction obs generalizing s with
  | nil => rfl
  | cons o obs ih => simp [posteriorHistoryFrom, ih]

theorem addEnding_eq_add (c : CCounts) (ending : EndingClass) :
    addEnding c ending = c + endingDelta ending := by
  rfl

omit [Nonempty Policy] in
theorem runFrom_append_one (m : Makeup Policy) (s : State Policy)
    (pre : List (Observation Policy)) (o : Observation Policy) :
    (runFrom m s (pre ++ [o])).1 =
      (runFrom m s pre).1 ++ [(step m (runFrom m s pre).2 o).1] := by
  induction pre generalizing s with
  | nil => simp [runFrom]
  | cons x xs ih => simp [runFrom, ih]

/-- The power-weighted Smith, Friston & Whyte 2022 ending increments. -/
def geometricEndings (omega : ℚ) : List (Observation Policy) → CCounts
  | [] => 0
  | o :: obs => omega ^ obs.length • endingDelta o.endingClass + geometricEndings omega obs

/-- The power-weighted Friston 2017 equation 2.7 posterior increments. -/
def geometricBeliefs (omega : ℝ) : List (Hidden → ℝ) → Hidden → ℝ
  | [] => 0
  | p :: ps => omega ^ ps.length • p + geometricBeliefs omega ps

omit [Nonempty Policy] in
theorem stateAfterFrom_c (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.c =
      m.omegaC ^ obs.length • s.c + m.etaC • geometricEndings m.omegaC obs := by
  induction obs generalizing s with
  | nil => simp [runFrom, geometricEndings]
  | cons o obs ih =>
      rw [show (runFrom m s (o :: obs)).2 = (runFrom m (step m s o).2 obs).2 by rfl, ih]
      simp only [step, geometricEndings, List.length_cons, pow_succ]
      funext ending
      simp [advanceC]
      ring

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
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

omit [Nonempty Policy] in
theorem stateAfter_c (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).c =
      m.omegaC ^ obs.length • initialC m + m.etaC • geometricEndings m.omegaC obs := by
  simpa [stateAfter, init] using stateAfterFrom_c m (init m) obs

omit [Nonempty Policy] in
theorem click_c_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    let click := (step m (stateAfter m pre) o).1
    click.c = m.omegaC ^ pre.length • initialC m +
        m.etaC • geometricEndings m.omegaC pre ∧
      click.C = normalizeC click.c := by
  simp [step, stateAfter_c]

omit [Nonempty Policy] in
theorem click_zero_C_kit (m : Makeup Policy) (o : Observation Policy) :
    let click := (step m (init m) o).1
    click.c = initialC m ∧ click.C = normalizeC (initialC m) := by
  simp [step, init]

omit [Nonempty Policy] in
theorem stateAfterFrom_d (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.d = m.omegaD ^ obs.length • s.d +
      m.etaD • geometricBeliefs m.omegaD (posteriorHistoryFrom m s obs) := by
  induction obs generalizing s with
  | nil => simp [runFrom, posteriorHistoryFrom, geometricBeliefs]
  | cons o obs ih =>
      rw [show (runFrom m s (o :: obs)).2 = (runFrom m (step m s o).2 obs).2 by rfl, ih]
      simp only [posteriorHistoryFrom, geometricBeliefs, List.length_cons, step, pow_succ]
      funext hidden
      simp [posteriorHistoryFrom_length]
      ring

omit [Nonempty Policy] in
theorem stateAfter_d (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).d = m.omegaD ^ obs.length • m.d₀ +
      m.etaD • geometricBeliefs m.omegaD (posteriorHistory m obs) := by
  simpa [stateAfter, posteriorHistory, init] using stateAfterFrom_d m (init m) obs

omit [Nonempty Policy] in
theorem click_d_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.d =
      m.omegaD ^ pre.length • m.d₀ +
        m.etaD • geometricBeliefs m.omegaD (posteriorHistory m pre) := by
  simp [step, stateAfter_d]

omit [Nonempty Policy] in
theorem stateAfterFrom_habit (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.habit =
      obs.foldl (fun habit o => advanceRated m.etaHabit m.omegaHabit habit o.habitOutcome)
        s.habit := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih => simpa [runFrom, step] using ih (step m s o).2

omit [Nonempty Policy] in
theorem stateAfter_habit (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).habit =
      obs.foldl (fun habit o => advanceRated m.etaHabit m.omegaHabit habit o.habitOutcome)
        (ofSlowState m.habit₀) := by
  simpa [stateAfter, init] using stateAfterFrom_habit m (init m) obs

omit [Nonempty Policy] in
theorem click_habit_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.habitBefore =
      pre.foldl (fun habit x => advanceRated m.etaHabit m.omegaHabit habit x.habitOutcome)
        (ofSlowState m.habit₀) := by
  simp [step, stateAfter_habit]

omit [Nonempty Policy] in
theorem stateAfterFrom_theta (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.theta =
      obs.foldl (fun theta o => advanceWitnessedRated m.etaTheta m.omegaTheta
        m.pattern theta o.thetaOutcomes)
        s.theta := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih => simpa [runFrom, step] using ih (step m s o).2

omit [Nonempty Policy] in
theorem stateAfter_theta (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).theta =
      obs.foldl (fun theta o => advanceWitnessedRated m.etaTheta m.omegaTheta
        m.pattern theta o.thetaOutcomes) (ofSlowState m.theta₀) := by
  simpa [stateAfter, init] using stateAfterFrom_theta m (init m) obs

omit [Nonempty Policy] in
theorem click_theta_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.thetaBefore =
      pre.foldl
        (fun theta x => advanceWitnessedRated m.etaTheta m.omegaTheta
          m.pattern theta x.thetaOutcomes) (ofSlowState m.theta₀) := by
  simp [step, stateAfter_theta]

/-- With η = ω = 1, the rated habit update is exactly the existing R15 update. -/
theorem advanceRated_one {Key : Type} [DecidableEq Key]
    (s : SlowState Key) (o : FastOutcome Key) :
    advanceRated 1 1 (ofSlowState s) o = ofSlowState (R15TemporalHierarchy.advance s o) := by
  funext query
  by_cases h : query = o.policy
  · subst query
    simp [advanceRated, decayRated, addRated, ofSlowState, R15TemporalHierarchy.advance,
      R15TemporalHierarchy.countsFor_setCounts_same, R15TemporalHierarchy.updatedCounts]
    split <;> simp
  · simp [advanceRated, decayRated, addRated, ofSlowState, R15TemporalHierarchy.advance, h,
      R15TemporalHierarchy.countsFor_setCounts_other _ _ _ _ h]

theorem decayRated_one {Key : Type} (counts : RatedCounts Key) :
    decayRated 1 counts = counts := by
  funext key
  simp [decayRated]

theorem fold_addRated_one_ofSlowState {Key : Type} [DecidableEq Key]
    (key : Key) (s : SlowState Key) (xs : List Bool) :
    xs.foldl (fun counts succeeded => addRated 1 counts key succeeded) (ofSlowState s) =
      ofSlowState (PatternTheta.foldFires key s xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons succeeded xs ih =>
      rw [List.foldl_cons]
      have one_step :
          addRated 1 (ofSlowState s) key succeeded =
            ofSlowState (R15TemporalHierarchy.advance s ⟨key, true, succeeded⟩) := by
        simpa [advanceRated, decayRated_one] using
          advanceRated_one s (⟨key, true, succeeded⟩ : FastOutcome Key)
      rw [one_step, ih]
      rfl

/-- With η = ω = 1, the rated witnessed-pattern update is exactly PatternTheta's update. -/
theorem advanceWitnessedRated_one (pattern : PatternIdentity)
    (s : SlowState PatternIdentity) (outcomes : List (FastOutcome PatternIdentity)) :
    advanceWitnessedRated 1 1 pattern (ofSlowState s) outcomes =
      ofSlowState (PatternTheta.advanceWitnessed pattern s outcomes) := by
  rw [advanceWitnessedRated, decayRated_one]
  simp [PatternTheta.advanceWitnessed,
    fold_addRated_one_ofSlowState]

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem geometricEndings_one (obs : List (Observation Policy)) :
    geometricEndings 1 obs = endingCounts obs := by
  induction obs with
  | nil => rfl
  | cons o obs ih => simp [geometricEndings, endingCounts, ih]

omit [DecidableEq Policy] in
theorem geometricBeliefs_one (ps : List (Hidden → ℝ)) :
    geometricBeliefs 1 ps = sumBeliefs ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [geometricBeliefs, sumBeliefs, ih]

omit [Nonempty Policy] in
theorem stateAfter_c_unit_rates (m : Makeup Policy) (obs : List (Observation Policy))
    (heta : m.etaC = 1) (homega : m.omegaC = 1) :
    (stateAfter m obs).c = initialC m + endingCounts obs := by
  rw [stateAfter_c, heta, homega, geometricEndings_one]
  simp

omit [Nonempty Policy] in
theorem stateAfter_d_unit_rates (m : Makeup Policy) (obs : List (Observation Policy))
    (heta : m.etaD = 1) (homega : m.omegaD = 1) :
    (stateAfter m obs).d = m.d₀ + sumBeliefs (posteriorHistory m obs) := by
  rw [stateAfter_d, heta, homega, geometricBeliefs_one]
  simp

omit [Nonempty Policy] in
/-- The next click's Friston 2017 equation 2.7 prior is computed from this
click's Hesp et al. 2021, pp. 286–288 valence transition. -/
theorem step_betaPrior_next (m : Makeup Policy) (s : State Policy)
    (o next : Observation Policy) :
    (step m (step m s o).2 next).1.precision.betaPrior =
      R20Run.descend m.L
        (R20Run.predict m.L (R20Run.valenceUpdate m.L s.valence
          (step m s o).1.precision.betaPrior (step m s o).1.precision.betaPosterior)) := by
  rfl

omit [Nonempty Policy] in
/-- Zero affective charge leaves only the Hesp et al. 2021, pp. 286–288
prediction step in the next valence. -/
theorem step_zero_charge_keeps_valence (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy)
    (same : (step m s o).1.precision.betaPosterior = (step m s o).1.precision.betaPrior)
    (nonzero : (step m s o).1.precision.betaPrior ≠ 0)
    (rates : ∀ k, m.L.rate k ≠ 0) (normal : ∑ k, s.valence k = 1) :
    (step m s o).2.valence = R20Run.predict m.L s.valence := by
  simp only [step] at same nonzero ⊢
  rw [same, R20Run.zero_charge_keeps_valence m.L s.valence nonzero rates normal]

omit [Nonempty Policy] in
theorem runFrom_append_one_state (m : Makeup Policy) (s : State Policy)
    (pre : List (Observation Policy)) (o : Observation Policy) :
    (runFrom m s (pre ++ [o])).2 = (step m (runFrom m s pre).2 o).2 := by
  induction pre generalizing s with
  | nil => rfl
  | cons x xs ih => simpa [runFrom] using ih (step m s x).2

omit [Nonempty Policy] in
/-- Under flat affective rates and stochastic transitions, every computed
Friston 2017 equation 2.7 prior remains the flat rate.  `nondeg` is needed
because `valenceUpdate` normalizes by that weighted evidence sum. -/
theorem click_betaPrior_constant_of_flat (m : Makeup Policy) {r : ℝ}
    (flat : ∀ k, m.L.rate k = r)
    (stoch : ∀ j, ∑ k, m.L.B k j = 1)
    (start : ∑ k, m.q₀ k = 1)
    (nondeg : ∀ (pre : List (Observation Policy)) (o : Observation Policy),
      ∑ k, (stateAfter m pre).valence k *
        R20Run.affectiveEvidence m.L
          (step m (stateAfter m pre) o).1.precision.betaPrior
          (step m (stateAfter m pre) o).1.precision.betaPosterior k ≠ 0)
    (pre : List (Observation Policy)) (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.precision.betaPrior = r := by
  have total : ∀ xs : List (Observation Policy), ∑ k, (stateAfter m xs).valence k = 1 := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil => simpa only [stateAfter, runFrom, init] using start
    | append_singleton x xs ih =>
        rw [stateAfter, runFrom_append_one_state]
        simp only [step]
        rw [R20Run.predict_sum m.L stoch]
        apply R20Run.normalize_sum
        simpa [stateAfter, R20Run.valenceUpdate, step] using nondeg x xs
  simp only [step]
  exact R20Run.descend_flat m.L flat (total pre)

omit [DecidableEq Policy] in
theorem firstIterate_constant_F (betaPrior beta : ℝ) (E G : Policy → ℝ) (c : ℝ) :
    PrecisionFromObservation.firstIterate betaPrior beta E G (fun _ => c) = betaPrior := by
  unfold PrecisionFromObservation.firstIterate PrecisionFromObservation.expectedGChange
  rw [PrecisionFromObservation.posterior_eq_prior_of_constant_F]
  simp

omit [DecidableEq Policy] in
/-- Constant F is the exact fixed point of every bounded Friston 2017
equation 2.7 iteration count. -/
theorem iteratePrecision_constant_F (iterations : ℕ) (betaPrior : ℝ)
    (E G : Policy → ℝ) (c : ℝ) :
    iteratePrecision iterations betaPrior E G (fun _ => c) = betaPrior := by
  induction iterations with
  | zero => rfl
  | succ n ih =>
      rw [iteratePrecision, Function.iterate_succ_apply']
      exact firstIterate_constant_F betaPrior _ E G c

theorem step_constant_F (m : Makeup Policy) (s : State Policy) (o : Observation Policy)
    (c : ℝ) (constant : o.F = fun _ => c) :
    (step m s o).1.precision.betaPosterior = (step m s o).1.precision.betaPrior := by
  simp [step, constant, iteratePrecision_constant_F]

omit [Nonempty Policy] in
/-- Once the bounded iterate is a positive fixed point, the computed precision
row satisfies `IsPosteriorTemperature`; no general convergence is claimed. -/
theorem step_precision_conforms_at_fixed_point (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy)
    (fixed : PrecisionFromObservation.firstIterate
      (step m s o).1.precision.betaPrior (step m s o).1.precision.betaPosterior
      o.E o.G o.F = (step m s o).1.precision.betaPosterior)
    (positive : 0 < (step m s o).1.precision.betaPosterior) :
    PrecisionFromObservation.IsPosteriorTemperature
      (step m s o).1.precision.betaPrior (step m s o).1.precision.betaPosterior
      o.E o.G o.F := by
  refine ⟨positive, ?_⟩
  unfold PrecisionFromObservation.firstIterate at fixed
  unfold PrecisionFromObservation.precisionError
  linarith

omit [Nonempty Policy] in
theorem click_evidence_conforms (m : Makeup Policy) (s : State Policy)
    (o : Observation Policy) :
    R20Certificate.EvidenceConforms (step m s o).1.evidence := by
  rfl

omit [Nonempty Policy] in
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

omit [Nonempty Policy] in
theorem stateAfterFrom_runId (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.runId = s.runId + obs.length := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih =>
      rw [show (runFrom m s (o :: obs)).2 = (runFrom m (step m s o).2 obs).2 by rfl, ih]
      simp [step]
      omega

omit [Nonempty Policy] in
theorem stateAfter_runId (m : Makeup Policy) (obs : List (Observation Policy)) :
    (stateAfter m obs).runId = obs.length := by
  simpa [stateAfter, init] using stateAfterFrom_runId m (init m) obs

omit [Nonempty Policy] in
theorem click_runId_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.runId = pre.length := by
  simp [step, stateAfter_runId]

omit [Nonempty Policy] in
theorem consecutive_runIds (m : Makeup Policy) (pre : List (Observation Policy))
    (a b : Observation Policy) :
    (step m (stateAfter m pre) a).1.runId <
      (step m (stateAfter m (pre ++ [a])) b).1.runId := by
  simp [click_runId_at]

omit [Nonempty Policy] in
theorem stateAfterFrom_focus (m : Makeup Policy) (s : State Policy)
    (obs : List (Observation Policy)) :
    (runFrom m s obs).2.previousFocus =
      obs.foldl (fun _ o => o.focus) s.previousFocus := by
  induction obs generalizing s with
  | nil => simp [runFrom]
  | cons o obs ih => simpa [runFrom, step] using ih (step m s o).2

omit [Nonempty Policy] in
theorem click_previousFocus_at (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    (step m (stateAfter m pre) o).1.previousFocus =
      pre.foldl (fun _ x => x.focus) m.initialFocus := by
  simp [step, stateAfter, stateAfterFrom_focus, init]

theorem kit_total : CTauClassPreference.totalMass kit = 1 := by
  norm_num [CTauClassPreference.totalMass, kit]

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem initialC_total (m : Makeup Policy) :
    CTauClassPreference.totalMass (initialC m) = m.kappa := by
  simp [CTauClassPreference.totalMass, initialC, kit]
  ring

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem normalize_initialC (m : Makeup Policy) : normalizeC (initialC m) = kit := by
  funext ending
  unfold normalizeC
  rw [initialC_total]
  unfold initialC
  field_simp [m.kappa_pos.ne']

omit [Nonempty Policy] in
theorem click_zero_C_is_kit (m : Makeup Policy) (o : Observation Policy) :
    (step m (init m) o).1.C = kit := by
  simp [step, init, normalize_initialC]

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
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

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
theorem fold_addEnding_nonnegative {c : CCounts}
    (hc : CTauClassPreference.Nonnegative c) (obs : List (Observation Policy)) :
    CTauClassPreference.Nonnegative
      (obs.foldl (fun counts o => addEnding counts o.endingClass) c) := by
  induction obs generalizing c with
  | nil => simpa
  | cons o obs ih =>
      simp only [List.foldl_cons]
      exact ih (addEnding_nonnegative hc _)

theorem advanceC_nonnegative {c : CCounts} (hc : CTauClassPreference.Nonnegative c)
    (eta omega : ℚ) (heta : 0 ≤ eta) (homega : 0 ≤ omega) (ending : EndingClass) :
    CTauClassPreference.Nonnegative (advanceC eta omega c ending) := by
  intro x
  simp only [advanceC, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hdelta : 0 ≤ endingDelta ending x := by
    by_cases h : ending = x ∧ x ≠ .notYetEvaluated <;> simp [endingDelta, h]
  nlinarith [hc x]

omit [Nonempty Policy] in
theorem runFrom_c_nonnegative (m : Makeup Policy) (s : State Policy)
    (hs : CTauClassPreference.Nonnegative s.c) (obs : List (Observation Policy)) :
    CTauClassPreference.Nonnegative (runFrom m s obs).2.c := by
  induction obs generalizing s with
  | nil => simpa [runFrom]
  | cons o obs ih =>
      apply ih
      simpa [step] using advanceC_nonnegative hs m.etaC m.omegaC
        m.etaC_pos.le m.omegaC_pos.le o.endingClass

omit [Nonempty Policy] in
theorem stateAfter_c_nonnegative (m : Makeup Policy) (obs : List (Observation Policy)) :
    CTauClassPreference.Nonnegative (stateAfter m obs).c := by
  exact runFrom_c_nonnegative m (init m) (by simpa [init] using initialC_nonnegative m) obs

theorem addEnding_total (c : CCounts) (ending : EndingClass) :
    CTauClassPreference.totalMass (addEnding c ending) =
      CTauClassPreference.totalMass c + if ending = .notYetEvaluated then 0 else 1 := by
  fin_cases ending <;> simp [CTauClassPreference.totalMass, addEnding] <;> ring

theorem advanceC_total (eta omega : ℚ) (c : CCounts) (ending : EndingClass) :
    CTauClassPreference.totalMass (advanceC eta omega c ending) =
      omega * CTauClassPreference.totalMass c +
        eta * if ending = .notYetEvaluated then 0 else 1 := by
  fin_cases ending <;> simp [CTauClassPreference.totalMass, advanceC, endingDelta] <;> ring

omit [DecidableEq Policy] [Fintype Policy] [Nonempty Policy] in
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

omit [Nonempty Policy] in
theorem stateAfter_c_total_positive (m : Makeup Policy) (obs : List (Observation Policy)) :
    0 < CTauClassPreference.totalMass (stateAfter m obs).c := by
  have aux : ∀ (s : State Policy) (xs : List (Observation Policy)),
      0 < CTauClassPreference.totalMass s.c →
        0 < CTauClassPreference.totalMass (runFrom m s xs).2.c := by
    intro s xs hs
    induction xs generalizing s with
    | nil => simpa [runFrom]
    | cons o xs ih =>
        apply ih
        simp only [step]
        rw [advanceC_total]
        split <;> nlinarith [m.omegaC_pos, m.etaC_pos]
  apply aux (init m) obs
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

omit [Nonempty Policy] in
theorem click_C_probability (m : Makeup Policy) (pre : List (Observation Policy))
    (o : Observation Policy) :
    CTauClassPreference.ProbabilityDistribution (step m (stateAfter m pre) o).1.C := by
  simp only [step]
  exact normalizeC_probability (stateAfter_c_nonnegative m pre)
    (stateAfter_c_total_positive m pre)

/-! A concrete two-click preference update. -/

/-- Example η_d is 1 so the example isolates preference forgetting. -/
def exampleEtaD : ℝ := 1
/-- Example ω_d is 1 so the example isolates preference forgetting. -/
def exampleOmegaD : ℝ := 1
/-- Example η_c is 1 to add one focused terminal observation. -/
def exampleEtaC : ℚ := 1
/-- Example ω_c is 9/10 to exhibit a nontrivial forgetting step. -/
def exampleOmegaC : ℚ := 9 / 10
/-- Example η_h is 1 because habit rates are not the demonstrated quantity. -/
def exampleEtaHabit : ℚ := 1
/-- Example ω_h is 1 because habit rates are not the demonstrated quantity. -/
def exampleOmegaHabit : ℚ := 1
/-- Example η_θ is 1 because pattern rates are not the demonstrated quantity. -/
def exampleEtaTheta : ℚ := 1
/-- Example ω_θ is 1 because pattern rates are not the demonstrated quantity. -/
def exampleOmegaTheta : ℚ := 1

/-- Concrete makeup for the Friston 2017 / Smith, Friston & Whyte 2022 example. -/
noncomputable def exampleMakeup : Makeup Unit where
  A := fun _ _ => 1
  d₀ := fun _ => 1
  habit₀ := []
  pattern := ⟨"pattern/example"⟩
  theta₀ := []
  kappa := 100
  kappa_pos := by norm_num
  etaD := exampleEtaD
  etaD_pos := by norm_num [exampleEtaD]
  omegaD := exampleOmegaD
  omegaD_pos := by norm_num [exampleOmegaD]
  omegaD_le_one := by norm_num [exampleOmegaD]
  etaC := exampleEtaC
  etaC_pos := by norm_num [exampleEtaC]
  omegaC := exampleOmegaC
  omegaC_pos := by norm_num [exampleOmegaC]
  omegaC_le_one := by norm_num [exampleOmegaC]
  etaHabit := exampleEtaHabit
  etaHabit_pos := by norm_num [exampleEtaHabit]
  omegaHabit := exampleOmegaHabit
  omegaHabit_pos := by norm_num [exampleOmegaHabit]
  omegaHabit_le_one := by norm_num [exampleOmegaHabit]
  etaTheta := exampleEtaTheta
  etaTheta_pos := by norm_num [exampleEtaTheta]
  omegaTheta := exampleOmegaTheta
  omegaTheta_pos := by norm_num [exampleOmegaTheta]
  omegaTheta_le_one := by norm_num [exampleOmegaTheta]
  L := R20Run.hespLevel
  q₀ := R20Run.half
  precisionIterations := 2
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
  E := fun _ => 1
  G := fun _ => 1
  F := fun _ => 0

example :
    let clicks := run exampleMakeup
      [exampleObservation .focused 8, exampleObservation .related 9]
    clicks.map (fun click => click.c .focused) = [55, 101 / 2] := by
  have h : CTauClassPreference.EndingClass.focused ≠ .notYetEvaluated := by decide
  norm_num [run, runFrom, step, init, initialC, kit, normalizeC,
    evidencePrior, EvidenceFromTheProcess.posterior, EvidenceFromTheProcess.evidence,
    exampleMakeup, exampleObservation, exampleOutcome, advanceC, endingDelta,
    exampleEtaD, exampleOmegaD, exampleEtaC, exampleOmegaC, exampleEtaHabit,
    exampleOmegaHabit, exampleEtaTheta, exampleOmegaTheta, decayRated, addRated,
    advanceRated, advanceWitnessedRated, h]

abbrev ExamplePolicy := PrecisionFromObservation.TwoPolicy

/-- Two-policy makeup for the computed Friston 2017 precision example. -/
noncomputable def precisionExampleMakeup : Makeup ExamplePolicy where
  A := fun _ _ => 1
  d₀ := fun _ => 1
  habit₀ := []
  pattern := ⟨"pattern/precision-example"⟩
  theta₀ := []
  kappa := 100
  kappa_pos := by norm_num
  etaD := 1
  etaD_pos := by norm_num
  omegaD := 1
  omegaD_pos := by norm_num
  omegaD_le_one := by norm_num
  etaC := 1
  etaC_pos := by norm_num
  omegaC := 9 / 10
  omegaC_pos := by norm_num
  omegaC_le_one := by norm_num
  etaHabit := 1
  etaHabit_pos := by norm_num
  omegaHabit := 1
  omegaHabit_pos := by norm_num
  omegaHabit_le_one := by norm_num
  etaTheta := 1
  etaTheta_pos := by norm_num
  omegaTheta := 1
  omegaTheta_pos := by norm_num
  omegaTheta_le_one := by norm_num
  L := R20Run.hespLevel
  q₀ := R20Run.half
  precisionIterations := 2
  initialFocus := 7

/-- Two-policy E, G, F arrive as observations in slice 2; constant F makes
the fixed point exact while E and G remain policy-indexed. -/
def precisionExampleObservation (ending : EndingClass) (focus : Nat) :
    Observation ExamplePolicy where
  observation := true
  habitOutcome := ⟨.a, true, true⟩
  thetaOutcomes := []
  endingClass := ending
  focus := focus
  E := fun | .a => 2 | .b => 1
  G := fun | .a => 0 | .b => 1
  F := fun _ => 0

example :
    let clicks := run precisionExampleMakeup
      [precisionExampleObservation .focused 8, precisionExampleObservation .related 9]
    clicks.map (fun click => click.precision.betaPrior) = [5 / 4, 5 / 4] := by
  norm_num [run, runFrom, step, init, precisionExampleMakeup, precisionExampleObservation,
    iteratePrecision, PrecisionFromObservation.firstIterate,
    PrecisionFromObservation.expectedGChange,
    PrecisionFromObservation.posterior_eq_prior_of_constant_F,
    R20Run.descend, R20Run.predict, R20Run.valenceUpdate, R20Run.normalize,
    R20Run.affectiveEvidence, R20Run.charge, R20Run.hespLevel, R20Run.half,
    R20Run.identityB, R20Run.sum_valence]

/-! A nonconstant-F two-click example where precision changes valence. -/

/-- One Friston 2017 equation 2.7 iteration makes the nonconstant-F effect explicit. -/
noncomputable def movingPrecisionMakeup : Makeup ExamplePolicy :=
  { precisionExampleMakeup with precisionIterations := 1 }

/-- Exact two-policy scores: F cancels G/β for policy b at the initial β = 5/4. -/
noncomputable def movingPrecisionObservation (ending : EndingClass) (focus : Nat) :
    Observation ExamplePolicy where
  observation := true
  habitOutcome := ⟨.a, true, true⟩
  thetaOutcomes := []
  endingClass := ending
  focus := focus
  E := fun _ => 1
  G := fun | .a => 0 | .b => 5 / 4 * Real.log 3
  F := fun | .a => 0 | .b => -Real.log 3

/-- The exact first-click expected-G displacement. -/
noncomputable def movingX : ℝ := 5 / 16 * Real.log 3

theorem moving_click_zero_betaPosterior :
    let clicks := run movingPrecisionMakeup
      [movingPrecisionObservation .focused 8, movingPrecisionObservation .related 9]
    (clicks.head?.getD (step movingPrecisionMakeup (init movingPrecisionMakeup)
      (movingPrecisionObservation .focused 8)).1).precision.betaPosterior = 5 / 4 + movingX := by
  norm_num [run, runFrom, step, init, movingPrecisionMakeup, precisionExampleMakeup,
    movingPrecisionObservation, movingX, iteratePrecision,
    PrecisionFromObservation.firstIterate, PrecisionFromObservation.expectedGChange,
    PrecisionFromObservation.priorPolicy, PrecisionFromObservation.posteriorPolicy,
    PrecisionFromObservation.softmax, R20Run.descend, R20Run.hespLevel, R20Run.half,
    R20Run.sum_valence, PrecisionFromObservation.sum_twoPolicy, Real.exp_neg]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  norm_num
  ring

theorem moving_click_one_betaPrior :
    let first := movingPrecisionObservation .focused 8
    let second := movingPrecisionObservation .related 9
    (step movingPrecisionMakeup (step movingPrecisionMakeup
      (init movingPrecisionMakeup) first).2 second).1.precision.betaPrior =
      (10 + 17 * movingX) / (8 + 10 * movingX) := by
  norm_num [step, init, movingPrecisionMakeup, precisionExampleMakeup,
    movingPrecisionObservation, movingX, iteratePrecision,
    PrecisionFromObservation.firstIterate, PrecisionFromObservation.expectedGChange,
    PrecisionFromObservation.priorPolicy, PrecisionFromObservation.posteriorPolicy,
    PrecisionFromObservation.softmax, PrecisionFromObservation.sum_twoPolicy,
    R20Run.descend, R20Run.predict, R20Run.valenceUpdate, R20Run.normalize,
    R20Run.affectiveEvidence, R20Run.charge, R20Run.hespLevel, R20Run.half,
    R20Run.identityB, R20Run.sum_valence, Real.exp_neg]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have log_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  field_simp <;> ring_nf <;> nlinarith

theorem moving_click_one_betaPrior_moved :
    let first := movingPrecisionObservation .focused 8
    let second := movingPrecisionObservation .related 9
    let beta := (step movingPrecisionMakeup (step movingPrecisionMakeup
      (init movingPrecisionMakeup) first).2 second).1.precision.betaPrior
    beta ≠ 5 / 4 ∧ 5 / 4 < beta := by
  dsimp only
  rw [moving_click_one_betaPrior]
  have log_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have x_pos : 0 < movingX := by
    unfold movingX
    positivity
  have denominator_pos : 0 < 8 + 10 * movingX := by positivity
  have greater : (5 / 4 : ℝ) < (10 + 17 * movingX) / (8 + 10 * movingX) := by
    rw [lt_div_iff₀ denominator_pos]
    nlinarith
  exact ⟨ne_of_gt greater, greater⟩

#print axioms moving_click_one_betaPrior
#print axioms moving_click_one_betaPrior_moved

#print axioms step_betaPrior_next
#print axioms click_betaPrior_constant_of_flat
#print axioms iteratePrecision_constant_F

end DarkTower.WarMachine.R20Step
