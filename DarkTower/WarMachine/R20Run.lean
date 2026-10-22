import DarkTower.WarMachine.R20FocusedSelection

/-!
# R20 over a run: what one click hands to the next

In plain terms: the certificate judges one click. A machine is a sequence of
clicks, and each click starts from what the previous one left. This module
states what carries across a click boundary, and proves what follows over a
run: the habit counts are the fold of every outcome, the belief about the
initial state is the count of every posterior, the prior precision is set by
a valence belief that each click updates, and each click's strategic row names
the focus the previous click held.

Friston et al. (2017), `refs/friston2017.txt`:

* :718-721: "at the end of each sequence of observations (i.e., trial of
  observation epochs), the expected (concentration) parameters are updated to
  mediate learning over trials". A click is a trial here.
* :378-379: concentration parameters "can be regarded as the number of
  occurrences encountered in the past".
* eq. 2.7, :678: `d = d + s1`, the update of the initial-state counts.
  :820-822: "if a particular state is encountered frequently, it will come to
  dominate posterior expectations" (`repeated_state_dominates`).
* eq. 2.1, :324-339: `β` is one of the model parameters `η = {a, b, d, β}`,
  with prior `Γ(1, β)`, the same kind of thing as `d`. :1356-1357, "In this
  article, the only parameters that are updated are those encoding prior
  beliefs about the initial state", says which parameters that paper chose to
  learn in its simulations; it is not a rule that `β` cannot be learned.

The prior `β` is set from a slower level, as in Hesp et al. (2021),
`refs/hesp2021.txt` §3.3. Each click carries a belief `q` over two valence
states, `+` and `−`, each with its own rate, `β⁽⁺,⁻⁾ = (0.5, 2.0)` in their
simulations.

* Downward, §3.3.2, :260-271: `β = β⁽⁺,⁻⁾ · A⁽ᴬ⁾ s⁽ᴬ⁾`, the rate averaged
  over the predicted valence (`BetaFromValence`, `descend`). The ascending
  message below has no `A⁽ᴬ⁾` term, which is consistent only with `A⁽ᴬ⁾` the
  identity; it is taken as the identity here.
* Upward, §3.3.3, :283-286: after the click,
  `s̄⁽ᴬ⁾ = σ(ln B⁽ᴬ⁾ s̄⁽ᴬ⁾ₜ₋₁ − ln[(βₖ − AC)/βₖ · β/(β − AC)])`, and the next
  click starts from `B⁽ᴬ⁾ s̄⁽ᴬ⁾` (`Carries.valence`, `valenceUpdate`,
  `predict`). The affective charge is `AC = β − β̄` (`charge`): Table 4 and
  :166 write `AC = (π − π̄) · G` with `π` the prior and `π̄` the posterior,
  which is `β − β̄` by Friston 2017 eq. 2.7. The line after the update, :288,
  writes `(π̄ − π) · G`; with that sign the update is not the Bayesian model
  reduction of `Γ(1, β)` to `Γ(1, βₖ)` that §3.3.3 says it is, so Table 4 is
  followed.

So only the prior `β` is set from above; the posterior `β̄` is still inferred
within the click, and the precision row's cases record which way it moved.
Carrying a click's posterior `β̄` forward as the next prior is not this rule
and is refused (`posteriorBetaCarried_refused`). When every valence state has
the same rate, the prior `β` is that rate at every click
(`run_betaPrior_constant_of_flat`); this is the narrower choice of Friston
2017's simulations and of SPM, which resets the rate to the fixed `MDP.beta`
at the start of each trial (`spm_MDP_VB_X.m:433`).

The evidence row's prior is the mean of `Dir(d)`, `d / Σ d`. Friston writes
the expected log, `ψ(d) − ψ(d0)`, inside inference; the row records a
probability, and the mean is the probability that `Dir(d)` assigns.

The habit counts (`R15TemporalHierarchy`) are the same kind of parameter: the
next click consumes the slow state this click produced. The strategic row's
`previousFocus` is, by its meaning, the focus of the previous click; this
module makes that a condition, so a focus change is read off two clicks.

Results, for a run whose clicks are each focus-certified and carried:

* `run_habit_accumulates`: the last click's slow state is the fold of
  `advance` over every click's outcome, from the first click's;
* `run_concentration_accumulates`: the d counts at click `n` are the first
  click's plus every earlier posterior;
* `repeated_state_dominates`: if every posterior so far was certain of `s`,
  the prior on `s` at click `n` is `(d₀ s + n) / (Σ d₀ + n)`, and it tends to 1;
* `run_betaPrior_step`: the next click's prior `β` is `descend` of
  `predict` of this click's valence updated by this click's `β` and `β̄`;
* `zero_charge_keeps_valence`: when `β̄ = β` the valence belief does not move
  (Hesp :288, "the logarithm of one is zero");
* `rising_precision_favours_positive`: when `β̄ < β` (precision rose), the
  evidence for the lower-rate valence `+` is larger than for `−`;
* `example_valence_moves`: with Hesp's rates, from `q = (1/2, 1/2)`,
  `β = 5/4` and `β̄ = 1`, the valence moves to `(7/11, 4/11)` and the next
  prior `β` is `23/22`;
* `run_betaPrior_constant_of_flat`: with equal rates, every click has the
  same prior `β`;
* `run_focus_case`: a click's strategic case is `focusKept` exactly when its
  focus equals the previous click's;
* `run_ids_distinct`: no two clicks share a run id, so a click whose
  precision row reads another click's G is not wired (`stale_G_not_wired`).

Controls, each refused by `Carries`: habit counts reset between clicks; the
d counts not updated; the valence not carried; a stale previous focus; a
replayed run id. The posterior `β` carried as prior is refused by
`BetaFromValence`. `example_carries` shows the conditions can be met.
-/

namespace DarkTower.WarMachine.R20Run

open DarkTower.WarMachine.CTauClassPreference
open DarkTower.WarMachine.R20Graph (Node)
open DarkTower.WarMachine.R20Certificate
open DarkTower.WarMachine.R20FocusedSelection
open DarkTower.WarMachine.R15StrategicTarget
open DarkTower.WarMachine.R15TemporalHierarchy
open Filter Topology

open scoped BigOperators
noncomputable section
variable {Policy : Type} [Fintype Policy] [Nonempty Policy]
attribute [local instance] Classical.propDecidable

/-! ## The valence level (Hesp et al. 2021, §3.3) -/

/-- The two affective states, `+` and `−`. -/
inductive Valence
  | pos
  | neg
  deriving DecidableEq

instance : Fintype Valence :=
  ⟨{.pos, .neg}, by intro x; cases x <;> simp⟩

theorem sum_valence (f : Valence → ℝ) : ∑ k, f k = f .pos + f .neg := by
  rw [show (Finset.univ : Finset Valence) = {.pos, .neg} from rfl,
    Finset.sum_pair (by decide)]

theorem card_valence : Fintype.card Valence = 2 := rfl

/-- The slow level: a rate `βₖ` for each valence state, and the transition
`B k j`, the probability of `k` at the next click after `j`. -/
structure AffectiveLevel where
  rate : Valence → ℝ
  B : Valence → Valence → ℝ

/-- The downward message: the prior rate is the rate averaged over the
valence belief, `β = β⁽⁺,⁻⁾ · q`. -/
def descend (L : AffectiveLevel) (q : Valence → ℝ) : ℝ := ∑ k, L.rate k * q k

/-- Affective charge, `AC = β − β̄`. -/
def charge (betaPrior betaPosterior : ℝ) : ℝ := betaPrior - betaPosterior

/-- The evidence for valence `k` from one click,
`exp(−ln[(βₖ − AC)/βₖ · β/(β − AC)])`: the Bayesian model reduction of the
prior `Γ(1, β)` to `Γ(1, βₖ)`, given the posterior `Γ(1, β̄)`. -/
def affectiveEvidence (L : AffectiveLevel) (betaPrior betaPosterior : ℝ) (k : Valence) : ℝ :=
  L.rate k / (L.rate k - charge betaPrior betaPosterior) *
    ((betaPrior - charge betaPrior betaPosterior) / betaPrior)

def normalize (x : Valence → ℝ) : Valence → ℝ := fun k => x k / ∑ j, x j

/-- The upward message, `σ(ln q + ln evidence)`, written as the normalised
product, which it equals for positive factors. -/
def valenceUpdate (L : AffectiveLevel) (q : Valence → ℝ) (betaPrior betaPosterior : ℝ) :
    Valence → ℝ :=
  normalize fun k => q k * affectiveEvidence L betaPrior betaPosterior k

/-- The valence the next click starts from, `B⁽ᴬ⁾ s̄⁽ᴬ⁾`. -/
def predict (L : AffectiveLevel) (q : Valence → ℝ) : Valence → ℝ :=
  fun k => ∑ j, L.B k j * q j

/-- One click as the run keeps it: its rows, its ports, its outer choice, the
initial-state counts `d` it started from, and the valence belief it started
from. -/
structure Click (Policy : Type) where
  records : Records Policy
  ports : R20Graph.Ports Policy
  selection : OuterSelection
  d : Hidden → ℝ
  valence : Valence → ℝ

/-- The evidence row's prior is the mean of `Dir(d)`. -/
def PriorFromCounts (c : Click Policy) : Prop :=
  (∀ s, 0 < c.d s) ∧
    ∀ r, c.records .evidence = some r → r.prior = fun s => c.d s / ∑ x, c.d x

/-- The precision row's prior `β` is the downward message from the valence
the click started from. -/
def BetaFromValence (L : AffectiveLevel) (c : Click Policy) : Prop :=
  ∀ r, c.records .precision = some r → r.betaPrior = descend L c.valence

/-- What click `a` hands to the next click `b`. -/
structure Carries (L : AffectiveLevel) (a b : Click Policy) : Prop where
  runAdvances : a.ports.runId < b.ports.runId
  habit : ∀ ra rb, a.records .habit = some ra → b.records .habit = some rb →
    rb.before = ra.nextConsumed
  counts : ∀ ra, a.records .evidence = some ra → b.d = a.d + ra.posterior
  valence : ∀ ra, a.records .precision = some ra →
    b.valence = predict L (valenceUpdate L a.valence ra.betaPrior ra.betaPosterior)
  focus : ∀ sa sb, a.records .strategicFocus = some sa →
    b.records .strategicFocus = some sb → sb.previousFocus = sa.tick.focus

/-- Clicks `0 .. n`: each focus-certified, with its evidence prior read from
its counts and its prior `β` from its valence, and each carried into the
next. -/
def RunCertified (L : AffectiveLevel) (relation : Target → Target → TargetRelation)
    (c : ℕ → Click Policy) (n : ℕ) : Prop :=
  (∀ i ≤ n, FocusCertified relation (c i).records (c i).ports (c i).selection ∧
    PriorFromCounts (c i) ∧ BetaFromValence L (c i)) ∧
  ∀ i < n, Carries L (c i) (c (i + 1))

omit [Nonempty Policy] in
/-- A certified click has every row, and every row conforms. -/
theorem row_of_certified {relation : Target → Target → TargetRelation} {c : Click Policy}
    (h : FocusCertified relation c.records c.ports c.selection) (node : Node) :
    ∃ r, c.records node = some r ∧ conforms node r :=
  ((certified_iff c.records c.ports).mp h.1).1 node

/-! ## Habit counts -/

omit [Fintype Policy] [Nonempty Policy] in
/-- The fold, stated on the rows: if each row is R15 feedback and each click
consumes the previous click's slow state, the last after-state is every
outcome folded into the first before-state. -/
theorem habit_fold (hab : ℕ → TwoTickRecord Policy) (n : ℕ)
    (feedback : ∀ i ≤ n, TwoTickFeedback (hab i))
    (carried : ∀ i < n, (hab (i + 1)).before = (hab i).nextConsumed) :
    (hab n).after =
      ((List.range (n + 1)).map fun i => (hab i).outcome).foldl advance (hab 0).before := by
  induction n with
  | zero => simp [(feedback 0 le_rfl).2.1]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append,
      ← ih (fun i hi => feedback i (by omega)) (fun i hi => carried i (by omega))]
    have fb := feedback (n + 1) le_rfl
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [fb.2.1, carried n (by omega), (feedback n (by omega)).2.2]

omit [Nonempty Policy] in
theorem run_habit_accumulates {relation : Target → Target → TargetRelation}
    {L : AffectiveLevel} {c : ℕ → Click Policy} {n : ℕ} (run : RunCertified L relation c n)
    (hab : ℕ → TwoTickRecord Policy) (hh : ∀ i ≤ n, (c i).records .habit = some (hab i)) :
    (hab n).after =
      ((List.range (n + 1)).map fun i => (hab i).outcome).foldl advance (hab 0).before := by
  apply habit_fold hab n
  · intro i hi
    obtain ⟨r, hr, good⟩ := row_of_certified (run.1 i hi).1 .habit
    rw [hh i hi] at hr
    cases hr
    exact good
  · intro i hi
    exact (run.2 i hi).habit _ _ (hh i (by omega)) (hh (i + 1) (by omega))

/-! ## Initial-state counts -/

omit [Nonempty Policy] in
theorem run_concentration_accumulates {relation : Target → Target → TargetRelation}
    {L : AffectiveLevel} {c : ℕ → Click Policy} {n : ℕ} (run : RunCertified L relation c n)
    (ev : ℕ → EvidenceRow) (he : ∀ i ≤ n, (c i).records .evidence = some (ev i)) :
    (c n).d = (c 0).d + ∑ i ∈ Finset.range n, (ev i).posterior := by
  induction n with
  | zero => simp
  | succ n ih =>
    have run' : RunCertified L relation c n :=
      ⟨fun i hi => run.1 i (by omega), fun i hi => run.2 i (by omega)⟩
    rw [Finset.sum_range_succ, ← add_assoc,
      ← ih run' (fun i hi => he i (by omega)),
      (run.2 n (by omega)).counts _ (he n (by omega))]

def pointMass (s : Hidden) : Hidden → ℝ := fun x => if x = s then 1 else 0

/-- `(a + n) / (b + n)` tends to 1. -/
theorem shifted_ratio_tendsto_one (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => (a + n) / (b + n)) atTop (𝓝 1) := by
  have key : ∀ n : ℕ, (a + n) / (b + n) = 1 - (b - a) / (b + n) := by
    intro n
    have : (b + n) ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [key]
  have : Tendsto (fun n : ℕ => (b - a) / (b + n)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_left _ b tendsto_natCast_atTop_atTop
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this

omit [Nonempty Policy] in
/-- Friston 2017 :820-822. If every posterior so far was certain of `s`, the
prior on `s` at click `n` is `(d₀ s + n) / (Σ d₀ + n)`. -/
theorem repeated_state_prior {relation : Target → Target → TargetRelation}
    {L : AffectiveLevel} {c : ℕ → Click Policy} {n : ℕ} (run : RunCertified L relation c n)
    (ev : ℕ → EvidenceRow) (he : ∀ i ≤ n, (c i).records .evidence = some (ev i))
    (s : Hidden) (certain : ∀ i < n, (ev i).posterior = pointMass s) :
    (ev n).prior s = ((c 0).d s + n) / ((∑ x, (c 0).d x) + n) := by
  have counts := run_concentration_accumulates run ev he
  have point : ∀ x, ∑ i ∈ Finset.range n, (ev i).posterior x = n * pointMass s x := by
    intro x
    rw [Finset.sum_congr rfl (fun i hi => congrFun (certain i (Finset.mem_range.mp hi)) x)]
    simp
  rw [(run.1 n le_rfl).2.1.2 _ (he n le_rfl), counts]
  simp only [Pi.add_apply, Finset.sum_apply, point, Fin.sum_univ_two]
  fin_cases s <;> simp [pointMass] <;> ring

/-- The repeated state comes to dominate: along runs that keep observing it,
its prior tends to 1. -/
theorem repeated_state_dominates (d₀ : Hidden → ℝ) (pos : ∀ x, 0 < d₀ x) (s : Hidden) :
    Tendsto (fun n : ℕ => (d₀ s + n) / ((∑ x, d₀ x) + n)) atTop (𝓝 1) :=
  shifted_ratio_tendsto_one _ _ (Finset.sum_pos (fun x _ => pos x) Finset.univ_nonempty)

/-! ## Prior precision from the valence level -/

omit [Nonempty Policy] in
/-- The next click's prior `β` is the downward message from this click's
valence, updated by this click's `β` and `β̄` and moved by `B⁽ᴬ⁾`. -/
theorem run_betaPrior_step {relation : Target → Target → TargetRelation}
    {L : AffectiveLevel} {c : ℕ → Click Policy} {n : ℕ} (run : RunCertified L relation c n)
    (pr : ℕ → PrecisionFromObservation.TickRecord Policy)
    (hp : ∀ i ≤ n, (c i).records .precision = some (pr i)) {i : ℕ} (hi : i < n) :
    (pr (i + 1)).betaPrior =
      descend L
        (predict L (valenceUpdate L (c i).valence (pr i).betaPrior (pr i).betaPosterior)) := by
  rw [(run.1 (i + 1) hi).2.2 _ (hp (i + 1) hi), (run.2 i hi).valence _ (hp i (by omega))]

/-- Hesp :288: "when the affective charge is zero, the affective expectations
on the current trial are determined completely by the expectations at the
previous trial". -/
theorem zero_charge_keeps_valence (L : AffectiveLevel) (q : Valence → ℝ) {beta : ℝ}
    (hb : beta ≠ 0) (hr : ∀ k, L.rate k ≠ 0) (hq : ∑ k, q k = 1) :
    valenceUpdate L q beta beta = q := by
  funext k
  simp [valenceUpdate, normalize, affectiveEvidence, charge, hb, hr, hq]

/-- When the posterior rate falls below the prior rate (`AC > 0`, precision
rose), the evidence for the valence with the lower rate is the larger. -/
theorem rising_precision_favours_positive (L : AffectiveLevel) {betaPrior betaPosterior : ℝ}
    (h0 : 0 < betaPosterior) (h1 : betaPosterior < betaPrior)
    (hpos : charge betaPrior betaPosterior < L.rate .pos) (hlt : L.rate .pos < L.rate .neg) :
    affectiveEvidence L betaPrior betaPosterior .neg <
      affectiveEvidence L betaPrior betaPosterior .pos := by
  unfold affectiveEvidence
  have hac : 0 < charge betaPrior betaPosterior := by unfold charge; linarith
  have common : 0 < (betaPrior - charge betaPrior betaPosterior) / betaPrior := by
    unfold charge; apply div_pos <;> linarith
  apply mul_lt_mul_of_pos_right _ common
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem normalize_sum {x : Valence → ℝ} (h : ∑ k, x k ≠ 0) : ∑ k, normalize x k = 1 := by
  simp only [normalize, ← Finset.sum_div, div_self h]

theorem predict_sum (L : AffectiveLevel) (stoch : ∀ j, ∑ k, L.B k j = 1) (x : Valence → ℝ) :
    ∑ k, predict L x k = ∑ k, x k := by
  have sp := stoch .pos
  have sn := stoch .neg
  simp only [predict, sum_valence] at sp sn ⊢
  linear_combination x .pos * sp + x .neg * sn

theorem descend_flat (L : AffectiveLevel) {r : ℝ} (flat : ∀ k, L.rate k = r)
    {q : Valence → ℝ} (hq : ∑ k, q k = 1) : descend L q = r := by
  simp only [descend, flat, ← Finset.mul_sum, hq, mul_one]

omit [Nonempty Policy] in
/-- With equal rates, a stochastic `B⁽ᴬ⁾` and a normalised first valence,
every click has the same prior `β`: the constant prior of Friston 2017's
simulations is the special case of a flat valence level. -/
theorem run_betaPrior_constant_of_flat {relation : Target → Target → TargetRelation}
    {L : AffectiveLevel} {c : ℕ → Click Policy} {n : ℕ} (run : RunCertified L relation c n)
    (pr : ℕ → PrecisionFromObservation.TickRecord Policy)
    (hp : ∀ i ≤ n, (c i).records .precision = some (pr i))
    {r : ℝ} (flat : ∀ k, L.rate k = r) (stoch : ∀ j, ∑ k, L.B k j = 1)
    (start : ∑ k, (c 0).valence k = 1)
    (nondeg : ∀ i < n,
      ∑ k, (c i).valence k * affectiveEvidence L (pr i).betaPrior (pr i).betaPosterior k ≠ 0) :
    ∀ i ≤ n, (pr i).betaPrior = r := by
  have total : ∀ i ≤ n, ∑ k, (c i).valence k = 1 := by
    intro i hi
    induction i with
    | zero => exact start
    | succ i ih =>
      rw [(run.2 i (by omega)).valence _ (hp i (by omega)), predict_sum L stoch]
      exact normalize_sum (nondeg i (by omega))
  intro i hi
  rw [(run.1 i hi).2.2 _ (hp i hi)]
  exact descend_flat L flat (total i hi)

/-! ## Two valence levels -/

def half : Valence → ℝ := fun _ => 1 / 2

def identityB : Valence → Valence → ℝ := fun k j => if k = j then 1 else 0

theorem predict_identity {L : AffectiveLevel} (h : L.B = identityB) (q : Valence → ℝ) :
    predict L q = q := by
  funext k
  cases k <;> simp [predict, h, identityB]

/-- Hesp's rates, `β⁽⁺,⁻⁾ = (0.5, 2.0)`. Their `B⁽ᴬ⁾` is not printed; the
identity is this example's choice. -/
def hespLevel : AffectiveLevel := ⟨fun | .pos => 1 / 2 | .neg => 2, identityB⟩

/-- Every valence state with rate 1: the prior `β` stays 1. -/
def flatLevel : AffectiveLevel := ⟨fun _ => 1, identityB⟩

/-- From an even valence belief, Hesp's rates give the prior `β = 5/4`. -/
theorem hesp_start : descend hespLevel half = 5 / 4 := by
  norm_num [descend, sum_valence, hespLevel, half]

/-- A click whose posterior rate fell from `5/4` to `1` moves the valence
belief from `1/2` to `7/11` on `+`, and the next prior `β` from `5/4` to
`23/22`. -/
theorem example_valence_moves :
    valenceUpdate hespLevel half (5 / 4) 1 .pos = 7 / 11 ∧
      descend hespLevel (predict hespLevel (valenceUpdate hespLevel half (5 / 4) 1)) =
        23 / 22 := by
  rw [predict_identity rfl]
  constructor <;>
    norm_num [valenceUpdate, normalize, affectiveEvidence, charge, descend, sum_valence,
      hespLevel, half]

/-- Under the flat level an even valence belief is carried unchanged. -/
theorem carried_half_flat {betaPrior betaPosterior : ℝ}
    (h : affectiveEvidence flatLevel betaPrior betaPosterior .pos ≠ 0) :
    predict flatLevel (valenceUpdate flatLevel half betaPrior betaPosterior) = half := by
  rw [predict_identity rfl]
  have same : ∀ k, affectiveEvidence flatLevel betaPrior betaPosterior k =
      affectiveEvidence flatLevel betaPrior betaPosterior .pos := fun _ => rfl
  funext k
  simp only [valenceUpdate, normalize, sum_valence, same, half]
  field_simp
  ring

/-! ## Focus, run ids -/

omit [Nonempty Policy] in
/-- The strategic case of click `i + 1` is read off two clicks. -/
theorem run_focus_case {relation : Target → Target → TargetRelation}
    {L : AffectiveLevel} {c : ℕ → Click Policy} {n : ℕ} (run : RunCertified L relation c n)
    {i : ℕ} (hi : i < n)
    (sa sb : StrategicFocusRow) (ha : (c i).records .strategicFocus = some sa)
    (hb : (c (i + 1)).records .strategicFocus = some sb) :
    caseOf (Policy := Policy) .strategicFocus sb = .strategicFocus .focusKept ↔
      sb.tick.focus = sa.tick.focus := by
  have prev := (run.2 i hi).focus _ _ ha hb
  by_cases eq : sb.tick.focus = sa.tick.focus
  · simp [caseOf, prev, eq]
  · have ne : sa.tick.focus ≠ sb.tick.focus := fun h => eq h.symm
    simp [caseOf, prev, eq, ne]

omit [Nonempty Policy] in
theorem run_ids_distinct {relation : Target → Target → TargetRelation}
    {L : AffectiveLevel} {c : ℕ → Click Policy} {n : ℕ} (run : RunCertified L relation c n)
    {i j : ℕ}
    (hij : i < j) (hj : j ≤ n) : (c i).ports.runId < (c j).ports.runId := by
  induction j with
  | zero => omega
  | succ j ih =>
    have step := (run.2 j (by omega)).runAdvances
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with lt | rfl
    · exact (ih lt (by omega)).trans step
    · exact step

omit [Nonempty Policy] in
/-- A later click whose precision row reads an earlier click's G is not
wired: that G carries the earlier run id. -/
theorem stale_G_not_wired {relation : Target → Target → TargetRelation}
    {L : AffectiveLevel} {c : ℕ → Click Policy} {n : ℕ} (run : RunCertified L relation c n)
    {i j : ℕ}
    (hij : i < j) (hj : j ≤ n)
    (stale : (c j).ports.precisionG = (c i).ports.selectionG) :
    ¬ R20Graph.Wired (c j).records (c j).ports := by
  intro wired
  have lt := run_ids_distinct run hij hj
  have wi := ((certified_iff (c i).records (c i).ports).mp (run.1 i (by omega)).1.1).2.1
  have run_i := wi.gRun
  rw [← stale, wired.gRead, wired.gRun] at run_i
  exact (ne_of_gt lt) run_i

/-! ## Controls

Two clicks with the habit, evidence, precision and strategic rows present.
The other rows are absent: `Carries` is about the four rows that cross the
boundary, and a certified run supplies all of them (`row_of_certified`). -/

def rows (h : TwoTickRecord Policy) (e : EvidenceRow)
    (p : PrecisionFromObservation.TickRecord Policy) (s : StrategicFocusRow) : Records Policy
  | .habit => some h
  | .evidence => some e
  | .precision => some p
  | .strategicFocus => some s
  | _ => none

def evidenceAt (prior posterior : Hidden → ℝ) : EvidenceRow :=
  ⟨prior, fun _ _ => 1, true, posterior⟩

def precisionAt (betaPrior betaPosterior : ℝ) : PrecisionFromObservation.TickRecord Policy :=
  ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 1 / 2, fun _ => 1 / 2, betaPrior, betaPosterior⟩

def selection0 : OuterSelection := ⟨[⟨7, 1⟩], ⟨7, 1⟩⟩

def counts0 : Hidden → ℝ := fun _ => 1

open PrecisionFromObservation (TwoPolicy)

/-- Habit counts before click 0: policy `a` (2, 3), policy `b` (4, 5). -/
def habitStart : SlowState TwoPolicy := [(.a, ⟨2, 3⟩), (.b, ⟨4, 5⟩)]
def successA : FastOutcome TwoPolicy := ⟨.a, true, true⟩
def failureB : FastOutcome TwoPolicy := ⟨.b, true, false⟩

/-- Click 0's habit row: a witnessed success of policy `a`. -/
def habit0 : TwoTickRecord TwoPolicy :=
  { before := habitStart, outcome := successA
    after := advance habitStart successA, nextConsumed := advance habitStart successA }

/-- Click 0: focus 7, posterior certain of state 0, an even valence belief,
`β` moved from 1 to 1/2. -/
def click0 : Click TwoPolicy :=
  ⟨rows habit0 (evidenceAt (fun _ => 1 / 2) (pointMass 0)) (precisionAt 1 (1 / 2))
    ⟨7, tickAt 7 [7]⟩, R20Graph.goodPorts 0, selection0, counts0, half⟩

/-- The successor that click 0 hands on. -/
def nextHabit : TwoTickRecord TwoPolicy :=
  { before := habit0.nextConsumed, outcome := failureB
    after := advance habit0.nextConsumed failureB
    nextConsumed := advance habit0.nextConsumed failureB }

def click1With (h : TwoTickRecord TwoPolicy) (d : Hidden → ℝ) (betaPrior : ℝ)
    (previousFocus : Target) (run : R20Graph.RunId) (valence : Valence → ℝ := half) :
    Click TwoPolicy :=
  ⟨rows h (evidenceAt (fun s => d s / ∑ x, d x) (pointMass 0)) (precisionAt betaPrior 1)
    ⟨previousFocus, tickAt 3 [3]⟩, R20Graph.goodPorts run, selection0, d, valence⟩

def click1 : Click TwoPolicy :=
  click1With nextHabit (counts0 + pointMass 0) 1 7 1

theorem example_carries : Carries flatLevel click0 click1 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro ra rb ha hb
    simp only [click0, click1, click1With, rows] at ha hb
    cases ha; cases hb; rfl
  · intro ra ha
    simp only [click0, rows] at ha
    cases ha; rfl
  · intro ra ha
    simp only [click0, rows] at ha
    cases ha
    exact (carried_half_flat
      (by norm_num [affectiveEvidence, charge, flatLevel, precisionAt])).symm
  · intro sa sb ha hb
    simp only [click0, click1, click1With, rows] at ha hb
    cases ha; cases hb; rfl

/-- The successor's prior is the mean of its counts, `(2/3, 1/3)`. -/
theorem click1_prior : PriorFromCounts click1 := by
  refine ⟨fun s => ?_, fun r hr => ?_⟩
  · simp only [click1, click1With, counts0, pointMass, Pi.add_apply]
    split_ifs <;> norm_num
  · simp only [click1, click1With, rows] at hr
    cases hr
    rfl

/-- Both clicks read their prior `β = 1` from the flat valence level. -/
theorem example_beta : BetaFromValence flatLevel click0 ∧ BetaFromValence flatLevel click1 := by
  constructor <;> intro r hr <;>
    simp only [click0, click1, click1With, rows, Option.some.injEq] at hr <;> subst hr <;>
    norm_num [click0, click1, click1With, precisionAt, descend, card_valence, flatLevel, half]

/-- Habit counts reset to the first click's before-state. -/
theorem habitReset_refused :
    ¬ Carries flatLevel click0 (click1With { nextHabit with before := habitStart }
      (counts0 + pointMass 0) 1 7 1) := by
  intro h
  have := h.habit _ _ rfl rfl
  simp only [habit0] at this
  exact advance_ne_before habitStart successA this.symm

/-- The counts not updated: click 1 starts from click 0's d. -/
theorem countsNotUpdated_refused :
    ¬ Carries flatLevel click0 (click1With nextHabit counts0 1 7 1) := by
  intro h
  have := congrFun (h.counts _ rfl) 0
  simp [click0, click1With, evidenceAt, counts0, pointMass] at this

/-- Click 0's posterior `β` (1/2) carried as click 1's prior: the valence
click 1 starts from gives 1. -/
theorem posteriorBetaCarried_refused :
    ¬ BetaFromValence flatLevel (click1With nextHabit (counts0 + pointMass 0) (1 / 2) 7 1) := by
  intro h
  have := h _ rfl
  norm_num [click1With, precisionAt, descend, card_valence, flatLevel, half] at this

/-- Click 1 starts from a valence certain of `+`, not the one click 0 hands on. -/
theorem valenceNotCarried_refused :
    ¬ Carries flatLevel click0 (click1With nextHabit (counts0 + pointMass 0) 1 7 1
      (fun k => if k = .pos then 1 else 0)) := by
  intro h
  have := congrFun (h.valence _ rfl) .pos
  change (1 : ℝ) = predict flatLevel (valenceUpdate flatLevel half 1 (1 / 2)) .pos at this
  rw [carried_half_flat (by norm_num [affectiveEvidence, charge, flatLevel])] at this
  norm_num [half] at this

/-- Click 1 reports a previous focus that click 0 did not hold. -/
theorem staleFocus_refused :
    ¬ Carries flatLevel click0 (click1With nextHabit (counts0 + pointMass 0) 1 8 1) := by
  intro h
  have := h.focus _ _ rfl rfl
  simp [tickAt] at this

/-- Click 1 replays click 0's run id. -/
theorem replayedRun_refused :
    ¬ Carries flatLevel click0 (click1With nextHabit (counts0 + pointMass 0) 1 7 0) := by
  intro h
  exact absurd h.runAdvances (by decide)

#print axioms run_habit_accumulates
#print axioms repeated_state_prior
#print axioms stale_G_not_wired
#print axioms example_carries
#print axioms example_valence_moves
#print axioms run_betaPrior_constant_of_flat

end
end DarkTower.WarMachine.R20Run
