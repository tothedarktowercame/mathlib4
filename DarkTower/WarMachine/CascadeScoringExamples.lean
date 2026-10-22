import DarkTower.WarMachine.CascadeEFE
import DarkTower.WarMachine.Proof2.ContainmentOrder

/-!
# Scoring small cascades with `CascadeEFE.scoreCascade`

`CascadeEFE.scoreCascade` is the canonical G over cascades (`GOverCascades`),
but no concrete cascade had been scored with it. This module scores the
smallest ones: the empty cascade, one pattern, two in a chain, and three in two
shapes, a chain and a join (two independent patterns that a third needs both
of).

Construction, for every example the same way:

* tokens are a finite type; a state is the set of tokens established;
* each pattern is a `CascadeTransition.InterpretedPattern` (what it consumes,
  produces, forbids, and its probability `θ` of success), interpreted when it
  is put into the cascade: `model` gives every pattern its interpretation, so
  no cascade built here can be refused for a missing one
  (`every_cascade_interpreted`);
* the cascade's order is the containment order built from the patterns
  (`Proof2.ContainmentOrder`: A is above B when A produces a token B
  consumes), acyclic by a token stratification;
* at each epoch the first enabled pattern in the precedence list fires
  (`CascadeEFE.choose`);
* the outcome observed at each epoch is whether the goal token is established,
  and the preference is `9/10` on reaching it.

With `θ = 1` every prediction is a point mass, so ambiguity is zero and the
risk at an epoch is `-log C` of the outcome on the cascade's trajectory
(`score_deterministic`). The scores, over three epochs:

| cascade | trajectory (goal reached?) | G |
|---|---|---|
| empty | no, no, no | `3 log 10` |
| one pattern | yes, yes, yes | `3 log (10/9)` |
| chain of two | no, yes, yes | `log 10 + 2 log (10/9)` |
| chain of three | no, no, yes | `2 log 10 + log (10/9)` |
| join of three | no, no, yes | `2 log 10 + log (10/9)` |

The chain and the join of three score the same: one pattern fires per epoch,
so a join of two independent patterns takes as many epochs as a chain of two.
Under first-enabled firing the score sees how many epochs pass before the goal,
not the shape of the cascade (`chain_and_join_score_equal`).
-/

namespace DarkTower.WarMachine.CascadeScoringExamples

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.CascadeEFE
open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.Proof2.ContainmentOrder
open scoped BigOperators

noncomputable section

variable {ι V : Type} [DecidableEq ι] [Fintype V] [DecidableEq V]

/-! ## The model -/

/-- A pattern's interpretation as a kernel on states (`CascadeTransition.patternKernel`). -/
def patK (p : InterpretedPattern V) : ProbabilityKernel (Finset V) (Finset V) :=
  finiteKernel (fun s s' => patternKernel p s s') (patternKernel_nonneg p) (patternKernel_rowsum p)

/-- The outcome: whether the goal token is established. -/
def obsK (goal : V) : ProbabilityKernel (Finset V) Bool :=
  finiteKernel (fun s b => if b = decide (goal ∈ s) then 1 else 0)
    (by intros; split_ifs <;> norm_num)
    (by intro s; cases decide (goal ∈ s) <;> simp [Fintype.sum_bool])

/-- The preference: `c` on reaching the goal, `1 - c` otherwise. -/
def prefK (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) : ProbabilityKernel Unit Bool :=
  finiteKernel (fun _ b => if b then c else 1 - c)
    (by intro _ b; cases b <;> simp <;> linarith)
    (by intro; simp [Fintype.sum_bool])

/-- Every pattern is interpreted when it is put into the cascade. -/
def model (pats : ι → InterpretedPattern V) (start : Finset V) (goal : V) :
    Model ι (Finset V) Bool where
  initial := point start
  observation := obsK goal
  guard := fun p s => decide (guard (pats p) s)
  interpretation := fun p => some (patK (pats p))

/-- The cascade on the patterns `ps`, in that precedence, ordered by containment. -/
def cascadeOf (pats : ι → InterpretedPattern V) (strat : Stratification pats) (ps : List ι) :
    CascadeEFE.Policy ι where
  cascade :=
    { nodes := {p | p ∈ ps}, addedByOrganise := ∅, edges := containmentOrder pats
      acyclic := acyclicDescent_of_stratification pats strat, precedence := ps }
  nodeDecidable := fun p => inferInstanceAs (Decidable (p ∈ ps))

theorem firing_cascadeOf (pats : ι → InterpretedPattern V) (strat : Stratification pats)
    (ps : List ι) : firing (cascadeOf pats strat ps) = ps := by
  simp [firing, cascadeOf]

/-- No cascade built from these interpretations is refused for a missing one. -/
theorem every_cascade_interpreted (pats : ι → InterpretedPattern V) (start : Finset V)
    (goal : V) (pi : CascadeEFE.Policy ι) :
    (policyKernel (model pats start goal) pi).isSome = true :=
  (policyKernel_isSome_iff _ _).2 fun _ _ => rfl

/-! ## Deterministic patterns score by their trajectory -/

/-- The state after one epoch: the first enabled pattern's products added. -/
def next (pats : ι → InterpretedPattern V) : List ι → Finset V → Finset V
  | [], s => s
  | p :: ps, s => if guard (pats p) s then s ∪ (pats p).produces else next pats ps s

theorem resolve_model (pats : ι → InterpretedPattern V) (start : Finset V) (goal : V)
    (ps : List ι) :
    resolve (model pats start goal) ps = some (ps.map fun p => (p, patK (pats p))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [resolve, ih]; rfl

theorem patK_one (p : InterpretedPattern V) (one : p.theta = 1) (s s' : Finset V) :
    (patK p).mass s s' = if s' = s ∪ p.produces then 1 else 0 := by
  simp [patK, finiteKernel, patternKernel, one]

theorem choose_det (pats : ι → InterpretedPattern V) (start : Finset V) (goal : V)
    (one : ∀ p, (pats p).theta = 1) (ps : List ι) (s y : Finset V) :
    (choose (model pats start goal) (ps.map fun p => (p, patK (pats p))) s).mass () y =
      if y = next pats ps s then 1 else 0 := by
  induction ps with
  | nil => simp [choose, next, point, finiteKernel]
  | cons p ps ih =>
    by_cases g : guard (pats p) s
    · simp [choose, next, model, g, patK_one _ (one p)]
    · simp only [List.map_cons, choose, model, next, g, decide_false, if_false]
      exact ih

/-- The cascade's kernel moves each state to `next`. -/
theorem policyKernel_det (pats : ι → InterpretedPattern V) (strat : Stratification pats)
    (start : Finset V) (goal : V) (one : ∀ p, (pats p).theta = 1) (ps : List ι) :
    ∃ b, policyKernel (model pats start goal) (cascadeOf pats strat ps) = some b ∧
      ∀ s y, b.mass s y = if y = next pats ps s then 1 else 0 := by
  unfold policyKernel
  rw [firing_cascadeOf, resolve_model]
  exact ⟨_, rfl, fun s y => choose_det pats start goal one ps s y⟩

theorem prediction_det {b : ProbabilityKernel (Finset V) (Finset V)} (f : Finset V → Finset V)
    (hb : ∀ s y, b.mass s y = if y = f s then 1 else 0) (start : Finset V) (t : ℕ)
    (y : Finset V) :
    (prediction (point start) b t).mass () y = if y = f^[t] start then 1 else 0 := by
  induction t generalizing y with
  | zero => simp [prediction, point, finiteKernel]
  | succ t ih =>
    simp only [prediction, push, finiteKernel, ih, hb, Function.iterate_succ_apply']
    rw [Finset.sum_eq_single (f^[t] start)]
    · simp
    · intro x _ hx; simp [hx]
    · simp

/-- At a point-mass prediction, an epoch's G is `-log C` of the observed outcome. -/
theorem stepG_point (goal : V) (c : ℝ) (h0 : 0 < c) (h1 : c < 1)
    (q : ProbabilityKernel Unit (Finset V)) (x : Finset V)
    (hq : ∀ y, q.mass () y = if y = x then 1 else 0)
    (h : PreferenceRiskSeparation.riskAdmissible (push q (obsK goal)) (prefK c h0.le h1.le)) :
    stepG q (obsK goal) (prefK c h0.le h1.le) h =
      -Real.log ((prefK c h0.le h1.le).mass () (decide (goal ∈ x))) := by
  have hpush : ∀ o, (push q (obsK goal)).mass () o = if o = decide (goal ∈ x) then 1 else 0 := by
    intro o
    simp only [CascadeEFE.push, finiteKernel, hq, obsK, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq']
  have hamb : CascadeEFE.ambiguity q (obsK goal) = 0 := by
    simp only [CascadeEFE.ambiguity, hq, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [CascadeEFE.entropy, obsK, finiteKernel]
    cases decide (goal ∈ x) <;> simp [Fintype.sum_bool]
  simp only [stepG, CascadeEFE.risk, hamb, add_zero, hpush]
  cases hx : decide (goal ∈ x) <;>
    simp [Fintype.sum_bool, klTerm, prefK, finiteKernel, Real.log_inv]

theorem prefK_pos (c : ℝ) (h0 : 0 < c) (h1 : c < 1) (b : Bool) :
    0 < (prefK c h0.le h1.le).mass () b := by
  cases b <;> simp [prefK, finiteKernel] <;> linarith

/-- With deterministic patterns, the cascade's G over `T` epochs is the sum of
`-log C` of the outcome at each epoch of its trajectory. -/
theorem score_deterministic (pats : ι → InterpretedPattern V) (strat : Stratification pats)
    (start : Finset V) (goal : V) (one : ∀ p, (pats p).theta = 1) (ps : List ι)
    (c : ℝ) (h0 : 0 < c) (h1 : c < 1) (T : ℕ) :
    scoreCascade (model pats start goal) (cascadeOf pats strat ps) T
        (fun _ => prefK c h0.le h1.le) =
      .ok (∑ t : Fin T, -Real.log ((prefK c h0.le h1.le).mass ()
        (decide (goal ∈ (next pats ps)^[t.val + 1] start)))) := by
  obtain ⟨b, hb, hmass⟩ := policyKernel_det pats strat start goal one ps
  have adm : ∀ t : Fin T, PreferenceRiskSeparation.riskAdmissible
      (push (prediction (model pats start goal).initial b (t.val + 1))
        (model pats start goal).observation) (prefK c h0.le h1.le) :=
    fun _ _ d _ _ => prefK_pos c h0 h1 d
  unfold scoreCascade
  simp only [hb, dif_pos adm]
  congr 1
  unfold totalG
  refine Finset.sum_congr rfl fun t _ => ?_
  exact stepG_point goal c h0 h1 _ _ (prediction_det (next pats ps) hmass start _) _

/-! ## The examples

Tokens `Fin 4`: `a = 0`, `b = 1`, the goal `g = 3` (token 2 unused). The
preference is `9/10` on reaching the goal, over three epochs. -/

abbrev Tok := Fin 4

def pat (consumes produces : Finset Tok) : InterpretedPattern Tok :=
  ⟨consumes, produces, ∅, 1, zero_le_one, le_rfl⟩

/-- One pattern: nothing to the goal. -/
def onePats : Fin 1 → InterpretedPattern Tok := fun _ => pat ∅ {3}

/-- A chain of two: nothing to `a`, `a` to the goal. -/
def chain2 : Fin 2 → InterpretedPattern Tok
  | 0 => pat ∅ {0}
  | 1 => pat {0} {3}

/-- A chain of three: nothing to `a`, `a` to `b`, `b` to the goal. -/
def chain3 : Fin 3 → InterpretedPattern Tok
  | 0 => pat ∅ {0}
  | 1 => pat {0} {1}
  | 2 => pat {1} {3}

/-- A join of three: nothing to `a`, nothing to `b`, `a` and `b` to the goal. -/
def join3 : Fin 3 → InterpretedPattern Tok
  | 0 => pat ∅ {0}
  | 1 => pat ∅ {1}
  | 2 => pat {0, 1} {3}

/-- Token level = index + 1; every pattern here raises it. -/
def strat {n : ℕ} (pats : Fin n → InterpretedPattern Tok) (h : ∀ i, ∀ c ∈ (pats i).consumes,
    ∀ p ∈ (pats i).produces, c.val + 1 < p.val + 1) : Stratification pats :=
  ⟨fun v => v.val + 1, fun _ => Nat.succ_pos _, h⟩

def C : ProbabilityKernel Unit Bool := prefK (9 / 10) (by norm_num) (by norm_num)

def score {n : ℕ} (pats : Fin n → InterpretedPattern Tok) (s : Stratification pats)
    (ps : List (Fin n)) : Except Refusal ℝ :=
  scoreCascade (model pats ∅ 3) (cascadeOf pats s ps) 3 (fun _ => C)

def s1 := strat onePats (by decide)
def s2 := strat chain2 (by decide)
def s3 := strat chain3 (by decide)
def sj := strat join3 (by decide)

theorem log_inv_c : -Real.log (9 / 10 : ℝ) = Real.log (10 / 9) := by
  rw [← Real.log_inv]; norm_num

theorem log_inv_1c : -Real.log (1 - 9 / 10 : ℝ) = Real.log 10 := by
  rw [← Real.log_inv]; norm_num

theorem empty_score : score onePats s1 [] = .ok (3 * Real.log 10) := by
  rw [score, C, score_deterministic onePats s1 ∅ 3 (fun _ => rfl) [] (9 / 10) (by norm_num)
    (by norm_num) 3]
  have traj : ∀ k, (next onePats [])^[k] (∅ : Finset Tok) = ∅ := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl
  simp only [Fin.sum_univ_three, traj]
  simp [prefK, finiteKernel, log_inv_1c]
  ring

theorem one_score : score onePats s1 [0] = .ok (3 * Real.log (10 / 9)) := by
  rw [score, C, score_deterministic onePats s1 ∅ 3 (fun _ => rfl) [0] (9 / 10) (by norm_num)
    (by norm_num) 3]
  have t1 : (next onePats [0])^[1] (∅ : Finset Tok) = {3} := by decide
  have t2 : (next onePats [0])^[2] (∅ : Finset Tok) = {3} := by decide
  have t3 : (next onePats [0])^[3] (∅ : Finset Tok) = {3} := by decide
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, t1, t2, t3]
  simp [prefK, finiteKernel, log_inv_c]
  ring

theorem chain2_score :
    score chain2 s2 [1, 0] = .ok (Real.log 10 + 2 * Real.log (10 / 9)) := by
  rw [score, C, score_deterministic chain2 s2 ∅ 3 (fun i => by fin_cases i <;> rfl) [1, 0]
    (9 / 10) (by norm_num) (by norm_num) 3]
  have t1 : (next chain2 [1, 0])^[1] (∅ : Finset Tok) = {0} := by decide
  have t2 : (next chain2 [1, 0])^[2] (∅ : Finset Tok) = {0, 3} := by decide
  have t3 : (next chain2 [1, 0])^[3] (∅ : Finset Tok) = {0, 3} := by decide
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, t1, t2, t3]
  simp [prefK, finiteKernel, log_inv_c, log_inv_1c]
  ring

theorem chain3_score :
    score chain3 s3 [2, 1, 0] = .ok (2 * Real.log 10 + Real.log (10 / 9)) := by
  rw [score, C, score_deterministic chain3 s3 ∅ 3 (fun i => by fin_cases i <;> rfl) [2, 1, 0]
    (9 / 10) (by norm_num) (by norm_num) 3]
  have t1 : (next chain3 [2, 1, 0])^[1] (∅ : Finset Tok) = {0} := by decide
  have t2 : (next chain3 [2, 1, 0])^[2] (∅ : Finset Tok) = {0, 1} := by decide
  have t3 : (next chain3 [2, 1, 0])^[3] (∅ : Finset Tok) = {0, 1, 3} := by decide
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, t1, t2, t3]
  simp [prefK, finiteKernel, log_inv_c, log_inv_1c]
  ring

theorem join3_score :
    score join3 sj [2, 1, 0] = .ok (2 * Real.log 10 + Real.log (10 / 9)) := by
  rw [score, C, score_deterministic join3 sj ∅ 3 (fun i => by fin_cases i <;> rfl) [2, 1, 0]
    (9 / 10) (by norm_num) (by norm_num) 3]
  have t1 : (next join3 [2, 1, 0])^[1] (∅ : Finset Tok) = {1} := by decide
  have t2 : (next join3 [2, 1, 0])^[2] (∅ : Finset Tok) = {0, 1} := by decide
  have t3 : (next join3 [2, 1, 0])^[3] (∅ : Finset Tok) = {0, 1, 3} := by decide
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, t1, t2, t3]
  simp [prefK, finiteKernel, log_inv_c, log_inv_1c]
  ring

/-- The chain and the join of three score the same. -/
theorem chain_and_join_score_equal : score chain3 s3 [2, 1, 0] = score join3 sj [2, 1, 0] := by
  rw [chain3_score, join3_score]

/-- More patterns before the goal cost more: each epoch spent off the goal adds
`log 10 - log (10/9) = log 9`. -/
theorem chain2_beats_chain3 :
    Real.log 10 + 2 * Real.log (10 / 9) < 2 * Real.log 10 + Real.log (10 / 9) := by
  have : Real.log (10 / 9) < Real.log 10 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

end
end DarkTower.WarMachine.CascadeScoringExamples
