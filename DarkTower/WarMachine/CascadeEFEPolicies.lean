import DarkTower.WarMachine.CascadeEFE

/-! Admissible cascade policy priors and model-derived controls.
No posterior inference or live-machine correspondence is asserted. -/
namespace DarkTower.WarMachine.CascadeEFEPolicies
open Holes CascadeEFE
open scoped BigOperators
noncomputable section

/-- Holes.lean's zaifAuthored docstring (line 1102 at 480a666ad2) states
`u stands on v`; organise O2 preserves this orientation through Reach
(Holes organiseO2AuthoredReachability; F12RuledCarrier.ConformantOrganiseRuled.o2).
Thus v must precede u. Pairwise checks every later/earlier pair, including
transitive descent, and never interprets a temperament's non-node entries as actions. -/
def Admissible {P : Type*} (pi : Policy P) : Prop :=
  (firing pi).Pairwise (fun earlier later => ¬ Reach pi.cascade.edges earlier later)

/-- Finite duplicate-free policies with successful canonical scores. A refused
score cannot inhabit this candidate family. -/
structure CandidateFamily {P S O : Type*} [Fintype S] [Fintype O] [DecidableEq S]
    (m : Model P S O) (T : ℕ) (c : Fin T → ProbabilityKernel Unit O) where
  policies : List (Policy P)
  nodup : policies.Nodup
  nonempty : policies ≠ []
  admissible : ∀ pi ∈ policies, Admissible pi
  value : Policy P → ℝ
  scored : ∀ pi ∈ policies, scoreCascade m pi T c = .ok (value pi)

abbrev CandidateFamily.index {P S O : Type*} [Fintype S] [Fintype O] [DecidableEq S]
    {m : Model P S O} {T : ℕ} {c : Fin T → ProbabilityKernel Unit O}
    (f : CandidateFamily m T c) := Fin f.policies.length

theorem refused_not_candidate {P S O : Type*} [Fintype S] [Fintype O] [DecidableEq S]
    {m : Model P S O} {T : ℕ} {c : Fin T → ProbabilityKernel Unit O}
    (f : CandidateFamily m T c) (pi : Policy P) (r : Refusal)
    (h : scoreCascade m pi T c = .error r) : pi ∉ f.policies := by
  intro hp
  have hs := f.scored pi hp
  rw [h] at hs
  cases hs

variable {I : Type*} [Fintype I]

def partition (logit : I → ℝ) : ℝ := ∑ i, Real.exp (logit i)
def prior (logit : I → ℝ) (i : I) : ℝ := Real.exp (logit i) / partition logit

theorem partition_positive [Nonempty I] (l : I → ℝ) : 0 < partition l := by
  classical
  exact Finset.sum_pos (fun i _ => Real.exp_pos (l i)) Finset.univ_nonempty

theorem prior_normalised [Nonempty I] (l : I → ℝ) : ∑ i, prior l i = 1 := by
  simp only [prior, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_positive l))

theorem prior_positive [Nonempty I] (l : I → ℝ) (i : I) : 0 < prior l i :=
  div_pos (Real.exp_pos _) (partition_positive l)

theorem prior_order [Nonempty I] (l : I → ℝ) (i j : I) (h : l j < l i) :
    prior l j < prior l i :=
  (div_lt_div_iff_of_pos_right (partition_positive l)).mpr (Real.exp_lt_exp.mpr h)

inductive PriorForm where
  | base | habit | precision | habitPrecision
  deriving DecidableEq

/-- habitPrecision is the labelled combination of B.7 and B.13, not a claim
that the book's observed-data posterior omits F. -/
def logits (form : PriorForm) (G E : I → ℝ) (gamma : ℝ) (i : I) : ℝ :=
  match form with
  | .base => -G i
  | .habit => Real.log (E i) - G i
  | .precision => -gamma * G i
  | .habitPrecision => Real.log (E i) - gamma * G i

theorem four_priors [Nonempty I] (form : PriorForm) (G E : I → ℝ)
    (_hE : ∀ i, 0 < E i) (gamma : ℝ) (_hg : 0 < gamma) :
    0 < partition (logits form G E gamma) ∧
    (∑ i, prior (logits form G E gamma) i) = 1 :=
  ⟨partition_positive _, prior_normalised _⟩

theorem lower_G_higher_prior [Nonempty I] (form : PriorForm) (G E : I → ℝ)
    (_hE : ∀ i, 0 < E i) (gamma : ℝ) (hg : 0 < gamma)
    (i j : I) (heq : E i = E j) (hG : G i < G j) :
    prior (logits form G E gamma) j < prior (logits form G E gamma) i := by
  apply prior_order
  have hm := mul_lt_mul_of_pos_left hG hg
  cases form <;> simp only [logits, heq] <;> linarith

def familyLogits {P S O : Type*} [Fintype S] [Fintype O] [DecidableEq S]
    {m : Model P S O} {T : ℕ} {c : Fin T → ProbabilityKernel Unit O}
    (f : CandidateFamily m T c) (form : PriorForm) (E : f.index → ℝ) (gamma : ℝ) :
    f.index → ℝ := logits form (fun i => f.value (f.policies.get i)) E gamma

theorem family_priors {P S O : Type*} [Fintype S] [Fintype O] [DecidableEq S]
    {m : Model P S O} {T : ℕ} {c : Fin T → ProbabilityKernel Unit O}
    (f : CandidateFamily m T c) (form : PriorForm) (E : f.index → ℝ)
    (hE : ∀ i, 0 < E i) (gamma : ℝ) (hg : 0 < gamma) :
    0 < partition (familyLogits f form E gamma) ∧
    (∑ i, prior (familyLogits f form E gamma) i) = 1 := by
  have hl : 0 < f.policies.length := List.length_pos_iff.mpr f.nonempty
  letI : NeZero f.policies.length := ⟨by omega⟩
  exact four_priors form _ E hE gamma hg

/-- Empty descent has no dependencies; used for the controls, not to remove
edges from supplied policies. -/
theorem noReach {P : Type*} (x y : P) : ¬ Reach (fun _ _ : P => False) x y := by
  intro h
  induction h with
  | single h => exact h
  | tail _ h => exact h

def twoPolicy (first : Bool) : Policy Bool where
  cascade := {
    nodes := Set.univ
    addedByOrganise := ∅
    edges := fun _ _ => False
    acyclic := fun x => noReach x x
    precedence := [first, !first] }
  nodeDecidable := fun _ => isTrue trivial

theorem twoPolicy_admissible (b : Bool) : Admissible (twoPolicy b) := by
  simp [Admissible, firing, twoPolicy, noReach]

theorem twoPolicy_same_nodes : (twoPolicy true).cascade.nodes = (twoPolicy false).cascade.nodes := rfl

def deterministic {S : Type*} [Fintype S] [DecidableEq S] (f : S → S) : ProbabilityKernel S S :=
  finiteKernel (fun s t => if t = f s then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro; simp)

/-- State is (has-applied-p, has-applied-q, shared-bit). Both patterns write
shared-bit: p sets it true, q negates it. Each guard prevents repeat execution. -/
abbrev SharedState := Bool × Bool × Bool

def sharedUpdate (p : Bool) (s : SharedState) : SharedState :=
  if p then (true, s.2.1, true) else (s.1, true, !s.2.2)

def sharedModel : Model Bool SharedState Bool where
  initial := point (false, false, false)
  observation := finiteKernel (fun s o => if o = s.2.2 then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro; simp)
  guard := fun p s => if p then !s.1 else !s.2.1
  interpretation := fun p => some (deterministic (sharedUpdate p))

def boolPreference : ProbabilityKernel Unit Bool :=
  finiteKernel (fun _ o => if o then 3/4 else 1/4)
    (by intro _ o; cases o <;> norm_num)
    (by intro; simp; norm_num)

/-- Kernel extracted only after the explicit successful resolution proof. -/
def sharedKernel (first : Bool) : ProbabilityKernel SharedState SharedState :=
  let row := fun s => choose sharedModel
    [(first, deterministic (sharedUpdate first)), (!first, deterministic (sharedUpdate (!first)))] s
  { support := fun s => (row s).support ()
    mass := fun s => (row s).mass ()
    nonnegative := fun s => (row s).nonnegative ()
    normalised := fun s => (row s).normalised ()
    support_nodup := fun s => (row s).support_nodup ()
    mass_eq_zero_of_not_mem := fun s => (row s).mass_eq_zero_of_not_mem () }

theorem sharedKernel_resolved (first : Bool) :
    policyKernel sharedModel (twoPolicy first) = some (sharedKernel first) := by
  cases first <;> rfl

theorem shared_prediction_one (first : Bool) (s : SharedState) :
    (prediction sharedModel.initial (sharedKernel first) 1).mass () s =
      if s = (if first then (true,false,true) else (false,true,true)) then 1 else 0 := by
  cases first <;>
    simp [prediction, push, finiteKernel, sharedModel, point, sharedKernel,
      choose, deterministic, sharedUpdate]

theorem shared_prediction_two (first : Bool) (s : SharedState) :
    (prediction sharedModel.initial (sharedKernel first) 2).mass () s =
      if s = (true,true,!first) then 1 else 0 := by
  change (∑ x, (prediction sharedModel.initial (sharedKernel first) 1).mass () x *
    (sharedKernel first).mass x s) = _
  simp_rw [shared_prediction_one]
  cases first <;>
    simp [sharedKernel, choose, deterministic, sharedUpdate, sharedModel, finiteKernel, point]

/-- Both orders predict true first; the shared-state interaction changes the
second prediction. These are derived from the selected transition kernels. -/
theorem shared_outcome_one (first o : Bool) :
    (push (prediction sharedModel.initial (sharedKernel first) 1) sharedModel.observation).mass () o =
      if o = true then 1 else 0 := by
  change (∑ s, (prediction sharedModel.initial (sharedKernel first) 1).mass () s *
    sharedModel.observation.mass s o) = _
  simp_rw [shared_prediction_one]
  cases first <;> cases o <;> norm_num [sharedModel, finiteKernel, Fintype.sum_prod_type] <;> decide

theorem shared_outcome_two (first o : Bool) :
    (push (prediction sharedModel.initial (sharedKernel first) 2) sharedModel.observation).mass () o =
      if o = !first then 1 else 0 := by
  change (∑ s, (prediction sharedModel.initial (sharedKernel first) 2).mass () s *
    sharedModel.observation.mass s o) = _
  simp_rw [shared_prediction_two]
  cases first <;> cases o <;> norm_num [sharedModel, finiteKernel, Fintype.sum_prod_type] <;> decide

theorem shared_admitted (first : Bool) (t : Fin 2) :
    PreferenceRiskSeparation.riskAdmissible
      (push (prediction sharedModel.initial (sharedKernel first) (t.val + 1)) sharedModel.observation)
      boolPreference := by
  intro _ o _ _
  cases o <;> norm_num [boolPreference, finiteKernel]

def sharedG (first : Bool) : ℝ :=
  totalG sharedModel.initial (sharedKernel first) sharedModel.observation 2
    (fun _ => boolPreference) (shared_admitted first)

theorem shared_ambiguity_zero (q : ProbabilityKernel Unit SharedState) :
    CascadeEFE.ambiguity q sharedModel.observation = 0 := by
  unfold CascadeEFE.ambiguity
  have ha (s : SharedState) : entropy (sharedModel.observation.mass s) = 0 := by
    simp [entropy, sharedModel, finiteKernel]
  simp [ha]

theorem sharedG_computed (first : Bool) :
    sharedG first = Real.log (4/3) + (if first then Real.log 4 else Real.log (4/3)) := by
  unfold sharedG totalG
  rw [Fin.sum_univ_two]
  simp only [stepG, risk, shared_ambiguity_zero, add_zero]
  simp only [show (0 : Fin 2).val + 1 = 1 from rfl, show (1 : Fin 2).val + 1 = 2 from rfl,
    shared_outcome_one, shared_outcome_two]
  cases first <;> norm_num [klTerm, boolPreference, finiteKernel]

theorem composition_outcomes_differ :
    (push (prediction sharedModel.initial (sharedKernel true) 2) sharedModel.observation).mass () ≠
    (push (prediction sharedModel.initial (sharedKernel false) 2) sharedModel.observation).mass () := by
  intro h
  have hh := congrFun h true
  simp [shared_outcome_two] at hh

theorem composition_G_differs : sharedG true ≠ sharedG false := by
  rw [sharedG_computed, sharedG_computed]
  simp only [Bool.false_eq_true, if_false, if_true]
  have hl : Real.log (4/3 : ℝ) < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- Two independent factors, initially false. Each guarded rule sets its own
factor true once and leaves the other unchanged. Observation is symmetric XOR;
preferences are identical at corresponding times. These are the explicit
conditions of this control, not a conclusion from commutation alone. -/
def independentUpdate (p : Bool) (s : Bool × Bool) : Bool × Bool :=
  if p then (true, s.2) else (s.1, true)

theorem independent_scopes (s : Bool × Bool) :
    (independentUpdate true s).2 = s.2 ∧ (independentUpdate false s).1 = s.1 := by
  simp [independentUpdate]

theorem independent_commutes (s : Bool × Bool) :
    independentUpdate true (independentUpdate false s) =
    independentUpdate false (independentUpdate true s) := by simp [independentUpdate]

/-- The joint transition factors into the changed-coordinate point law and
identity on the other factor, derived from the update, not postulated. -/
theorem independent_transition_product (s t : Bool × Bool) :
    (deterministic (independentUpdate true)).mass s t =
      (point true).mass () t.1 * (point s.2).mass () t.2 ∧
    (deterministic (independentUpdate false)).mass s t =
      (point s.1).mass () t.1 * (point true).mass () t.2 := by
  rcases s with ⟨s1,s2⟩; rcases t with ⟨t1,t2⟩
  cases s1 <;> cases s2 <;> cases t1 <;> cases t2 <;>
    norm_num [deterministic, independentUpdate, point, finiteKernel]

def independentModel : Model Bool (Bool × Bool) Bool where
  initial := point (false,false)
  observation := finiteKernel (fun s o => if o = Bool.xor s.1 s.2 then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro; simp)
  guard := fun p s => if p then !s.1 else !s.2
  interpretation := fun p => some (deterministic (independentUpdate p))

def independentKernel (first : Bool) : ProbabilityKernel (Bool × Bool) (Bool × Bool) :=
  let row := fun s => choose independentModel
    [(first, deterministic (independentUpdate first)), (!first, deterministic (independentUpdate (!first)))] s
  { support := fun s => (row s).support ()
    mass := fun s => (row s).mass ()
    nonnegative := fun s => (row s).nonnegative ()
    normalised := fun s => (row s).normalised ()
    support_nodup := fun s => (row s).support_nodup ()
    mass_eq_zero_of_not_mem := fun s => (row s).mass_eq_zero_of_not_mem () }

theorem independentKernel_resolved (first : Bool) :
    policyKernel independentModel (twoPolicy first) = some (independentKernel first) := by
  cases first <;> rfl

theorem independent_prediction_one (first : Bool) (s : Bool × Bool) :
    (prediction independentModel.initial (independentKernel first) 1).mass () s =
      if s = (first, !first) then 1 else 0 := by
  cases first <;> simp [prediction, push, independentModel, independentKernel, choose,
    point, deterministic, independentUpdate, finiteKernel]

theorem independent_prediction_two (first : Bool) (s : Bool × Bool) :
    (prediction independentModel.initial (independentKernel first) 2).mass () s =
      if s = (true,true) then 1 else 0 := by
  change (∑ x, (prediction independentModel.initial (independentKernel first) 1).mass () x *
    (independentKernel first).mass x s) = _
  simp_rw [independent_prediction_one]
  cases first <;> simp [independentModel, independentKernel, choose,
    point, deterministic, independentUpdate, finiteKernel]

theorem independent_outcome_one (first o : Bool) :
    (push (prediction independentModel.initial (independentKernel first) 1) independentModel.observation).mass () o =
      if o = true then 1 else 0 := by
  change (∑ s, (prediction independentModel.initial (independentKernel first) 1).mass () s *
    independentModel.observation.mass s o) = _
  simp_rw [independent_prediction_one]
  cases first <;> cases o <;> norm_num [independentModel, finiteKernel, Fintype.sum_prod_type]

theorem independent_outcome_two (first o : Bool) :
    (push (prediction independentModel.initial (independentKernel first) 2) independentModel.observation).mass () o =
      if o = false then 1 else 0 := by
  change (∑ s, (prediction independentModel.initial (independentKernel first) 2).mass () s *
    independentModel.observation.mass s o) = _
  simp_rw [independent_prediction_two]
  cases o <;> norm_num [independentModel, finiteKernel, Fintype.sum_prod_type]

theorem independent_ambiguity_zero (q : ProbabilityKernel Unit (Bool × Bool)) :
    CascadeEFE.ambiguity q independentModel.observation = 0 := by
  unfold CascadeEFE.ambiguity
  have ha (s : Bool × Bool) : entropy (independentModel.observation.mass s) = 0 := by
    simp [entropy, independentModel, finiteKernel]
  simp [ha]

theorem independent_per_step (t : Fin 2) :
    (push (prediction independentModel.initial (independentKernel true) (t.val+1)) independentModel.observation).mass () =
      (push (prediction independentModel.initial (independentKernel false) (t.val+1)) independentModel.observation).mass () ∧
    CascadeEFE.ambiguity (prediction independentModel.initial (independentKernel true) (t.val+1)) independentModel.observation =
      CascadeEFE.ambiguity (prediction independentModel.initial (independentKernel false) (t.val+1)) independentModel.observation := by
  constructor
  · funext o
    fin_cases t <;> simp [independent_outcome_one, independent_outcome_two]
  · simp [independent_ambiguity_zero]

theorem independent_admitted (first : Bool) (t : Fin 2) :
    PreferenceRiskSeparation.riskAdmissible
      (push (prediction independentModel.initial (independentKernel first) (t.val+1)) independentModel.observation)
      boolPreference := by
  intro _ o _ _; cases o <;> norm_num [boolPreference, finiteKernel]

def independentG (first : Bool) : ℝ :=
  totalG independentModel.initial (independentKernel first) independentModel.observation 2
    (fun _ => boolPreference) (independent_admitted first)

theorem independent_G_equal : independentG true = independentG false := by
  unfold independentG totalG
  apply Finset.sum_congr rfl
  intro t _
  obtain ⟨ho, ha⟩ := independent_per_step t
  simp only [stepG, risk]
  rw [ho, ha]

def singletonPolicy : Policy Unit where
  cascade := {
    nodes := Set.univ
    addedByOrganise := ∅
    edges := fun _ _ => False
    acyclic := fun x => noReach x x
    precedence := [()] }
  nodeDecidable := fun _ => isTrue trivial

theorem singleton_admissible : Admissible singletonPolicy := by
  simp [Admissible, singletonPolicy, firing]

def singletonModel {S O : Type*} (q : ProbabilityKernel Unit S)
    (a : ProbabilityKernel S O) (b : ProbabilityKernel S S) : Model Unit S O :=
  ⟨q, a, fun _ _ => true, fun _ => some b⟩

theorem singleton_resolved {S O : Type*} [Fintype S] [DecidableEq S]
    (q : ProbabilityKernel Unit S) (a : ProbabilityKernel S O) (b : ProbabilityKernel S S) :
    policyKernel (singletonModel q a b) singletonPolicy = some b := rfl

theorem singleton_reduction {S O : Type*} [Fintype S] [Fintype O] [DecidableEq S]
    (q : ProbabilityKernel Unit S) (a : ProbabilityKernel S O) (b : ProbabilityKernel S S)
    (c : ProbabilityKernel Unit O)
    (h : PreferenceRiskSeparation.riskAdmissible (push (prediction q b 1) a) c) :
    scoreCascade (singletonModel q a b) singletonPolicy 1 (fun _ => c) =
      .ok (stepG (prediction q b 1) a c h) := by
  have hh : ∀ t : Fin 1, PreferenceRiskSeparation.riskAdmissible
      (push (prediction q b (t.val+1)) a) c := by intro t; fin_cases t; exact h
  unfold scoreCascade
  rw [singleton_resolved]
  dsimp only [singletonModel]
  rw [dif_pos hh]
  simp [totalG]

theorem shared_score (first : Bool) :
    scoreCascade sharedModel (twoPolicy first) 2 (fun _ => boolPreference) = .ok (sharedG first) := by
  unfold scoreCascade
  rw [sharedKernel_resolved]
  simp [shared_admitted, sharedG]

/-- Same nodes, legal distinct precedence, shared-state interaction, different
predicted outcomes and canonical scores. No arbitrary G values are supplied. -/
theorem composition_control :
    Admissible (twoPolicy true) ∧ Admissible (twoPolicy false) ∧
    (twoPolicy true).cascade.nodes = (twoPolicy false).cascade.nodes ∧
    (twoPolicy true).cascade.precedence ≠ (twoPolicy false).cascade.precedence ∧
    scoreCascade sharedModel (twoPolicy true) 2 (fun _ => boolPreference) = .ok (sharedG true) ∧
    scoreCascade sharedModel (twoPolicy false) 2 (fun _ => boolPreference) = .ok (sharedG false) ∧
    sharedG true ≠ sharedG false := by
  exact ⟨twoPolicy_admissible _, twoPolicy_admissible _, rfl, by decide,
    shared_score _, shared_score _, composition_G_differs⟩

theorem independent_score (first : Bool) :
    scoreCascade independentModel (twoPolicy first) 2 (fun _ => boolPreference) = .ok (independentG first) := by
  unfold scoreCascade
  rw [independentKernel_resolved]
  simp [independent_admitted, independentG]

-- Exact signatures and axiom reports retained by the build log.
#check refused_not_candidate
#print axioms refused_not_candidate
#check partition_positive
#print axioms partition_positive
#check prior_normalised
#print axioms prior_normalised
#check prior_positive
#print axioms prior_positive
#check prior_order
#print axioms prior_order
#check four_priors
#print axioms four_priors
#check lower_G_higher_prior
#print axioms lower_G_higher_prior
#check family_priors
#print axioms family_priors
#check noReach
#print axioms noReach
#check twoPolicy_admissible
#print axioms twoPolicy_admissible
#check twoPolicy_same_nodes
#print axioms twoPolicy_same_nodes
#check sharedKernel_resolved
#print axioms sharedKernel_resolved
#check shared_prediction_one
#print axioms shared_prediction_one
#check shared_prediction_two
#print axioms shared_prediction_two
#check shared_outcome_one
#print axioms shared_outcome_one
#check shared_outcome_two
#print axioms shared_outcome_two
#check shared_admitted
#print axioms shared_admitted
#check shared_ambiguity_zero
#print axioms shared_ambiguity_zero
#check sharedG_computed
#print axioms sharedG_computed
#check composition_outcomes_differ
#print axioms composition_outcomes_differ
#check composition_G_differs
#print axioms composition_G_differs
#check independent_scopes
#print axioms independent_scopes
#check independent_commutes
#print axioms independent_commutes
#check independent_transition_product
#print axioms independent_transition_product
#check independentKernel_resolved
#print axioms independentKernel_resolved
#check independent_prediction_one
#print axioms independent_prediction_one
#check independent_prediction_two
#print axioms independent_prediction_two
#check independent_outcome_one
#print axioms independent_outcome_one
#check independent_outcome_two
#print axioms independent_outcome_two
#check independent_ambiguity_zero
#print axioms independent_ambiguity_zero
#check independent_per_step
#print axioms independent_per_step
#check independent_admitted
#print axioms independent_admitted
#check independent_G_equal
#print axioms independent_G_equal
#check singleton_admissible
#print axioms singleton_admissible
#check singleton_resolved
#print axioms singleton_resolved
#check singleton_reduction
#print axioms singleton_reduction
#check shared_score
#print axioms shared_score
#check composition_control
#print axioms composition_control
#check independent_score
#print axioms independent_score

end
end DarkTower.WarMachine.CascadeEFEPolicies
