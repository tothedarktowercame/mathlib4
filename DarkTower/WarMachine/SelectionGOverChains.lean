import DarkTower.WarMachine.SelectionGOverCascades

/-!
# Selection G over chains

SPECIFICATION DIRECTION (WM hardening package 6, 2026-11-13; requisition from
`futon2/holes/labs/H-wm-ladder-lucy-handoff-2026-11-13.md` §4).  The Clojure
scorer `futon2.aif.selection-canonical-g` gained chains at commit `ca062096f`;
this module extends `SelectionGOverCascades` (the single-pick spec) so the Lean
spec describes what the scorer computes:

- a unit is (pattern, pick) — every distinct pattern of the cascade applied on
  every pick of the chain (`candidate` in the Clojure);
- a unit on pick `k > 0` additionally requires the previous pick's `canBegin`
  (`[pick(k-1) :can-begin]`), so a later pick's patterns fire only once the
  earlier pick can begin;
- tokens are target-qualified (pick-index-qualified here; equivalent because
  two candidates reading the same target read the same facts) in one shared
  state, here the union of the picks' whole-task facts;
- the observation is the FIRST pick's class once its `canBegin` holds,
  `notYetEvaluated` before, `stopTheLine` with no pick (stopping is the empty
  policy: no patterns, no novelty);
- pattern counts are per pattern along the chain (commit `ca062096f`): a
  pattern's unit on pick `k` starts from Beta(1 + n, 1), `n` = its firings on
  earlier picks of the same chain; a one-pick cascade keeps Beta(1,1), so its
  G is unchanged (`chainCounts_one_pick`).

The acceptance case (`ladder_ordering`) is the Clojure test
`a-repeated-pattern-is-less-novel-than-a-second-pattern` (Lucy 2026-11-13,
wm-click-3e072695, field 09/10): two patterns once each < one pattern twice <
one pattern once.  `ladder_bad_case` shows the old Beta(1,1)-per-unit model
ties the first two, which is the defect `ca062096f` fixed.

NOT PROVED HERE (see the report): the one-pick agreement
`chainG = SelectionGOverCascades.selectionG` at the level of full G.  The two
candidates live on different token types (`Fin 1 × SelectionToken` vs
`SelectionToken`), and the substrate has no transport theorem for
`scoreCascadeCoN` under a token-type equivalence; the count agreement and the
deterministic dynamics are proved (`chainCounts_one_pick`, `prediction_point`),
which is what the count change needed.
-/

namespace DarkTower.WarMachine.SelectionGOverChains

open DarkTower.WarMachine
open CascadeEFE CascadeTransition CascadeCoApplyG CascadeCoApplyGNovelty
open PatternThetaNovelty
open Proof2.ContainmentOrder Proof2.CoApplicationKernel Holes
open R20Step SelectionGOverCascades

noncomputable section

/-! ## Deterministic co-application at θ = 1 -/

section Deterministic

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- One deterministic co-application step: the state state gains every produce of the
enabled frontier. -/
def coStep (pat : ι → InterpretedPattern V) (s : Finset V) : Finset V :=
  s ∪ (enabledFrontier pat (containmentOrder pat) s).biUnion (fun p => (pat p).produces)

/-- The deterministic trajectory from `s0` (θ = 1 for every pattern). -/
def coTraj (pat : ι → InterpretedPattern V) (s0 : Finset V) : ℕ → Finset V
  | 0 => s0
  | t + 1 => coStep pat (coTraj pat s0 t)

/-- With every θ equal to 1 the co-application kernel is the point step. -/
theorem coApplyKernel_one (pat : ι → InterpretedPattern V)
    (hθ : ∀ p, (pat p).theta = 1) (s s' : Finset V) :
    coApplyKernel pat (containmentOrder pat) s s' =
      if s' = coStep pat s then 1 else 0 := by
  classical
  have hmem : enabledFrontier pat (containmentOrder pat) s ∈
      (enabledFrontier pat (containmentOrder pat) s).powerset :=
    Finset.mem_powerset.2 (by simp)
  have hothers : ∀ S ∈ (enabledFrontier pat (containmentOrder pat) s).powerset,
      S ≠ enabledFrontier pat (containmentOrder pat) s →
      ((∏ p ∈ S, (pat p).theta) *
        ∏ p ∈ enabledFrontier pat (containmentOrder pat) s \ S, (1 - (pat p).theta)) *
      (if s' = s ∪ S.biUnion (fun p => (pat p).produces) then 1 else 0) = 0 := by
    intro S _ hS
    have hsub : S ⊆ enabledFrontier pat (containmentOrder pat) s := Finset.mem_powerset.1 ‹_›
    have hne : (enabledFrontier pat (containmentOrder pat) s \ S).Nonempty := by
      by_contra hempty
      have hle : enabledFrontier pat (containmentOrder pat) s \ S = ∅ :=
        Finset.not_nonempty_iff_eq_empty.1 hempty
      have hsub' : enabledFrontier pat (containmentOrder pat) s ⊆ S := by
        simpa using hle
      exact hS (hsub.antisymm hsub')
    obtain ⟨p, hp⟩ := hne
    have hzero : ∏ q ∈ enabledFrontier pat (containmentOrder pat) s \ S, (1 - (pat q).theta)
        = 0 := Finset.prod_eq_zero hp (by simp [hθ p])
    simp only [hzero, zero_mul, mul_zero]
  unfold coApplyKernel coStep
  rw [Finset.sum_eq_single (enabledFrontier pat (containmentOrder pat) s) hothers
      (by simpa using hmem)]
  rw [Finset.sdiff_self, Finset.prod_empty, Finset.prod_eq_one (fun p _ => hθ p),
    one_mul, one_mul]

/-- The push of a point-massed kernel reads only the point's row. -/
theorem push_pointMass {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (q : ProbabilityKernel Unit X) (b : ProbabilityKernel X Y) (T : X)
    (hq : ∀ s, q.mass () s = if s = T then 1 else 0) (o : Y) :
    (push q b).mass () o = b.mass T o := by
  unfold push finiteKernel
  simp only [hq, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- With every θ = 1, prediction from a point mass stays a point mass on the
deterministic trajectory. -/
theorem prediction_point (pat : ι → InterpretedPattern V)
    (hθ : ∀ p, (pat p).theta = 1) (s0 : Finset V) :
    ∀ (t : ℕ) (s : Finset V),
    (prediction (point s0) (coKernel pat) t).mass () s =
      if s = coTraj pat s0 t then 1 else 0 := by
  intro t
  induction t with
  | zero => intro s; simp [prediction, point, finiteKernel, coTraj]
  | succ t ih =>
      intro s
      unfold prediction coTraj
      rw [push_pointMass _ _ _ ih]
      simp only [coKernel, finiteKernel]
      rw [coApplyKernel_one pat hθ]

/-- Expected novelty from a point mass is the frontier sum at the trajectory
state. -/
theorem expectedNovelty_point (pat : ι → InterpretedPattern V)
    (hθ : ∀ p, (pat p).theta = 1) (counts : ι → ℝ × ℝ) (s0 : Finset V) (tau : ℕ) :
    expectedNovelty pat counts (point s0) tau =
      ∑ p ∈ enabledFrontier pat (containmentOrder pat) (coTraj pat s0 tau),
        novelty (counts p).1 (counts p).2 := by
  unfold expectedNovelty
  simp only [prediction_point pat hθ s0 tau, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Deterministic

/-! ## The chain model

Clojure `futon2.aif.selection-canonical-g` after `ca062096f`: a menu entry may
carry `:picks`, an ordered chain; its first pick is what the click enacts.  A
unit is (pattern, pick); a unit on pick `k > 0` additionally requires the
previous pick's `canBegin`; tokens are target-qualified (here: pick-index
qualified, which is equivalent because two candidates reading the same target
read the same facts); the observation is the FIRST pick's class once its
`canBegin` holds.  Pattern counts are per pattern along the chain: a pattern's
unit on pick `k` starts from Beta(1 + n, 1) where `n` counts its firings on
earlier picks of the same chain.
-/

section Model

open DarkTower.WarMachine.SelectionGOverCascades.SelectionToken

/-- Target-qualified tokens: pick index × token (`[target token]` in the
Clojure). -/
abbrev ChainToken (n : ℕ) := Fin n × SelectionToken

/-- `tag` in the Clojure: qualify a token by its pick. -/
def tagTok {n : ℕ} (k : Fin n) (t : SelectionToken) : ChainToken n := (k, t)

/-- A set of tokens, all qualified by the same pick. -/
def tagSet {n : ℕ} (k : Fin n) (S : Finset SelectionToken) : Finset (ChainToken n) :=
  S.image (tagTok k)

/-- The extra guard of a unit on pick `k > 0`: the previous pick can begin
(`[pick(k-1) :can-begin]`). -/
def prevGuard {n : ℕ} : (k : Fin n) → Finset (ChainToken n)
  | ⟨0, _⟩ => ∅
  | ⟨j + 1, h⟩ => {tagTok ⟨j, Nat.lt_of_succ_lt h⟩ canBegin}

/-- One unit: pattern `i` of the policy, applied on pick `k`. -/
def unitPattern (pats : List SelectionPattern) {n : ℕ} (i : Fin pats.length) (k : Fin n) :
    InterpretedPattern (ChainToken n) where
  consumes := tagSet k (interpret (pats.get i)).consumes ∪ prevGuard k
  produces := tagSet k (interpret (pats.get i)).produces
  forbids := tagSet k (interpret (pats.get i)).forbids
  theta := 1
  theta_nonneg := by norm_num
  theta_le_one := le_refl _

/-- The unit family of a chain policy: every pattern on every pick. -/
def chainFam (pats : List SelectionPattern) (picks : List Target) :
    Fin pats.length × Fin picks.length → InterpretedPattern (ChainToken picks.length)
  | (i, k) => unitPattern pats i k

/-- The whole-task facts of every pick, each tagged by its pick index
(the Clojure's shared state restricted to this candidate's targets). -/
def chainInitial (picks : List Target) (facts : Target → SelectionFacts) :
    Finset (ChainToken picks.length) :=
  Finset.univ.biUnion (fun k => tagSet k (initialTokens (facts (picks.get k))))

/-- The class observed for the FIRST pick once it can begin; `notYetEvaluated`
before that, and always, when there is no pick at all. -/
def chainObsClass {n : ℕ} (ending : CTauClassPreference.EndingClass)
    (s : Finset (ChainToken n)) : CTauClassPreference.EndingClass :=
  if h : 0 < n then if tagTok ⟨0, h⟩ canBegin ∈ s then ending else .notYetEvaluated
  else .notYetEvaluated

def chainObservationKernel {n : ℕ} (ending : CTauClassPreference.EndingClass) :
    ProbabilityKernel (Finset (ChainToken n)) CTauClassPreference.EndingClass :=
  finiteKernel (fun s e => if chainObsClass ending s = e then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro s; simp)

/-- A unit fired along the deterministic trajectory (θ = 1 throughout). -/
def firedOn {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (fam : ι → InterpretedPattern V) (s0 : Finset V) (u : ι) : Prop :=
  ∃ t : ℕ, guard (fam u) (coTraj fam s0 t)

open Classical in
/-- How often pattern `i` fired on picks before `k`. -/
def earlierFires (pats : List SelectionPattern) (picks : List Target)
    (facts : Target → SelectionFacts) (i : Fin pats.length) (k : Fin picks.length) : ℕ :=
  ((Finset.univ : Finset (Fin picks.length)).filter
    (fun j : Fin picks.length => (j : ℕ) < (k : ℕ) ∧
      firedOn (chainFam pats picks) (chainInitial picks facts) (i, j))).card

/-- Per-pattern counts along the chain: Beta(1 + n, 1), n = firings on earlier
picks of the same chain. -/
def chainCounts (pats : List SelectionPattern) (picks : List Target)
    (facts : Target → SelectionFacts) :
    Fin pats.length × Fin picks.length → ℝ × ℝ :=
  fun u => (1 + earlierFires pats picks facts u.1 u.2, 1)

/-- The canonical candidate of a chain policy: the first pick is what the click
enacts (`ending` is its class; `.stopTheLine` with no pick). -/
def chainCandidate (pats : List SelectionPattern) (picks : List Target)
    (facts : Target → SelectionFacts) (ending : CTauClassPreference.EndingClass) :
    CascadeCoApplyGNovelty.CandidateN
      (Fin pats.length × Fin picks.length) (ChainToken picks.length) :=
  { patterns := some (chainFam pats picks)
    initial := point (chainInitial picks facts)
    observation := chainObservationKernel ending
    counts := chainCounts pats picks facts
    counts_pos := fun _ => ⟨by simp only [chainCounts]; positivity,
      by simp only [chainCounts]; norm_num⟩ }

/-- Chain-selection G: the canonical cascade G of the chain candidate. -/
def chainG (pats : List SelectionPattern) (picks : List Target)
    (facts : Target → SelectionFacts) (ending : CTauClassPreference.EndingClass)
    (H : ℕ) (c : Fin H → ProbabilityKernel Unit CTauClassPreference.EndingClass) :
    Except CascadeCoApplyG.Refusal ℝ :=
  GOverCascades.cascadeGrainG (chainCandidate pats picks facts ending) H c

theorem chainFam_theta_one (pats : List SelectionPattern) (picks : List Target)
    (u : Fin pats.length × Fin picks.length) : (chainFam pats picks u).theta = 1 := by
  rfl

end Model

/-! ## Structural lemmas -/

section Lemmas

open DarkTower.WarMachine.SelectionGOverCascades.SelectionToken

variable {n : ℕ}

/-- Tagged sets from different picks are disjoint; from one pick they meet iff
the token sets meet. -/
theorem tagSet_inter_nonempty (k k' : Fin n) (A B : Finset SelectionToken) :
    (tagSet k A ∩ tagSet k' B).Nonempty ↔ k = k' ∧ (A ∩ B).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨t, ht, hx1⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).1
    obtain ⟨t', ht', hx2⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).2
    have hkk : k = k' := congrArg Prod.fst (hx1.trans hx2.symm)
    subst hkk
    have htt : t = t' := congrArg Prod.snd (hx1.trans hx2.symm)
    exact ⟨rfl, t, Finset.mem_inter.2 ⟨ht, htt ▸ ht'⟩⟩
  · rintro ⟨rfl, ⟨t, ht⟩⟩
    exact ⟨tagTok k t, Finset.mem_inter.2
      ⟨Finset.mem_image.2 ⟨t, (Finset.mem_inter.1 ht).1, rfl⟩,
        Finset.mem_image.2 ⟨t, (Finset.mem_inter.1 ht).2, rfl⟩⟩⟩

end Lemmas

/-! ## One-pick chains keep Beta(1,1) -/

section OnePick

open DarkTower.WarMachine.SelectionGOverCascades.SelectionToken

theorem fin1_eq_zero (k : Fin 1) : k = 0 := by
  obtain ⟨v, hv⟩ := k
  cases v with
  | zero => rfl
  | succ w => omega

open Classical in
/-- No earlier pick than the first. -/
theorem earlierFires_zero_pick (pats : List SelectionPattern) (picks : List Target)
    (facts : Target → SelectionFacts) (i : Fin pats.length) {k : Fin picks.length}
    (hk : (k : ℕ) = 0) : earlierFires pats picks facts i k = 0 := by
  unfold earlierFires
  have hfilter : ((Finset.univ : Finset (Fin picks.length)).filter
      (fun j : Fin picks.length => (j : ℕ) < (k : ℕ) ∧
        firedOn (chainFam pats picks) (chainInitial picks facts) (i, j))) = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [hk]
  rw [hfilter, Finset.card_empty]

/-- A unit on the first pick has no earlier pick, so its counts stay
Beta(1,1): a single-pick cascade is scored exactly as before `ca062096f`. -/
theorem chainCounts_one_pick (pats : List SelectionPattern) (picks : List Target)
    (facts : Target → SelectionFacts) (h : picks.length = 1)
    (u : Fin pats.length × Fin picks.length) :
    chainCounts pats picks facts u = (1, 1) := by
  have h0 : (u.2 : ℕ) = 0 := Nat.lt_one_iff.1 (h ▸ u.2.isLt)
  rw [chainCounts, earlierFires_zero_pick pats picks facts u.1 h0]
  norm_num

end OnePick

/-! ## Later picks wait for the earlier pick -/

section Gating

open DarkTower.WarMachine.SelectionGOverCascades.SelectionToken

/-- Whole-task facts never carry `canBegin`; only a pattern's THEN can produce
it. -/
theorem initialTokens_noCanBegin (f : SelectionFacts) : canBegin ∉ initialTokens f := by
  intro h
  simp only [SelectionGOverCascades.initialTokens, Finset.mem_union] at h
  aesop

/-- When no pattern of the library produces `canBegin`, no trajectory state
ever holds it. -/
theorem traj_noCanBegin (pats : List SelectionPattern) (picks : List Target)
    (facts : Target → SelectionFacts)
    (hno : ∀ i : Fin pats.length, canBegin ∉ (interpret (pats.get i)).produces)
    (t : ℕ) (tok : ChainToken picks.length)
    (hin : tok ∈ coTraj (chainFam pats picks) (chainInitial picks facts) t) :
    tok.2 ≠ canBegin := by
  induction t generalizing tok with
  | zero =>
      simp only [coTraj] at hin
      obtain ⟨k, _, ht⟩ := Finset.mem_biUnion.1 hin
      obtain ⟨t', ht', heq⟩ := Finset.mem_image.1 ht
      intro hc
      have h2 : t' = canBegin := by rw [← hc]; exact congrArg Prod.snd heq
      exact initialTokens_noCanBegin _ (h2 ▸ ht')
  | succ t ih =>
      simp only [coTraj, coStep] at hin
      rcases Finset.mem_union.1 hin with h | h
      · exact ih _ h
      · obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 h
        simp only [chainFam, unitPattern] at hp
        obtain ⟨t', ht', heq⟩ := Finset.mem_image.1 hp
        intro hc
        have h2 : t' = canBegin := by rw [← hc]; exact congrArg Prod.snd heq
        exact hno p.1 (h2 ▸ ht')

/-- The Clojure's `chain-later-pick-waits-for-the-earlier-pick`: a library
whose patterns never produce `canBegin` (e.g. only `find-out-before-building`)
fires nothing on later picks. -/
theorem laterPick_never_fires (pats : List SelectionPattern) (picks : List Target)
    (facts : Target → SelectionFacts)
    (hno : ∀ i : Fin pats.length, canBegin ∉ (interpret (pats.get i)).produces)
    (i : Fin pats.length) {k : Fin picks.length} (hk : (k : ℕ) ≠ 0) :
    ¬ firedOn (chainFam pats picks) (chainInitial picks facts) (i, k) := by
  rintro ⟨t, hguard⟩
  obtain ⟨v, hv⟩ := k
  cases v with
  | zero => exact hk rfl
  | succ w =>
      have hprev : prevGuard ⟨w + 1, hv⟩ = {tagTok ⟨w, Nat.lt_of_succ_lt hv⟩ canBegin} := rfl
      have hmem : tagTok ⟨w, Nat.lt_of_succ_lt hv⟩ canBegin ∈
          coTraj (chainFam pats picks) (chainInitial picks facts) t :=
        hguard.1 (by
          simp only [chainFam, unitPattern, hprev]
          exact Finset.mem_union_right _ (Finset.mem_singleton_self _))
      exact traj_noCanBegin pats picks facts hno t _ hmem rfl

/-- Stopping is the empty policy: no patterns, so no novelty term. -/
theorem stopping_no_novelty (facts : Target → SelectionFacts) (H : ℕ)
    (c : Fin H → ProbabilityKernel Unit CTauClassPreference.EndingClass) :
    totalNovelty (chainFam ([] : List SelectionPattern) ([] : List Target))
      (chainCounts [] [] facts) (point (chainInitial ([] : List Target) facts)) H = 0 := by
  have hf : ∀ s : Finset (ChainToken 0),
      enabledFrontier (chainFam ([] : List SelectionPattern) ([] : List Target))
        (containmentOrder (chainFam ([] : List SelectionPattern) ([] : List Target))) s = ∅ := by
    intro s; simp [enabledFrontier]
  unfold totalNovelty expectedNovelty
  refine Finset.sum_eq_zero fun tau _ => ?_
  simp only [hf, Finset.sum_empty, mul_zero]
  simp

end Gating

/-! ## The Lucy 09/10 acceptance case (wm-click-3e072695)

Clojure `selection-canonical-g-test/a-repeated-pattern-is-less-novel-than-a-
second-pattern`: field 09 (ready, placed under a way) and 10 (ready, present
but not placed).  `:way` (only-what-can-start-now + serves-a-way on 09) fires
two distinct patterns once each; `:chain` (only-what-can-start-now on 09 then
10) fires one pattern twice; `:alone` fires it once.  Per-pattern counts order
G as two-patterns-once-each < one-pattern-twice < one-pattern-once.  Under the
old Beta(1,1)-per-unit model the first two tie. -/

section Lucy0910

open DarkTower.WarMachine.SelectionGOverCascades.SelectionToken

def f09 : SelectionFacts where
  giraffe := { status := .ready, unblocks := 0, cone := 0 }
  placedWork := true
  unmetNeed := false
  namedLaterItem := false
  nonWorkPlacement := false

def f10 : SelectionFacts where
  giraffe := { status := .ready, unblocks := 0, cone := 0 }
  placedWork := false
  unmetNeed := false
  namedLaterItem := false
  nonWorkPlacement := true

def field0910 : Target → SelectionFacts
  | 9 => f09
  | 10 => f10
  | _ => f09

abbrev wayPats : List SelectionPattern :=
  [.onlyWhatCanStartNow, .servesAWay, .whatOthersWaitOnFirst]
abbrev onlyPats : List SelectionPattern := [.onlyWhatCanStartNow]
abbrev onePicks : List Target := [9]
abbrev chainPicks : List Target := [9, 10]

abbrev famW := chainFam wayPats onePicks
abbrev famC := chainFam onlyPats chainPicks
abbrev famA := chainFam onlyPats onePicks

theorem f09_tokens : initialTokens f09 = {ready, placedWork} := by decide
theorem f10_tokens : initialTokens f10 = {ready, nonWorkPlacement} := by decide

theorem famW_initial : chainInitial onePicks field0910 = tagSet (0 : Fin 1) {ready, placedWork} := by
  simp [chainInitial, onePicks, f09_tokens, field0910]

theorem famW_guard_only_s0 :
    CascadeTransition.guard (famW ((0 : Fin 3), (0 : Fin 1)))
      (tagSet (0 : Fin 1) {ready, placedWork}) := by
  unfold famW chainFam unitPattern wayPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
  decide

theorem famW_guard_serves_s0 :
    CascadeTransition.guard (famW ((1 : Fin 3), (0 : Fin 1)))
      (tagSet (0 : Fin 1) {ready, placedWork}) := by
  unfold famW chainFam unitPattern wayPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
  decide

theorem famC_guard_only_s0 :
    CascadeTransition.guard (famC ((0 : Fin 1), (0 : Fin 2)))
      (chainInitial chainPicks field0910) := by
  unfold famC chainFam unitPattern onlyPats chainInitial chainPicks field0910
    CascadeTransition.guard SelectionGOverCascades.interpret
    SelectionGOverCascades.mkPattern tagSet prevGuard
    SelectionGOverCascades.initialTokens f09 f10
  decide

/-- The chain's first step: only-what-can-start-now on 09 can begin. -/
def famC_s1 : Finset (ChainToken 2) :=
  chainInitial chainPicks field0910 ∪ tagSet (0 : Fin 2) {canBegin}

/-- The chain's second step: ... and then on 10. -/
def famC_s2 : Finset (ChainToken 2) :=
  famC_s1 ∪ tagSet (1 : Fin 2) {canBegin}

/-- The alone policy's one step. -/
def famA_s1 : Finset (ChainToken 1) :=
  tagSet (0 : Fin 1) {ready, placedWork} ∪ tagSet (0 : Fin 1) {canBegin}

theorem famC_guard_only_s1 : CascadeTransition.guard (famC ((0 : Fin 1), (1 : Fin 2))) famC_s1 := by
  unfold famC chainFam unitPattern onlyPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
    famC_s1
  decide

theorem famA_guard_only_s0 :
    CascadeTransition.guard (famA ((0 : Fin 1), (0 : Fin 1)))
      (tagSet (0 : Fin 1) {ready, placedWork}) := by
  unfold famA chainFam unitPattern onlyPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
  decide

theorem not_reach_of_none {α : Type*} {r : α → α → Prop} (a : α)
    (h : ∀ x, ¬ r a x) (b : α) : ¬ Reach r a b := by
  intro hR
  induction hR with
  | single he => exact h _ he
  | tail _ _ ih => exact ih

theorem coStep_empty {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (fam : ι → InterpretedPattern V) (s : Finset V)
    (h : enabledFrontier fam (containmentOrder fam) s = ∅) : coStep fam s = s := by
  simp [coStep, h]

theorem novelty_11 : novelty 1 1 = 1 / 4 := by
  rw [novelty_eq 1 1 (by norm_num) (by norm_num)]; norm_num

theorem novelty_21 : novelty 2 1 = 1 / 6 := by
  rw [novelty_eq 2 1 (by norm_num) (by norm_num)]; norm_num

/-- The way policy's next state: both firing patterns produce. -/
def famW_s1 : Finset (ChainToken 1) :=
  famA_s1 ∪ tagSet (0 : Fin 1) {reasonNamesWay}

theorem famW_notGuard20_s0 :
    ¬ CascadeTransition.guard (famW ((2 : Fin 3), (0 : Fin 1)))
      (chainInitial onePicks field0910) := by
  unfold famW chainFam unitPattern wayPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
    chainInitial onePicks field0910 f09 f10 SelectionGOverCascades.initialTokens
  decide

theorem famW_notGuard00_s1 : ¬ CascadeTransition.guard (famW ((0 : Fin 3), (0 : Fin 1))) famW_s1 := by
  unfold famW chainFam unitPattern wayPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
    famW_s1 famA_s1
  decide

theorem famW_notGuard10_s1 : ¬ CascadeTransition.guard (famW ((1 : Fin 3), (0 : Fin 1))) famW_s1 := by
  unfold famW chainFam unitPattern wayPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
    famW_s1 famA_s1
  decide

theorem famW_notGuard20_s1 : ¬ CascadeTransition.guard (famW ((2 : Fin 3), (0 : Fin 1))) famW_s1 := by
  unfold famW chainFam unitPattern wayPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
    famW_s1 famA_s1
  decide

theorem famC_notGuard01_s0 :
    ¬ CascadeTransition.guard (famC ((0 : Fin 1), (1 : Fin 2)))
      (chainInitial chainPicks field0910) := by
  unfold famC chainFam unitPattern onlyPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
    chainInitial chainPicks field0910 f09 f10 SelectionGOverCascades.initialTokens
  decide

theorem famC_notGuard00_s1 :
    ¬ CascadeTransition.guard (famC ((0 : Fin 1), (0 : Fin 2))) famC_s1 := by
  unfold famC chainFam unitPattern onlyPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
    famC_s1 chainInitial chainPicks field0910 f09 f10
    SelectionGOverCascades.initialTokens
  decide

theorem famC_notGuard00_s2 :
    ¬ CascadeTransition.guard (famC ((0 : Fin 1), (0 : Fin 2))) famC_s2 := by
  unfold famC chainFam unitPattern onlyPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
    famC_s2 famC_s1 chainInitial chainPicks field0910 f09 f10
    SelectionGOverCascades.initialTokens
  decide

theorem famC_notGuard01_s2 :
    ¬ CascadeTransition.guard (famC ((0 : Fin 1), (1 : Fin 2))) famC_s2 := by
  unfold famC chainFam unitPattern onlyPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
    famC_s2 famC_s1 chainInitial chainPicks field0910 f09 f10
    SelectionGOverCascades.initialTokens
  decide

theorem famA_notGuard00_s1 :
    ¬ CascadeTransition.guard (famA ((0 : Fin 1), (0 : Fin 1))) famA_s1 := by
  unfold famA chainFam unitPattern onlyPats CascadeTransition.guard
    SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern tagSet prevGuard
    famA_s1
  decide

theorem hedgeW : ∀ a b : Fin 3 × Fin 1, ¬ containmentOrder famW a b := by
  intro a b ⟨hne, h2⟩
  rw [Finset.nonempty_iff_ne_empty] at h2
  fin_cases a <;> fin_cases b <;>
    first
    | exact hne rfl
    | exact h2 (by unfold famW chainFam unitPattern wayPats SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern; decide)

theorem hedgeA : ∀ a b : Fin 1 × Fin 1, ¬ containmentOrder famA a b := by
  intro a b ⟨hne, h2⟩
  rw [Finset.nonempty_iff_ne_empty] at h2
  fin_cases a <;> fin_cases b <;>
    first
    | exact hne rfl
    | exact h2 (by unfold famA chainFam unitPattern onlyPats SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern; decide)

theorem hedgeC_from1 : ∀ x : Fin 1 × Fin 2,
    ¬ containmentOrder famC ((0 : Fin 1), (1 : Fin 2)) x := by
  intro x ⟨hne, h2⟩
  rw [Finset.nonempty_iff_ne_empty] at h2
  fin_cases x <;>
    first
    | exact hne rfl
    | exact h2 (by unfold famC chainFam unitPattern onlyPats SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern; decide)

theorem hedgeC_into0 : ∀ x : Fin 1 × Fin 2,
    ¬ containmentOrder famC x ((0 : Fin 1), (0 : Fin 2)) := by
  intro x ⟨hne, h2⟩
  rw [Finset.nonempty_iff_ne_empty] at h2
  fin_cases x <;>
    first
    | exact hne rfl
    | exact h2 (by unfold famC chainFam unitPattern onlyPats SelectionGOverCascades.interpret SelectionGOverCascades.mkPattern; decide)

theorem fw0 :
    enabledFrontier famW (containmentOrder famW) (chainInitial onePicks field0910)
      = {((0 : Fin 3), (0 : Fin 1)), ((1 : Fin 3), (0 : Fin 1))} := by
  ext u
  simp only [enabledFrontier, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ⟨hg, _⟩
    fin_cases u
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hg famW_notGuard20_s0
  · rintro (rfl | rfl)
    · exact ⟨famW_guard_only_s0, fun _ _ hR => not_reach_of_empty hedgeW hR⟩
    · exact ⟨famW_guard_serves_s0, fun _ _ hR => not_reach_of_empty hedgeW hR⟩

theorem fw1 : enabledFrontier famW (containmentOrder famW) famW_s1 = ∅ := by
  simp only [enabledFrontier, Finset.filter_eq_empty_iff]
  intro u _ ⟨hg, _⟩
  fin_cases u
  · exact absurd hg famW_notGuard00_s1
  · exact absurd hg famW_notGuard10_s1
  · exact absurd hg famW_notGuard20_s1

theorem famC_noReach00 (x : Fin 1 × Fin 2) :
    ¬ Reach (containmentOrder famC) x x := by
  intro hR
  fin_cases x
  · cases hR with
    | single he => exact hedgeC_into0 _ he
    | tail _ he => exact hedgeC_into0 _ he
  · cases hR with
    | single he => exact hedgeC_from1 _ he
    | tail h1 _ => exact not_reach_of_none _ hedgeC_from1 _ h1

theorem fc0 :
    enabledFrontier famC (containmentOrder famC) (chainInitial chainPicks field0910)
      = {((0 : Fin 1), (0 : Fin 2))} := by
  ext u
  simp only [enabledFrontier, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro ⟨hg, _⟩
    fin_cases u
    · exact rfl
    · exact absurd hg famC_notGuard01_s0
  · intro hu
    rw [hu]
    refine ⟨famC_guard_only_s0, fun q hq => ?_⟩
    fin_cases q
    · exact famC_noReach00 _
    · exact (famC_notGuard01_s0 hq).elim

theorem fc1 : enabledFrontier famC (containmentOrder famC) famC_s1
    = {((0 : Fin 1), (1 : Fin 2))} := by
  ext u
  simp only [enabledFrontier, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro ⟨hg, _⟩
    fin_cases u
    · exact absurd hg famC_notGuard00_s1
    · exact rfl
  · intro hu
    rw [hu]
    exact ⟨famC_guard_only_s1, fun q _ => not_reach_of_none _ hedgeC_from1 q⟩

theorem fc2 : enabledFrontier famC (containmentOrder famC) famC_s2 = ∅ := by
  simp only [enabledFrontier, Finset.filter_eq_empty_iff]
  intro u _ ⟨hg, _⟩
  fin_cases u
  · exact absurd hg famC_notGuard00_s2
  · exact absurd hg famC_notGuard01_s2

theorem fa0 :
    enabledFrontier famA (containmentOrder famA) (chainInitial onePicks field0910)
      = {((0 : Fin 1), (0 : Fin 1))} := by
  ext u
  simp only [enabledFrontier, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro ⟨hg, _⟩
    fin_cases u
    · exact rfl
  · rintro rfl
    exact ⟨famA_guard_only_s0, fun _ _ hR => not_reach_of_empty hedgeA hR⟩

theorem fa1 : enabledFrontier famA (containmentOrder famA) famA_s1 = ∅ := by
  simp only [enabledFrontier, Finset.filter_eq_empty_iff]
  intro u _ ⟨hg, _⟩
  fin_cases u
  · exact absurd hg famA_notGuard00_s1

theorem stepW0 : coStep famW (chainInitial onePicks field0910) = famW_s1 := by
  unfold coStep famW_s1 famA_s1
  rw [fw0, famW_initial]
  decide

theorem stepC0 : coStep famC (chainInitial chainPicks field0910) = famC_s1 := by
  unfold coStep famC_s1
  rw [fc0]
  decide

theorem stepC1 : coStep famC famC_s1 = famC_s2 := by
  unfold coStep famC_s2
  rw [fc1]
  decide

theorem stepA0 : coStep famA (chainInitial onePicks field0910) = famA_s1 := by
  unfold coStep famA_s1
  rw [fa0, famW_initial]
  decide

theorem chainCounts_zeroth_pick (pats : List SelectionPattern) (picks : List Target)
    (facts : Target → SelectionFacts) (i : Fin pats.length) (k : Fin picks.length)
    (hk : (k : ℕ) = 0) :
    chainCounts pats picks facts (i, k) = (1, 1) := by
  rw [chainCounts, earlierFires_zero_pick pats picks facts i hk]
  norm_num

open Classical in
theorem famC_fires00 :
    firedOn famC (chainInitial chainPicks field0910) ((0 : Fin 1), (0 : Fin 2)) :=
  ⟨0, famC_guard_only_s0⟩

open Classical in
theorem famC_earlier_one :
    earlierFires onlyPats chainPicks field0910 (0 : Fin 1) (1 : Fin 2) = 1 := by
  unfold earlierFires
  refine (Finset.card_eq_one).2 ⟨0, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    show ((1 : Fin 2) : ℕ) = 1 from rfl]
  fin_cases j
  · exact ⟨fun _ => rfl, fun _ => ⟨by decide, famC_fires00⟩⟩
  · exact ⟨fun h => absurd h.1 (by decide), fun h => absurd h (by decide)⟩

theorem famW_traj0 : coTraj famW (chainInitial onePicks field0910) 0
    = chainInitial onePicks field0910 := rfl
theorem famW_traj1 : coTraj famW (chainInitial onePicks field0910) 1 = famW_s1 := by
  show coStep famW (coTraj famW (chainInitial onePicks field0910) 0) = famW_s1
  rw [famW_traj0]; exact stepW0
theorem famW_traj2 : coTraj famW (chainInitial onePicks field0910) 2 = famW_s1 := by
  show coStep famW (coTraj famW (chainInitial onePicks field0910) 1) = famW_s1
  rw [famW_traj1]; exact coStep_empty famW famW_s1 fw1

theorem famC_traj0 : coTraj famC (chainInitial chainPicks field0910) 0
    = chainInitial chainPicks field0910 := rfl
theorem famC_traj1 : coTraj famC (chainInitial chainPicks field0910) 1 = famC_s1 := by
  show coStep famC (coTraj famC (chainInitial chainPicks field0910) 0) = famC_s1
  rw [famC_traj0]; exact stepC0
theorem famC_traj2 : coTraj famC (chainInitial chainPicks field0910) 2 = famC_s2 := by
  show coStep famC (coTraj famC (chainInitial chainPicks field0910) 1) = famC_s2
  rw [famC_traj1]; exact stepC1
theorem famC_traj3 : coTraj famC (chainInitial chainPicks field0910) 3 = famC_s2 := by
  show coStep famC (coTraj famC (chainInitial chainPicks field0910) 2) = famC_s2
  rw [famC_traj2]; exact coStep_empty famC famC_s2 fc2

theorem famA_traj0 : coTraj famA (chainInitial onePicks field0910) 0
    = chainInitial onePicks field0910 := rfl
theorem famA_traj1 : coTraj famA (chainInitial onePicks field0910) 1 = famA_s1 := by
  show coStep famA (coTraj famA (chainInitial onePicks field0910) 0) = famA_s1
  rw [famA_traj0]; exact stepA0
theorem famA_traj2 : coTraj famA (chainInitial onePicks field0910) 2 = famA_s1 := by
  show coStep famA (coTraj famA (chainInitial onePicks field0910) 1) = famA_s1
  rw [famA_traj1]; exact coStep_empty famA famA_s1 fa1

theorem famW_totalNovelty :
    totalNovelty famW (chainCounts wayPats onePicks field0910)
      (point (chainInitial onePicks field0910)) 3 = 1 / 2 := by
  unfold totalNovelty
  rw [Fin.sum_univ_three]
  have hθ : ∀ p, (famW p).theta = 1 := chainFam_theta_one wayPats onePicks
  simp only [expectedNovelty_point famW hθ]
  norm_num
  rw [famW_traj0, famW_traj1, famW_traj2, fw0, fw1]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty]
  simp [chainCounts, earlierFires_zero_pick, novelty_11]
  norm_num

theorem famC_totalNovelty :
    totalNovelty famC (chainCounts onlyPats chainPicks field0910)
      (point (chainInitial chainPicks field0910)) 3 = 5 / 12 := by
  unfold totalNovelty
  rw [Fin.sum_univ_three]
  have hθ : ∀ p, (famC p).theta = 1 := chainFam_theta_one onlyPats chainPicks
  simp only [expectedNovelty_point famC hθ]
  first | norm_num | skip
  rw [famC_traj0, famC_traj1, famC_traj2, fc0, fc1, fc2]
  simp only [Finset.sum_singleton, Finset.sum_empty]
  rw [chainCounts_zeroth_pick onlyPats chainPicks field0910 _ _ rfl]
  simp only [chainCounts, famC_earlier_one]
  norm_num
  rw [novelty_21, novelty_11]
  norm_num

theorem famA_totalNovelty :
    totalNovelty famA (chainCounts onlyPats onePicks field0910)
      (point (chainInitial onePicks field0910)) 3 = 1 / 4 := by
  unfold totalNovelty
  rw [Fin.sum_univ_three]
  have hθ : ∀ p, (famA p).theta = 1 := chainFam_theta_one onlyPats onePicks
  simp only [expectedNovelty_point famA hθ]
  first | norm_num | skip
  rw [famA_traj0, famA_traj1, famA_traj2, fa0, fa1]
  simp only [Finset.sum_singleton, Finset.sum_empty]
  simp [chainCounts, earlierFires_zero_pick, novelty_11]

theorem famW_totalNovelty_old :
    totalNovelty famW (fun _ => (1, 1)) (point (chainInitial onePicks field0910)) 3 = 1 / 2 := by
  unfold totalNovelty
  rw [Fin.sum_univ_three]
  have hθ : ∀ p, (famW p).theta = 1 := chainFam_theta_one wayPats onePicks
  simp only [expectedNovelty_point famW hθ]
  norm_num
  rw [famW_traj0, famW_traj1, famW_traj2, fw0, fw1]
  simp only [novelty_11, Finset.sum_insert, Finset.sum_singleton]
  norm_num

theorem famC_totalNovelty_old :
    totalNovelty famC (fun _ => (1, 1)) (point (chainInitial chainPicks field0910)) 3 = 1 / 2 := by
  unfold totalNovelty
  rw [Fin.sum_univ_three]
  have hθ : ∀ p, (famC p).theta = 1 := chainFam_theta_one onlyPats chainPicks
  simp only [expectedNovelty_point famC hθ]
  first | norm_num | skip
  rw [famC_traj0, famC_traj1, famC_traj2, fc0, fc1, fc2]
  simp only [novelty_11, Finset.sum_singleton, Finset.sum_empty]
  norm_num

/-! ### The acceptance theorem and the bad case

The three policies share the field 09/10 and the same first pick (09), so the
class route gives them one risk + ambiguity part; the hypotheses state exactly
that shared part (`scoreCascadeCo` agrees, at the Clojure horizon 3 = max unit
count).  The novelty term then orders G strictly, in the direction the Clojure
test asserts; with every count pinned at Beta(1,1) — the pre-`ca062096f` model
— the first two tie instead. -/

theorem ladder_ordering (ending : CTauClassPreference.EndingClass)
    (c : Fin 3 → ProbabilityKernel Unit CTauClassPreference.EndingClass) {g : ℝ}
    (hway : CascadeCoApplyG.scoreCascadeCo
      (chainCandidate wayPats onePicks field0910 ending).toCandidate 3 c = .ok g)
    (hchain : CascadeCoApplyG.scoreCascadeCo
      (chainCandidate onlyPats chainPicks field0910 ending).toCandidate 3 c = .ok g)
    (halone : CascadeCoApplyG.scoreCascadeCo
      (chainCandidate onlyPats onePicks field0910 ending).toCandidate 3 c = .ok g) :
    ∃ gw gc ga, chainG wayPats onePicks field0910 ending 3 c = .ok gw
      ∧ chainG onlyPats chainPicks field0910 ending 3 c = .ok gc
      ∧ chainG onlyPats onePicks field0910 ending 3 c = .ok ga
      ∧ gw < gc ∧ gc < ga := by
  refine ⟨g - 1 / 2, g - 5 / 12, g - 1 / 4, ?_, ?_, ?_, by norm_num, by norm_num⟩
  · unfold chainG GOverCascades.cascadeGrainG CascadeCoApplyGNovelty.scoreCascadeCoN
    rw [hway]
    simp only [chainCandidate]
    rw [famW_totalNovelty]
  · unfold chainG GOverCascades.cascadeGrainG CascadeCoApplyGNovelty.scoreCascadeCoN
    rw [hchain]
    simp only [chainCandidate]
    rw [famC_totalNovelty]
  · unfold chainG GOverCascades.cascadeGrainG CascadeCoApplyGNovelty.scoreCascadeCoN
    rw [halone]
    simp only [chainCandidate]
    rw [famA_totalNovelty]

/-- The old model: every count pinned at Beta(1,1). -/
def wayOld (ending : CTauClassPreference.EndingClass) :
    CascadeCoApplyGNovelty.CandidateN (Fin 3 × Fin 1) (ChainToken 1) :=
  { chainCandidate wayPats onePicks field0910 ending with
    counts := fun _ => (1, 1)
    counts_pos := fun _ => ⟨by norm_num, by norm_num⟩ }

def chainOld (ending : CTauClassPreference.EndingClass) :
    CascadeCoApplyGNovelty.CandidateN (Fin 1 × Fin 2) (ChainToken 2) :=
  { chainCandidate onlyPats chainPicks field0910 ending with
    counts := fun _ => (1, 1)
    counts_pos := fun _ => ⟨by norm_num, by norm_num⟩ }

theorem ladder_bad_case (ending : CTauClassPreference.EndingClass)
    (c : Fin 3 → ProbabilityKernel Unit CTauClassPreference.EndingClass) {g : ℝ}
    (hway : CascadeCoApplyG.scoreCascadeCo (wayOld ending).toCandidate 3 c = .ok g)
    (hchain : CascadeCoApplyG.scoreCascadeCo (chainOld ending).toCandidate 3 c = .ok g) :
    CascadeCoApplyGNovelty.scoreCascadeCoN (wayOld ending) 3 c
      = CascadeCoApplyGNovelty.scoreCascadeCoN (chainOld ending) 3 c := by
  unfold CascadeCoApplyGNovelty.scoreCascadeCoN
  rw [hway, hchain]
  simp only [wayOld, chainOld, chainCandidate]
  change Except.ok (g - totalNovelty famW (fun _ => (1, 1))
      (point (chainInitial onePicks field0910)) 3)
    = Except.ok (g - totalNovelty famC (fun _ => (1, 1))
      (point (chainInitial chainPicks field0910)) 3)
  rw [famW_totalNovelty_old, famC_totalNovelty_old]

end Lucy0910

#print axioms chainCounts_one_pick
#print axioms laterPick_never_fires
#print axioms stopping_no_novelty
#print axioms ladder_ordering
#print axioms ladder_bad_case

end
end DarkTower.WarMachine.SelectionGOverChains
