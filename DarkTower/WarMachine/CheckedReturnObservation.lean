import DarkTower.WarMachine.OuterReturnModel
import DarkTower.WarMachine.CheckedProblemMap

/-!
# Closure observations of checked returns

This module connects the finite outer-return kernels of `OuterReturnModel` to
the checked problem map of `CheckedProblemMap`.  An outer return value `a : A`
(for example a `Sigma Result` value drawn from `conditionalReturn`) is sent to
a proof-bearing optional report by a supplied `realize : A → Option
(ReturnReport I Label)`.  The *closure observation* of `a` is the declared
finite scored set intersected with `closedSet` of the map after
`update m₀ (realize a)`.  The observation therefore reads the actual checked
update: neither the report's label nor its `claimedClosed` field is consulted.

`realize` is an explicit parameter.  It stands for synthetic scenario
assumptions: a finite index of possible reports, each paired with the checked
artifacts and reductions it would carry.  Nothing here is a decoder from
runtime records or a theorem that a runtime record's proofs are genuine.  The
proof payload space itself need not be finite; only the return alphabet `A`
is.  Since every admitted artifact carries a Lean proof, no probability or
label can produce a proof that does not exist: `returnObs_sound` holds for
every return value, whatever mass the kernel puts on it.

The observation kernel is the existing deterministic post-composition
`AIFReportEncoding.reportKernel` applied to the return kernel; integration of
a finite latent parameter is the existing `CascadeEFE.push`.  No second
closure mechanism or kernel constructor is introduced.  Because the
observation is a function of the whole return value, any joint or shared
latent dependence in the return kernel is carried into the observation
(`push_observationKernel`, `shared_latent_joint_closure`).

An absent return (`realize a = none`) leaves the map unchanged; its
observation is the set of *preexisting* scored closures, which need not be
empty.  A present report with no checked content observes the same set.
Absent mass is kept at its own return value and is never dropped or
renormalised away.

Labels do not in general determine the observation.  `LabelFactors` states
the separate condition under which they would; `labelFactors_iff` reduces it to
constancy of the observation on label fibres, and the fixture refutes it.

AIF boundary.  Parr et al. 2022 ch. 7 (eqs. 7.9--7.11) treat outcomes as
observations generated through a normalised likelihood; this module supplies
one such finite likelihood, from return values to closure observations, by
composition of reviewed kernels.  That the observation is grounded in proof
closure is domain semantics of the problem map, not a theorem of active
inference.  `closedSet` is noncomputable: an executable closure and its
agreement with `Closed` remain open.  No probabilities, preferences, priors,
admission or learning rule are chosen here, and no R20, full-loop or runtime
claim is made.
-/

namespace DarkTower.WarMachine.CheckedReturnObservation

open scoped BigOperators
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.CheckedProblemMap
open DarkTower.WarMachine.OuterReturnModel

noncomputable section

universe u

variable {S : Type u} [Fintype S] [DecidableEq S] {I : S → Prop}

/-! ## The deterministic observation -/

/-- The scored closures of a map: declared scored IDs that are `Closed`. -/
def closureObs (scored : Finset S) (m : ProblemMap I) : Finset S :=
  scored ∩ closedSet m

theorem mem_closureObs {scored : Finset S} {m : ProblemMap I} {s : S} :
    s ∈ closureObs scored m ↔ s ∈ scored ∧ Closed m s := by
  simp [closureObs, mem_closedSet]

variable {Label : Type} {A : Type*}

/-- The closure observation of a return value: scored closures of the map
after the update by the report that `a` is supplied to realize. -/
def returnObs (m₀ : ProblemMap I) (scored : Finset S)
    (realize : A → Option (ReturnReport I Label)) (a : A) : Finset S :=
  closureObs scored (update m₀ (realize a))

variable {m₀ : ProblemMap I} {scored : Finset S}
  {realize : A → Option (ReturnReport I Label)}

theorem mem_returnObs {a : A} {s : S} :
    s ∈ returnObs m₀ scored realize a ↔
      s ∈ scored ∧ Closed (update m₀ (realize a)) s :=
  mem_closureObs

/-- Every observed closure is true under the interpretation. -/
theorem returnObs_sound {a : A} {s : S} (h : s ∈ returnObs m₀ scored realize a) :
    I s :=
  update_sound _ (mem_returnObs.1 h).2

theorem returnObs_subset_scored (a : A) : returnObs m₀ scored realize a ⊆ scored :=
  fun _ h => (mem_returnObs.1 h).1

/-- Every return, including an absent one, observes the preexisting scored
closures. -/
theorem preexisting_subset_returnObs (a : A) :
    closureObs scored m₀ ⊆ returnObs m₀ scored realize a := by
  intro s h
  rw [mem_closureObs] at h
  exact mem_returnObs.2 ⟨h.1, closed_update _ h.2⟩

/-- An absent return observes exactly the preexisting scored closures. -/
theorem returnObs_absent {a : A} (h : realize a = none) :
    returnObs m₀ scored realize a = closureObs scored m₀ := by
  simp [returnObs, h, update_none]

/-- A present report with no checked content observes the same set as an
absent one, whatever its label and claims. -/
theorem returnObs_unchecked {a : A} {r : ReturnReport I Label}
    (h : realize a = some r) (hc : r.checked = CheckedReturn.empty) :
    returnObs m₀ scored realize a = closureObs scored m₀ := by
  ext s
  rw [mem_returnObs, mem_closureObs, h, closed_update_unchecked m₀ r hc]

/-- The observation depends on a return only through its checked content. -/
theorem returnObs_eq_of_checked {a a' : A}
    (h : (realize a).map ReturnReport.checked = (realize a').map ReturnReport.checked) :
    returnObs m₀ scored realize a = returnObs m₀ scored realize a' := by
  unfold returnObs
  congr 1
  cases ha : realize a <;> cases ha' : realize a' <;> simp_all [update]

/-! ## Labels -/

/-- The separately stated condition under which the label of a present report
would determine its closure observation. -/
def LabelFactors (m₀ : ProblemMap I) (scored : Finset S)
    (realize : A → Option (ReturnReport I Label)) : Prop :=
  ∃ f : Label → Finset S, ∀ a r, realize a = some r →
    returnObs m₀ scored realize a = f r.label

/-- Labels factor the observation exactly when the observation is constant on
each label fibre of the present reports. -/
theorem labelFactors_iff :
    LabelFactors m₀ scored realize ↔
      ∀ a a' r r', realize a = some r → realize a' = some r' →
        r.label = r'.label →
          returnObs m₀ scored realize a = returnObs m₀ scored realize a' := by
  classical
  constructor
  · rintro ⟨f, hf⟩ a a' r r' ha ha' hl
    rw [hf a r ha, hf a' r' ha', hl]
  · intro h
    refine ⟨fun l => if hl : ∃ a r, realize a = some r ∧ r.label = l
      then returnObs m₀ scored realize hl.choose else ∅, ?_⟩
    intro a r ha
    have hex : ∃ a' r', realize a' = some r' ∧ r'.label = r.label := ⟨a, r, ha, rfl⟩
    dsimp only
    rw [dif_pos hex]
    obtain ⟨r', hr', hl'⟩ := hex.choose_spec
    exact h a _ r r' ha hr' hl'.symm

/-! ## The observation kernel -/

variable [Fintype A]

/-- Observation kernel: the existing deterministic report post-composition of
a return kernel by the closure observation. -/
def observationKernel {Z : Type*} [Fintype Z] (m₀ : ProblemMap I) (scored : Finset S)
    (realize : A → Option (ReturnReport I Label)) (k : ProbabilityKernel Z A) :
    ProbabilityKernel Z (Finset S) :=
  AIFReportEncoding.reportKernel k (returnObs m₀ scored realize)

variable {Z : Type*} [Fintype Z]

theorem observationKernel_normalised (k : ProbabilityKernel Z A) (z : Z) :
    ∑ o, (observationKernel m₀ scored realize k).mass z o = 1 :=
  CascadeEFE.kernel_sum _ _

theorem observationKernel_mass (k : ProbabilityKernel Z A) (z : Z) (o : Finset S) :
    (observationKernel m₀ scored realize k).mass z o =
      ∑ a, k.mass z a * if o = returnObs m₀ scored realize a then 1 else 0 :=
  rfl

/-- Exact event marginal: the probability of any event on observations is the
return-kernel mass of the return values whose actual checked update lands in
that event. -/
theorem observationKernel_event (k : ProbabilityKernel Z A) (z : Z)
    (P : Finset S → Prop) [DecidablePred P] :
    ∑ o ∈ Finset.univ.filter P, (observationKernel m₀ scored realize k).mass z o =
      ∑ a ∈ Finset.univ.filter (fun a => P (returnObs m₀ scored realize a)),
        k.mass z a := by
  simp only [observationKernel_mass]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, Finset.sum_filter]
  by_cases hP : P (returnObs m₀ scored realize a)
  · rw [Finset.sum_eq_single (returnObs m₀ scored realize a)]
    · simp [hP]
    · intro o _ ho
      simp [ho]
    · simp
  · rw [if_neg hP, Finset.sum_eq_zero]
    · simp
    · intro o _
      by_cases ho : o = returnObs m₀ scored realize a
      · subst ho; simp [hP]
      · simp [ho]

/-- Marginal probability that a scored ID is observed closed. -/
theorem observationKernel_closure_marginal (k : ProbabilityKernel Z A) (z : Z) (s : S) :
    ∑ o ∈ Finset.univ.filter (fun o => s ∈ o),
        (observationKernel m₀ scored realize k).mass z o =
      ∑ a ∈ Finset.univ.filter (fun a => s ∈ returnObs m₀ scored realize a),
        k.mass z a :=
  observationKernel_event k z (fun o => s ∈ o)

/-- A preexisting scored closure is observed with probability one, whatever
the return kernel puts on absent or present reports. -/
theorem preexisting_observed_surely (k : ProbabilityKernel Z A) (z : Z) {s : S}
    (hs : s ∈ scored) (hc : Closed m₀ s) :
    ∑ o ∈ Finset.univ.filter (fun o => s ∈ o),
        (observationKernel m₀ scored realize k).mass z o = 1 := by
  rw [observationKernel_closure_marginal, Finset.filter_true_of_mem]
  · exact CascadeEFE.kernel_sum k z
  · intro a _
    exact preexisting_subset_returnObs a (mem_closureObs.2 ⟨hs, hc⟩)

/-- Integrating a latent parameter with the existing `push` commutes with the
deterministic observation: the predictive observation is the observation of
the predictive joint return, so latent dependence is not factored away. -/
theorem push_observationKernel (prior : ProbabilityKernel Unit Z)
    (k : ProbabilityKernel Z A) (o : Finset S) :
    (CascadeEFE.push prior (observationKernel m₀ scored realize k)).mass () o =
      (observationKernel m₀ scored realize (CascadeEFE.push prior k)).mass () o :=
  AIFReportEncoding.push_report_mass prior k _ o

/-! ## Specialisation to the outer conditional return -/

section Conditional

variable {Theta V : Type*} {Result : V → Type*}
  [Fintype Theta] [Fintype V] [∀ v, Fintype (Result v)]

/-- Closure observation of the outer conditional return. -/
def conditionalObservation (m₀ : ProblemMap I) (scored : Finset S)
    (realize : Sigma Result → Option (ReturnReport I Label))
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v)) :
    ProbabilityKernel Theta (Finset S) :=
  observationKernel m₀ scored realize (conditionalReturn verdict result)

variable {realize : Sigma Result → Option (ReturnReport I Label)}

theorem conditionalObservation_normalised
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v)) (theta : Theta) :
    ∑ o, (conditionalObservation m₀ scored realize verdict result).mass theta o = 1 :=
  CascadeEFE.kernel_sum _ _

/-- Exact observation mass: verdict mass times joint result mass, summed over
the return values whose checked update yields that observation. -/
theorem conditionalObservation_mass
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v)) (theta : Theta)
    (o : Finset S) :
    (conditionalObservation m₀ scored realize verdict result).mass theta o =
      ∑ v, verdict.mass theta v * ∑ r, (result v).mass theta r *
        if o = returnObs m₀ scored realize ⟨v, r⟩ then 1 else 0 := by
  rw [conditionalObservation, observationKernel_mass,
    Fintype.sum_sigma' (fun v r => (conditionalReturn verdict result).mass theta ⟨v, r⟩ *
      if o = returnObs m₀ scored realize ⟨v, r⟩ then 1 else 0)]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [conditionalReturn, returnMass, CascadeEFE.finiteKernel]
  ring

/-- Marginal probability that a scored ID is observed closed under the outer
conditional return. -/
theorem conditionalObservation_closure_marginal
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v)) (theta : Theta) (s : S) :
    ∑ o ∈ Finset.univ.filter (fun o => s ∈ o),
        (conditionalObservation m₀ scored realize verdict result).mass theta o =
      ∑ a ∈ Finset.univ.filter (fun a => s ∈ returnObs m₀ scored realize a),
        verdict.mass theta a.1 * (result a.1).mass theta a.2 :=
  observationKernel_closure_marginal _ theta s

/-- The predictive closure observation is the observation of the existing
`predictiveReturn`. -/
theorem push_conditionalObservation (prior : ProbabilityKernel Unit Theta)
    (verdict : ProbabilityKernel Theta V)
    (result : ∀ v, ProbabilityKernel Theta (Result v)) (o : Finset S) :
    (CascadeEFE.push prior (conditionalObservation m₀ scored realize verdict result)).mass () o =
      (observationKernel m₀ scored realize (predictiveReturn prior verdict result)).mass () o :=
  push_observationKernel prior _ o

end Conditional

/-! ## Synthetic controls

The six-ID map `m0` of `CheckedProblemMap`: the consumer has a checked
reduction from foundation and adapter jointly, an alternative unresolved
route, and an unseeded cycle; no artifacts. -/

open CheckedProblemMap (Stmt interp Verdict m0 foundationOnly foundationAndAdapter
  predictionOnly censoredHelper)

/-- The declared scored problems for the controls. -/
def scoredFix : Finset Stmt := {.consumer, .adapter, .cycA}

/-- Reports realised by themselves: used for controls that do not need a
finite alphabet. -/
abbrev obsOf (m : ProblemMap interp) (o : Option (ReturnReport interp Verdict)) :
    Finset Stmt :=
  returnObs m scoredFix id o

theorem foundationOnly_not_observed : Stmt.consumer ∉ obsOf m0 (some foundationOnly) :=
  fun h => foundation_without_adapter_unclosed (mem_returnObs.1 h).2

theorem foundationAndAdapter_observed :
    Stmt.consumer ∈ obsOf m0 (some foundationAndAdapter) :=
  mem_returnObs.2 ⟨by simp [scoredFix], foundation_adapter_discharge.1⟩

theorem absent_on_m0_not_observed : Stmt.consumer ∉ obsOf m0 none :=
  fun h => reduction_not_discharge.2.2 (mem_returnObs.1 h).2

/-- The map after a successful return. -/
abbrev m1 : ProblemMap interp := update m0 (some foundationAndAdapter)

/-- An absent return on `m1` still observes the consumer, closed earlier. -/
theorem absent_preserves_preexisting : Stmt.consumer ∈ obsOf m1 none :=
  mem_returnObs.2 ⟨by simp [scoredFix], foundation_adapter_discharge.1⟩

/-- The empty update is not the empty observation. -/
theorem absent_observation_nonempty : obsOf m1 none ≠ ∅ :=
  Finset.ne_empty_of_mem absent_preserves_preexisting

/-- A prediction-only report observes exactly what an absent one does. -/
theorem predictionOnly_unchanged (m : ProblemMap interp) :
    obsOf m (some predictionOnly) = obsOf m none := by
  unfold obsOf
  rw [returnObs_unchecked (realize := id) rfl rfl, returnObs_absent (realize := id) rfl]

/-- A censored report's checked helper is observed; the consumer is not. -/
theorem censored_helper_observed :
    Stmt.adapter ∈ obsOf m0 (some censoredHelper) ∧
      Stmt.consumer ∉ obsOf m0 (some censoredHelper) :=
  ⟨mem_returnObs.2 ⟨by simp [scoredFix], censored_helper_admitted.1⟩,
    fun h => censored_helper_admitted.2 (mem_returnObs.1 h).2⟩

/-- Same label and same claims, different checked content, different
observation. -/
theorem same_label_different_observation :
    foundationOnly.label = foundationAndAdapter.label ∧
      foundationOnly.claimedClosed = foundationAndAdapter.claimedClosed ∧
      obsOf m0 (some foundationOnly) ≠ obsOf m0 (some foundationAndAdapter) :=
  ⟨rfl, rfl, fun h => foundationOnly_not_observed (h ▸ foundationAndAdapter_observed)⟩

/-- Hence labels cannot replace reports in this scenario. -/
theorem labels_do_not_factor :
    ¬ LabelFactors m0 scoredFix (id : Option (ReturnReport interp Verdict) → _) := by
  rw [labelFactors_iff]
  intro h
  exact same_label_different_observation.2.2
    (h (some foundationOnly) (some foundationAndAdapter) _ _ rfl rfl rfl)

/-! ### A finite outer return with a shared latent bit

The verdict marks presence; a present return's result records whether the
adapter came back checked.  A latent bit drives that result.  Both present
realisations carry the label `closed` and claim the consumer. -/

/-- Local copy of `CheckedProblemMap`'s private rule-closedness helper for
`m0` plus artifacts (the reviewed module is not edited). -/
private theorem ruleClosed_m0 (as : List (Artifact interp)) (T : Set Stmt)
    (ha : ∀ a ∈ as, a.stmt ∈ T)
    (hF : Stmt.consumer ∈ T ∨ Stmt.foundation ∉ T ∨ Stmt.adapter ∉ T)
    (hH : Stmt.consumer ∈ T ∨ Stmt.hard ∉ T)
    (hA : Stmt.cycA ∈ T ∨ Stmt.cycB ∉ T)
    (hB : Stmt.cycB ∈ T ∨ Stmt.cycA ∉ T) :
    RuleClosed (admit m0 ⟨as, []⟩) T := by
  open CheckedProblemMap in
  refine ⟨fun a h => ?_, fun r hr ht => ?_⟩
  · simp only [admit, m0, List.nil_append] at h
    exact ha a h
  · have hr' : r = viaFoundation ∨ r = viaHard ∨ r = cycAB ∨ r = cycBA := by
      simpa [admit, m0] using hr
    rcases hr' with rfl | rfl | rfl | rfl
    · rcases hF with h | h | h
      · exact h
      · exact absurd (ht .foundation (by simp [viaFoundation])) h
      · exact absurd (ht .adapter (by simp [viaFoundation])) h
    · rcases hH with h | h
      · exact h
      · exact absurd (ht .hard (by simp [viaHard])) h
    · rcases hA with h | h
      · exact h
      · exact absurd (ht .cycB (by simp [cycAB])) h
    · rcases hB with h | h
      · exact h
      · exact absurd (ht .cycA (by simp [cycBA])) h

/-- Result domains: a present return carries a Bool, an absent one is the
not-applicable singleton. -/
abbrev Res : Bool → Type
  | true => Bool
  | false => Unit

instance : ∀ v, Fintype (Res v)
  | true => inferInstanceAs (Fintype Bool)
  | false => inferInstanceAs (Fintype Unit)

instance : ∀ v, DecidableEq (Res v)
  | true => inferInstanceAs (DecidableEq Bool)
  | false => inferInstanceAs (DecidableEq Unit)

/-- The supplied realisation of each finite return value as a report. -/
def realizeFix : Sigma Res → Option (ReturnReport interp Verdict)
  | ⟨true, b⟩ => if (b : Bool) then some foundationAndAdapter else some foundationOnly
  | ⟨false, _⟩ => none

def presentVerdict : ProbabilityKernel Bool Bool :=
  CascadeEFE.finiteKernel (fun _ v => if v = true then 1 else 0)
    (by intros; split_ifs <;> norm_num) (by intro; simp)

/-- A present result copies the latent bit; the absent branch is its
singleton. -/
def latentResult : ∀ v, ProbabilityKernel Bool (Res v)
  | true => CascadeEFE.finiteKernel (fun theta (b : Bool) => if b = theta then 1 else 0)
      (by intros; split_ifs <;> norm_num)
      (by
        intro theta
        show ∑ b : Bool, (if b = theta then (1 : ℝ) else 0) = 1
        cases theta <;> simp)
  | false => CascadeEFE.finiteKernel (fun _ _ => 1)
      (by intros; norm_num) (by intro; show ∑ _u : Unit, (1 : ℝ) = 1; simp)

abbrev obsFix (a : Sigma Res) : Finset Stmt := returnObs m0 scoredFix realizeFix a

theorem realizeFix_tt : realizeFix ⟨true, (true : Bool)⟩ = some foundationAndAdapter := rfl

theorem obsFix_present_true : obsFix ⟨true, (true : Bool)⟩ = {.consumer, .adapter} := by
  ext s
  rw [mem_returnObs, realizeFix_tt]
  constructor
  · rintro ⟨hs, hc⟩
    have hT := ruleClosed_m0
      [CheckedProblemMap.foundationArt, CheckedProblemMap.adapterArt]
      {.foundation, .adapter, .consumer}
      (by simp [CheckedProblemMap.foundationArt, CheckedProblemMap.adapterArt])
      (by simp) (by simp) (by simp) (by simp)
    have hc' : Closed (admit m0 ⟨[CheckedProblemMap.foundationArt,
      CheckedProblemMap.adapterArt], []⟩) s := hc
    have := closed_least hT hc'
    simp [scoredFix] at hs
    rcases hs with rfl | rfl | rfl <;> simp_all
  · intro hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ⟨by simp [scoredFix], foundation_adapter_discharge.1⟩
    · exact ⟨by simp [scoredFix],
        Closed.artifact CheckedProblemMap.adapterArt
          (by simp [update, admit, foundationAndAdapter])⟩

theorem consumer_mem_obsFix_iff (a : Sigma Res) :
    Stmt.consumer ∈ obsFix a ↔ a = ⟨true, (true : Bool)⟩ := by
  rcases a with ⟨_ | _, b⟩
  · simp only [obsFix, returnObs_absent (realize := realizeFix) (a := ⟨false, b⟩) rfl]
    exact ⟨fun h => absurd (mem_closureObs.1 h).2 reduction_not_discharge.2.2,
      fun h => by cases h⟩
  · cases b
    · exact ⟨fun h => absurd h foundationOnly_not_observed, fun h => by cases h⟩
    · simp [obsFix_present_true]

theorem adapter_mem_obsFix_iff (a : Sigma Res) :
    Stmt.adapter ∈ obsFix a ↔ a = ⟨true, (true : Bool)⟩ := by
  rcases a with ⟨_ | _, b⟩
  · simp only [obsFix, returnObs_absent (realize := realizeFix) (a := ⟨false, b⟩) rfl]
    refine ⟨fun h => ?_, fun h => by cases h⟩
    have hT := ruleClosed_m0 [] ∅ (by simp) (by simp) (by simp)
      (by simp) (by simp)
    rw [show admit m0 ⟨[], []⟩ = m0 from admit_empty m0] at hT
    exact absurd (closed_least hT (mem_closureObs.1 h).2) (by simp)
  · cases b
    · refine ⟨fun h => ?_, fun h => by cases h⟩
      have hT := ruleClosed_m0 [CheckedProblemMap.foundationArt]
        {.foundation} (by simp [CheckedProblemMap.foundationArt]) (by simp) (by simp)
        (by simp) (by simp)
      have hc : Closed (admit m0 ⟨[CheckedProblemMap.foundationArt], []⟩) .adapter :=
        (mem_returnObs.1 h).2
      exact absurd (closed_least hT hc) (by simp)
    · simp [obsFix_present_true]

/-- Every present realisation is labelled `closed` and claims the consumer. -/
theorem present_reports_claim_consumer (a : Sigma Res) (r : ReturnReport interp Verdict)
    (h : realizeFix a = some r) :
    r.label = Verdict.closed ∧ Stmt.consumer ∈ r.claimedClosed := by
  rcases a with ⟨_ | _, b⟩
  · cases h
  · cases b <;> (simp only [realizeFix] at h; cases h; simp [foundationOnly, foundationAndAdapter])

/-- The predictive closure observation of the fixture. -/
abbrev predObsFix : ProbabilityKernel Unit (Finset Stmt) :=
  CascadeEFE.push OuterReturnModel.uniformBool
    (conditionalObservation m0 scoredFix realizeFix presentVerdict latentResult)

/-- Predictive probability of an event on observations, for the fixture. -/
abbrev probFix (P : Finset Stmt → Prop) [DecidablePred P] : ℝ :=
  ∑ o ∈ Finset.univ.filter P, predObsFix.mass () o

/-- Pull a fixture event back to the return values that realise it. -/
theorem probFix_eq (P : Finset Stmt → Prop) [DecidablePred P] :
    probFix P = ∑ a ∈ Finset.univ.filter (fun a => P (obsFix a)),
      (predictiveReturn OuterReturnModel.uniformBool presentVerdict latentResult).mass () a := by
  rw [probFix, Finset.sum_congr rfl fun o _ => push_conditionalObservation _ _ _ o,
    observationKernel_event]

theorem predictive_tt :
    (predictiveReturn OuterReturnModel.uniformBool presentVerdict latentResult).mass ()
      ⟨true, (true : Bool)⟩ = 1 / 2 := by
  norm_num [predictiveReturn, conditionalReturn, CascadeEFE.push, returnMass,
    CascadeEFE.finiteKernel, OuterReturnModel.uniformBool, presentVerdict, latentResult,
    Fintype.sum_bool]

/-- Predictive probability that the consumer is observed closed is one half,
although every present return is labelled `closed` and claims the consumer
(`present_reports_claim_consumer`) and the return is present surely. -/
theorem consumer_observed_half : probFix (fun o => Stmt.consumer ∈ o) = 1 / 2 := by
  rw [probFix_eq, show Finset.univ.filter (fun a => Stmt.consumer ∈ obsFix a) =
      {⟨true, (true : Bool)⟩} by ext a; simp [consumer_mem_obsFix_iff],
    Finset.sum_singleton, predictive_tt]

theorem adapter_observed_half : probFix (fun o => Stmt.adapter ∈ o) = 1 / 2 := by
  rw [probFix_eq, show Finset.univ.filter (fun a => Stmt.adapter ∈ obsFix a) =
      {⟨true, (true : Bool)⟩} by ext a; simp [adapter_mem_obsFix_iff],
    Finset.sum_singleton, predictive_tt]

/-- Both scored closures co-occur through the shared latent bit: their joint
probability is one half, not the product of their marginals. -/
theorem shared_latent_joint_closure :
    probFix (fun o => Stmt.consumer ∈ o ∧ Stmt.adapter ∈ o) = 1 / 2 ∧
      probFix (fun o => Stmt.consumer ∈ o ∧ Stmt.adapter ∈ o) ≠
        probFix (fun o => Stmt.consumer ∈ o) * probFix (fun o => Stmt.adapter ∈ o) := by
  have hj : probFix (fun o => Stmt.consumer ∈ o ∧ Stmt.adapter ∈ o) = 1 / 2 := by
    rw [probFix_eq, show Finset.univ.filter
        (fun a => Stmt.consumer ∈ obsFix a ∧ Stmt.adapter ∈ obsFix a) =
        {⟨true, (true : Bool)⟩} by
      ext a; simp [consumer_mem_obsFix_iff, adapter_mem_obsFix_iff],
      Finset.sum_singleton, predictive_tt]
  refine ⟨hj, ?_⟩
  rw [hj, consumer_observed_half, adapter_observed_half]
  norm_num

/-- On the map after a successful return, the consumer is observed with
probability one under every return kernel over this alphabet, including
kernels that put positive mass on the absent value: absent mass is kept, and
it observes the preexisting closure. -/
theorem m1_consumer_observed_surely {Z : Type*} [Fintype Z]
    (k : ProbabilityKernel Z (Sigma Res)) (z : Z) :
    ∑ o ∈ Finset.univ.filter (fun o => Stmt.consumer ∈ o),
        (observationKernel m1 scoredFix realizeFix k).mass z o = 1 :=
  preexisting_observed_surely k z (by simp [scoredFix]) foundation_adapter_discharge.1

end

end DarkTower.WarMachine.CheckedReturnObservation
