import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Checked problem map and its update from an outer return

A finite, fixed type `S` of declared statement IDs is interpreted by
`I : S → Prop`.  A checked *artifact* carries a proof of `I stmt`; a checked
*reduction* carries a head, a finite set of tails, and a proof that all tails
together imply the head.  Several reductions with the same head are
alternative routes (OR); the tails of one reduction are joint prerequisites
(AND).

`Closed m` is the least set of IDs containing every artifact's statement and
containing a reduction's head whenever it contains all of that reduction's
tails: the least model of a finite set of Horn rules (Aczel 1977, "An
introduction to inductive definitions", Handbook of Mathematical Logic,
§1.1–1.2; van Emden and Kowalski 1976).  `closed_sound` proves that every
closed ID has a proof assembled from the map's artifacts and reductions;
`closed_least` gives the least-set characterisation used by the controls
below.  A cycle of reductions with no artifact under it does not close.

`update` admits only the `CheckedReturn` part of a return.  The verdict label
and the claimed closures are carried as data and do not enter the map, so a
prediction or label alone never closes anything.  An absent return
(`none`) leaves the map as it was.  A censored return may still carry
checked helpers, and they are admitted.

The universe `S` is a type parameter, so an update cannot add IDs: a residual
statement must already be declared in `S`.  Statement identity is the typed
ID; nothing here equates an ID with a live Lean declaration name or a commit.

Scope.  This is supplied-proof semantics for a synthetic map.  It is not
runtime receipt authenticity, not a decoder from runtime records, and not a
counting or learning rule.  AIF boundary: under Parr et al. 2022 ch. 7 a
closure verdict enters the generative model as an observation through a
likelihood.  This module is the domain refinement that fixes what a "closed"
observation is grounded in; its soundness is a property of the proof map,
not a theorem derived from active inference.

Existing machinery searched: `FiniteListGraphClosure` (undirected reachability
over edge pairs, no proofs, no joint tails), `ConstructionReceipt` (Bool-valued
token-path receipts), `CertificateStates` (state labels without proofs) and
`R15StrategicTarget.withRepairs` (a single-valued `unblocks` relation).  None
carries proofs over joint tails, so this module does not duplicate them.
-/

namespace DarkTower.WarMachine.CheckedProblemMap

universe u

variable {S : Type u}

/-- A checked artifact: a declared ID together with a proof of its
interpretation. -/
structure Artifact (I : S → Prop) where
  stmt : S
  proof : I stmt

/-- A checked reduction: all tails jointly imply the head. -/
structure Reduction (I : S → Prop) where
  head : S
  tails : Finset S
  proof : (∀ t ∈ tails, I t) → I head

/-- The problem map: checked artifacts, checked reductions, and the declared
obligations (the IDs the outer loop wants closed). -/
structure ProblemMap (I : S → Prop) where
  artifacts : List (Artifact I)
  reductions : List (Reduction I)
  obligations : Finset S

variable {I : S → Prop}

/-- Least derivation over the map: artifacts are seeds; a reduction fires only
when every one of its tails is closed. -/
inductive Closed (m : ProblemMap I) : S → Prop
  | artifact (a : Artifact I) (ha : a ∈ m.artifacts) : Closed m a.stmt
  | reduction (r : Reduction I) (hr : r ∈ m.reductions)
      (htails : ∀ t ∈ r.tails, Closed m t) : Closed m r.head

/-- A checked conditional reduction exists for `s`.  This is weaker than
`Closed m s`. -/
def HasReduction (m : ProblemMap I) (s : S) : Prop :=
  ∃ r ∈ m.reductions, r.head = s

/-- Every closed ID has a proof of its interpretation. -/
theorem closed_sound {m : ProblemMap I} {s : S} (h : Closed m s) : I s := by
  induction h with
  | artifact a _ => exact a.proof
  | reduction r _ _ ih => exact r.proof ih

/-- A set closed under the map's rules. -/
def RuleClosed (m : ProblemMap I) (T : Set S) : Prop :=
  (∀ a ∈ m.artifacts, a.stmt ∈ T) ∧
    ∀ r ∈ m.reductions, (∀ t ∈ r.tails, t ∈ T) → r.head ∈ T

/-- `Closed m` is contained in every rule-closed set. -/
theorem closed_least {m : ProblemMap I} {T : Set S} (hT : RuleClosed m T)
    {s : S} (h : Closed m s) : s ∈ T := by
  induction h with
  | artifact a ha => exact hT.1 a ha
  | reduction r hr _ ih => exact hT.2 r hr ih

/-- `Closed m` is itself rule-closed, so it is the least rule-closed set. -/
theorem closed_ruleClosed (m : ProblemMap I) : RuleClosed m {s | Closed m s} :=
  ⟨fun a ha => Closed.artifact a ha, fun r hr ht => Closed.reduction r hr ht⟩

/-- The closed IDs as a finite subset of the fixed universe. -/
noncomputable def closedSet [Fintype S] (m : ProblemMap I) : Finset S := by
  classical exact Finset.univ.filter (Closed m)

theorem mem_closedSet [Fintype S] {m : ProblemMap I} {s : S} :
    s ∈ closedSet m ↔ Closed m s := by
  classical simp [closedSet]

/-! ## Return and update -/

/-- The checked part of a return: artifacts and reductions with proofs. -/
structure CheckedReturn (I : S → Prop) where
  artifacts : List (Artifact I)
  reductions : List (Reduction I)

def CheckedReturn.empty : CheckedReturn I := ⟨[], []⟩

/-- A minimal projection of a reported return.  `label` (verdict, censoring,
timeout, ...) and `claimedClosed` are data; only `checked` carries proofs. -/
structure ReturnReport (I : S → Prop) (Label : Type) where
  label : Label
  claimedClosed : Finset S
  checked : CheckedReturn I

/-- Admit checked artifacts and reductions, keeping everything already in the
map, including the declared obligations. -/
def admit (m : ProblemMap I) (c : CheckedReturn I) : ProblemMap I where
  artifacts := m.artifacts ++ c.artifacts
  reductions := m.reductions ++ c.reductions
  obligations := m.obligations

/-- Update from an optional report.  An absent report changes nothing; a
present one contributes only its checked part. -/
def update {Label : Type} (m : ProblemMap I) :
    Option (ReturnReport I Label) → ProblemMap I
  | none => m
  | some r => admit m r.checked

/-- Unresolved obligations: declared but not closed. -/
def Open (m : ProblemMap I) (s : S) : Prop :=
  s ∈ m.obligations ∧ ¬ Closed m s

theorem admit_artifacts_retained (m : ProblemMap I) (c : CheckedReturn I)
    {a : Artifact I} (ha : a ∈ m.artifacts) : a ∈ (admit m c).artifacts :=
  List.mem_append_left _ ha

theorem admit_reductions_retained (m : ProblemMap I) (c : CheckedReturn I)
    {r : Reduction I} (hr : r ∈ m.reductions) : r ∈ (admit m c).reductions :=
  List.mem_append_left _ hr

theorem admit_obligations (m : ProblemMap I) (c : CheckedReturn I) :
    (admit m c).obligations = m.obligations := rfl

theorem admit_empty (m : ProblemMap I) : admit m CheckedReturn.empty = m := by
  cases m
  simp [admit, CheckedReturn.empty]

/-- Monotonicity: admitting checked material never un-closes an ID. -/
theorem closed_admit {m : ProblemMap I} (c : CheckedReturn I) {s : S}
    (h : Closed m s) : Closed (admit m c) s := by
  induction h with
  | artifact a ha => exact Closed.artifact a (admit_artifacts_retained m c ha)
  | reduction r hr _ ih =>
      exact Closed.reduction r (admit_reductions_retained m c hr) ih

theorem closed_update {Label : Type} {m : ProblemMap I}
    (o : Option (ReturnReport I Label)) {s : S} (h : Closed m s) :
    Closed (update m o) s := by
  cases o with
  | none => exact h
  | some r => exact closed_admit r.checked h

/-- Soundness of the updated map. -/
theorem update_sound {Label : Type} {m : ProblemMap I}
    (o : Option (ReturnReport I Label)) {s : S} (h : Closed (update m o) s) :
    I s :=
  closed_sound h

theorem update_obligations {Label : Type} (m : ProblemMap I)
    (o : Option (ReturnReport I Label)) :
    (update m o).obligations = m.obligations := by
  cases o <;> rfl

/-- Unresolved obligations after an update were unresolved before it. -/
theorem open_update {Label : Type} {m : ProblemMap I}
    (o : Option (ReturnReport I Label)) {s : S} (h : Open (update m o) s) :
    Open m s :=
  ⟨update_obligations m o ▸ h.1, fun hc => h.2 (closed_update o hc)⟩

theorem update_none {Label : Type} (m : ProblemMap I) :
    update (Label := Label) m none = m := rfl

/-- The label and the claimed closures do not affect the map. -/
theorem update_report_irrelevant {Label : Type} (m : ProblemMap I)
    (r r' : ReturnReport I Label) (h : r.checked = r'.checked) :
    update m (some r) = update m (some r') := by
  simp [update, h]

/-- A report with no checked part closes exactly what was closed before,
whatever its label or claims. -/
theorem closed_update_unchecked {Label : Type} (m : ProblemMap I)
    (r : ReturnReport I Label) (h : r.checked = CheckedReturn.empty) (s : S) :
    Closed (update m (some r)) s ↔ Closed m s := by
  simp [update, h, admit_empty]

/-! ## Synthetic controls

A fixed universe of six IDs.  Every interpretation is a true proposition, so
each non-closure below is structural: it comes from what has been checked,
not from the statement being false. -/

inductive Stmt
  | foundation | adapter | consumer | hard | cycA | cycB
  deriving DecidableEq, Fintype

def interp : Stmt → Prop
  | .foundation => ∀ n : ℕ, 0 + n = n
  | .adapter => ∀ n : ℕ, n + 0 = n
  | .consumer => ∀ n : ℕ, 0 + n = n + 0
  | .hard => ∀ n : ℕ, n + 0 = 0 + n
  | .cycA => True
  | .cycB => True

inductive Verdict
  | closed | refuted | censored | timeout

/-- The consumer from the foundation and the adapter jointly. -/
def viaFoundation : Reduction interp where
  head := .consumer
  tails := {.foundation, .adapter}
  proof h := by
    have hf : ∀ n : ℕ, 0 + n = n := h .foundation (by simp)
    have ha : ∀ n : ℕ, n + 0 = n := h .adapter (by simp)
    show ∀ n : ℕ, 0 + n = n + 0
    exact fun n => (hf n).trans (ha n).symm

/-- An alternative route to the consumer, left unresolved. -/
def viaHard : Reduction interp where
  head := .consumer
  tails := {.hard}
  proof h := by
    have hh : ∀ n : ℕ, n + 0 = 0 + n := h .hard (by simp)
    show ∀ n : ℕ, 0 + n = n + 0
    exact fun n => (hh n).symm

def cycAB : Reduction interp where
  head := .cycA
  tails := {.cycB}
  proof _ := trivial

def cycBA : Reduction interp where
  head := .cycB
  tails := {.cycA}
  proof _ := trivial

def foundationArt : Artifact interp where
  stmt := .foundation
  proof := by
    show ∀ n : ℕ, 0 + n = n
    exact Nat.zero_add

def adapterArt : Artifact interp where
  stmt := .adapter
  proof := by
    show ∀ n : ℕ, n + 0 = n
    exact Nat.add_zero

/-- Before the return: two alternative reductions for the consumer and an
unseeded cycle; no artifacts. -/
def m0 : ProblemMap interp where
  artifacts := []
  reductions := [viaFoundation, viaHard, cycAB, cycBA]
  obligations := {.consumer, .cycA}

def foundationOnly : ReturnReport interp Verdict where
  label := .closed
  claimedClosed := {.foundation, .consumer}
  checked := ⟨[foundationArt], []⟩

def foundationAndAdapter : ReturnReport interp Verdict where
  label := .closed
  claimedClosed := {.foundation, .consumer}
  checked := ⟨[foundationArt, adapterArt], []⟩

def predictionOnly : ReturnReport interp Verdict where
  label := .closed
  claimedClosed := {.consumer}
  checked := CheckedReturn.empty

def censoredHelper : ReturnReport interp Verdict where
  label := .censored
  claimedClosed := ∅
  checked := ⟨[adapterArt], []⟩

/-- Membership in the reductions of `m0` after any admitted return with no
new reductions. -/
private theorem mem_m0_reductions {r : Reduction interp} {as : List (Artifact interp)}
    (hr : r ∈ (admit m0 ⟨as, []⟩).reductions) :
    r = viaFoundation ∨ r = viaHard ∨ r = cycAB ∨ r = cycBA := by
  simpa [admit, m0] using hr

/-- Rule-closedness of `T` for `m0` plus artifacts, checked reduction by
reduction: each reduction either has its head in `T` or a tail outside it. -/
private theorem ruleClosed_m0 (as : List (Artifact interp)) (T : Set Stmt)
    (ha : ∀ a ∈ as, a.stmt ∈ T)
    (hF : Stmt.consumer ∈ T ∨ Stmt.foundation ∉ T ∨ Stmt.adapter ∉ T)
    (hH : Stmt.consumer ∈ T ∨ Stmt.hard ∉ T)
    (hA : Stmt.cycA ∈ T ∨ Stmt.cycB ∉ T)
    (hB : Stmt.cycB ∈ T ∨ Stmt.cycA ∉ T) :
    RuleClosed (admit m0 ⟨as, []⟩) T := by
  refine ⟨fun a h => ?_, fun r hr ht => ?_⟩
  · simp only [admit, m0, List.nil_append] at h
    exact ha a h
  · rcases mem_m0_reductions hr with rfl | rfl | rfl | rfl
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

/-- A conditional reduction is not a discharge: `m0` has a checked reduction
for the consumer, and the consumer is open. -/
theorem reduction_not_discharge :
    HasReduction m0 .consumer ∧ Open m0 .consumer := by
  refine ⟨⟨viaFoundation, by simp [m0], rfl⟩, by simp [m0], fun h => ?_⟩
  have hT := ruleClosed_m0 [] ∅ (by simp) (by simp) (by simp) (by simp) (by simp)
  rw [show admit m0 ⟨[], []⟩ = m0 from admit_empty m0] at hT
  exact closed_least hT h

/-- Direct discharge: the returned foundation and adapter close the consumer,
and the consumer's interpretation follows from the closure. -/
theorem foundation_adapter_discharge :
    Closed (update m0 (some foundationAndAdapter)) .consumer ∧
      interp .consumer := by
  have hc : Closed (update m0 (some foundationAndAdapter)) .consumer := by
    refine Closed.reduction viaFoundation (by simp [update, admit, m0]) ?_
    intro t ht
    simp only [viaFoundation, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Closed.artifact foundationArt
        (by simp [update, admit, foundationAndAdapter])
    · exact Closed.artifact adapterArt
        (by simp [update, admit, foundationAndAdapter])
  exact ⟨hc, update_sound _ hc⟩

/-- One completed alternative suffices: the consumer closes although the
other route (`viaHard`) is unresolved, and its tail `hard` stays unclosed. -/
theorem one_alternative_suffices :
    Closed (update m0 (some foundationAndAdapter)) .consumer ∧
      ¬ Closed (update m0 (some foundationAndAdapter)) .hard := by
  refine ⟨foundation_adapter_discharge.1, fun h => ?_⟩
  have hT := ruleClosed_m0 [foundationArt, adapterArt]
    {.foundation, .adapter, .consumer}
    (by simp [foundationArt, adapterArt]) (by simp) (by simp) (by simp) (by simp)
  simpa using closed_least hT h

/-- The foundation without the required adapter leaves the consumer
unclosed, although the report labels it closed and claims the consumer. -/
theorem foundation_without_adapter_unclosed :
    ¬ Closed (update m0 (some foundationOnly)) .consumer := by
  intro h
  have hT := ruleClosed_m0 [foundationArt] {.foundation}
    (by simp [foundationArt]) (by simp) (by simp) (by simp) (by simp)
  simpa using closed_least hT h

/-- The unseeded cycle does not self-discharge, even after a successful
return elsewhere in the map. -/
theorem unseeded_cycle_unclosed :
    ¬ Closed (update m0 (some foundationAndAdapter)) .cycA ∧
      ¬ Closed (update m0 (some foundationAndAdapter)) .cycB := by
  have hT := ruleClosed_m0 [foundationArt, adapterArt]
    {.foundation, .adapter, .consumer}
    (by simp [foundationArt, adapterArt]) (by simp) (by simp) (by simp) (by simp)
  exact ⟨fun h => by simpa using closed_least hT h,
    fun h => by simpa using closed_least hT h⟩

/-- A prediction-only report and an absent report both leave the consumer
unclosed. -/
theorem prediction_or_absent_unclosed :
    ¬ Closed (update m0 (some predictionOnly)) .consumer ∧
      ¬ Closed (update (Label := Verdict) m0 none) .consumer := by
  have h0 := reduction_not_discharge.2.2
  exact ⟨fun h => h0 ((closed_update_unchecked m0 predictionOnly rfl _).1 h), h0⟩

/-- A censored report contributes its checked helper and nothing else: the
adapter closes, the consumer does not. -/
theorem censored_helper_admitted :
    Closed (update m0 (some censoredHelper)) .adapter ∧
      ¬ Closed (update m0 (some censoredHelper)) .consumer := by
  refine ⟨Closed.artifact adapterArt (by simp [update, admit, censoredHelper]),
    fun h => ?_⟩
  have hT := ruleClosed_m0 [adapterArt] {.adapter}
    (by simp [adapterArt]) (by simp) (by simp) (by simp) (by simp)
  simpa using closed_least hT h

end DarkTower.WarMachine.CheckedProblemMap
