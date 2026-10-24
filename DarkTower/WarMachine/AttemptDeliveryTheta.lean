import DarkTower.WarMachine.PatternTheta

/-!
# Authority-admitted attempt-delivery counts

This module models a Boolean attempt-delivery observation.  It is deliberately
separate from `PatternTheta.FastOutcome`: selection and declared-effect delivery
do not establish a guard-held pattern fire or pattern causality.

The event population is supplied by `PopulationCheck`.  In particular, this
file does not choose between the comparison-appended population specified by
`B-D.md` Revision 2 R2.1 and the accepted-increment wording retained in
`attempt-learning-contract-v2.edn`.  Before-condition, positive prediction,
close acceptance, or any other eligibility condition belongs in that supplied
predicate, not in an inference from selection or cumulative closure.

`family` is the reusable declaration-family parameter key. `event` is an
abstract event identity. Neither is a ledger configuration digest. Pooling by
`family` is a supplied model choice; no exchangeability theorem is claimed.

The count arithmetic is the binary Dirichlet/Beta specialization discussed in
Friston 2017 (`Q(B) = Dir(b)`) and da Costa 2020 Appendix A.1. Those references
support additive transition counts, not this domain admission or pooling.
-/

namespace DarkTower.WarMachine.AttemptDeliveryTheta

/-- Exact identity and payload requested for admission. -/
structure Request (Family Event Effect Route Revision : Type) where
  family : Family
  event : Event
  effect : Effect
  route : Route
  revision : Revision
  deriving DecidableEq, Repr

/-- Absence is distinct from the observed value `false`. -/
structure SuppliedObservation
    (Family Event Effect Route Revision Evidence : Type) where
  family : Family
  event : Event
  effect : Effect
  route : Route
  revision : Revision
  observed : Option Bool
  authorityEvidence : Option Evidence
  deriving DecidableEq, Repr

/-- Domain authority for the exact Boolean payload and exact request. -/
structure AuthorityCheck
    (Evidence Family Event Effect Route Revision : Type) where
  Admits : Evidence → Request Family Event Effect Route Revision → Bool → Prop
  check : Evidence → Request Family Event Effect Route Revision → Bool → Bool
  check_iff : ∀ e r b, check e r b = true ↔ Admits e r b

/-- A separately supplied decision about membership in the learning
population. This file chooses no runtime population semantics. -/
structure PopulationCheck (Family Event Effect Route Revision : Type) where
  Admits : Request Family Event Effect Route Revision → Bool → Prop
  check : Request Family Event Effect Route Revision → Bool → Bool
  check_iff : ∀ r b, check r b = true ↔ Admits r b

/-- An admitted delivery event is not a witnessed-fire event. -/
structure AttemptDeliveryOutcome (Family Event Effect Route Revision : Type) where
  family : Family
  event : Event
  effect : Effect
  route : Route
  revision : Revision
  delivered : Bool
  deriving DecidableEq, Repr

variable {Family Event Effect Route Revision Evidence : Type}
  [DecidableEq Family] [DecidableEq Event] [DecidableEq Effect]
  [DecidableEq Route] [DecidableEq Revision]

/-- Admit only an exact binding with present Boolean, present evidence,
payload-bound authority, and the separately supplied population premise. -/
def admit
    (authority : AuthorityCheck Evidence Family Event Effect Route Revision)
    (population : PopulationCheck Family Event Effect Route Revision)
    (requested : Request Family Event Effect Route Revision)
    (observation : SuppliedObservation Family Event Effect Route Revision Evidence) :
    Option (AttemptDeliveryOutcome Family Event Effect Route Revision) :=
  if observation.family = requested.family ∧
      observation.event = requested.event ∧
      observation.effect = requested.effect ∧
      observation.route = requested.route ∧
      observation.revision = requested.revision then
    match observation.observed, observation.authorityEvidence with
    | some delivered, some evidence =>
        if authority.check evidence requested delivered &&
            population.check requested delivered then
          some ⟨requested.family, requested.event, requested.effect,
            requested.route, requested.revision, delivered⟩
        else none
    | _, _ => none
  else none

/-- Sufficient admission theorem, including the exact Boolean payload. -/
theorem admit_of_exact
    (authority : AuthorityCheck Evidence Family Event Effect Route Revision)
    (population : PopulationCheck Family Event Effect Route Revision)
    (requested : Request Family Event Effect Route Revision)
    (delivered : Bool) (evidence : Evidence)
    (ha : authority.Admits evidence requested delivered)
    (hp : population.Admits requested delivered) :
    admit authority population requested
      ⟨requested.family, requested.event, requested.effect, requested.route,
        requested.revision, some delivered, some evidence⟩ =
      some ⟨requested.family, requested.event, requested.effect,
        requested.route, requested.revision, delivered⟩ := by
  simp [admit, (authority.check_iff evidence requested delivered).2 ha,
    (population.check_iff requested delivered).2 hp]

/-- Necessary admission theorem: output recovers the exact supplied binding,
actual Boolean, authority, and supplied population membership. -/
theorem admit_eq_some_only_if
    (authority : AuthorityCheck Evidence Family Event Effect Route Revision)
    (population : PopulationCheck Family Event Effect Route Revision)
    (requested : Request Family Event Effect Route Revision)
    (observation : SuppliedObservation Family Event Effect Route Revision Evidence)
    (outcome : AttemptDeliveryOutcome Family Event Effect Route Revision)
    (h : admit authority population requested observation = some outcome) :
    ∃ delivered evidence,
      observation = ⟨requested.family, requested.event, requested.effect,
        requested.route, requested.revision, some delivered, some evidence⟩ ∧
      authority.Admits evidence requested delivered ∧
      population.Admits requested delivered ∧
      outcome = ⟨requested.family, requested.event, requested.effect,
        requested.route, requested.revision, delivered⟩ := by
  simp only [admit] at h
  split at h <;> try contradiction
  next binding =>
    rcases binding with ⟨hf, hev, heff, hr, hrev⟩
    cases ho : observation.observed <;> simp [ho] at h
    cases he : observation.authorityEvidence <;> simp [he] at h
    rename_i delivered evidence
    by_cases ha : authority.check evidence requested delivered = true
    · by_cases hp : population.check requested delivered = true
      · simp [ha, hp] at h
        subst outcome
        exact ⟨delivered, evidence, by cases observation; simp_all,
          (authority.check_iff evidence requested delivered).1 ha,
          (population.check_iff requested delivered).1 hp, rfl⟩
      · simp [ha, hp] at h
    · simp [ha] at h

theorem missing_not_admitted
    (authority : AuthorityCheck Evidence Family Event Effect Route Revision)
    (population : PopulationCheck Family Event Effect Route Revision)
    (requested : Request Family Event Effect Route Revision)
    (observation : SuppliedObservation Family Event Effect Route Revision Evidence)
    (h : observation.observed = none) :
    admit authority population requested observation = none := by
  simp [admit, h]

inductive ReplayDisposition where
  | appended | duplicate | conflict
  deriving DecidableEq, Repr

structure State (Family Event Effect Route Revision : Type) where
  history : List (AttemptDeliveryOutcome Family Event Effect Route Revision)
  deriving DecidableEq, Repr

structure UpdateResult (Family Event Effect Route Revision : Type) where
  state : State Family Event Effect Route Revision
  disposition : ReplayDisposition
  deriving DecidableEq, Repr

/-- Event ids are immutable globally. Exact replay is a duplicate; any other
payload under the same id is a typed conflict. Neither changes history. -/
def update
    (state : State Family Event Effect Route Revision)
    (outcome : AttemptDeliveryOutcome Family Event Effect Route Revision) :
    UpdateResult Family Event Effect Route Revision :=
  match state.history.find? (fun old => old.event = outcome.event) with
  | none => ⟨⟨state.history ++ [outcome]⟩, .appended⟩
  | some old => if old = outcome then ⟨state, .duplicate⟩ else ⟨state, .conflict⟩

inductive ProcessDisposition where
  | rejected
  | admitted (replay : ReplayDisposition)
  deriving DecidableEq, Repr

/-- Result of the composed admission/update boundary. `outcome = none` is a
rejection and necessarily retains the input state. -/
structure ProcessResult (Family Event Effect Route Revision : Type) where
  state : State Family Event Effect Route Revision
  disposition : ProcessDisposition
  outcome : Option (AttemptDeliveryOutcome Family Event Effect Route Revision)
  deriving DecidableEq, Repr

/-- The only operation in this module that turns a supplied observation into a
counted history entry. Raw `update` remains available for proofs over already
admitted outcomes. The input state's prior history is supplied and is not
retrospectively certified by this operation. -/
def admitAndUpdate
    (authority : AuthorityCheck Evidence Family Event Effect Route Revision)
    (population : PopulationCheck Family Event Effect Route Revision)
    (requested : Request Family Event Effect Route Revision)
    (observation : SuppliedObservation Family Event Effect Route Revision Evidence)
    (state : State Family Event Effect Route Revision) :
    ProcessResult Family Event Effect Route Revision :=
  match admit authority population requested observation with
  | none => ⟨state, .rejected, none⟩
  | some outcome =>
      let result := update state outcome
      ⟨result.state, .admitted result.disposition, some outcome⟩

theorem admitAndUpdate_rejected_state
    (authority : AuthorityCheck Evidence Family Event Effect Route Revision)
    (population : PopulationCheck Family Event Effect Route Revision)
    (requested : Request Family Event Effect Route Revision)
    (observation : SuppliedObservation Family Event Effect Route Revision Evidence)
    (state : State Family Event Effect Route Revision)
    (h : admit authority population requested observation = none) :
    admitAndUpdate authority population requested observation state =
      ⟨state, .rejected, none⟩ := by
  simp [admitAndUpdate, h]

/-- Any appended composed result comes from the exact admitted outcome; the
admission theorem then recovers payload-bound authority and population proof. -/
theorem admitAndUpdate_appended_only_if
    (authority : AuthorityCheck Evidence Family Event Effect Route Revision)
    (population : PopulationCheck Family Event Effect Route Revision)
    (requested : Request Family Event Effect Route Revision)
    (observation : SuppliedObservation Family Event Effect Route Revision Evidence)
    (state : State Family Event Effect Route Revision)
    (next : State Family Event Effect Route Revision)
    (hout : AttemptDeliveryOutcome Family Event Effect Route Revision)
    (h : admitAndUpdate authority population requested observation state =
      ⟨next, .admitted .appended, some hout⟩) :
    admit authority population requested observation = some hout ∧
      update state hout = ⟨next, .appended⟩ ∧
      ∃ delivered evidence,
        observation = ⟨requested.family, requested.event, requested.effect,
          requested.route, requested.revision, some delivered, some evidence⟩ ∧
        authority.Admits evidence requested delivered ∧
        population.Admits requested delivered ∧
        hout = ⟨requested.family, requested.event, requested.effect,
          requested.route, requested.revision, delivered⟩ := by
  cases hadmit : admit authority population requested observation with
  | none => simp [admitAndUpdate, hadmit] at h
  | some outcome =>
    cases hupdate : update state outcome with
    | mk updated disposition =>
      simp [admitAndUpdate, hadmit, hupdate] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, hupdate,
        admit_eq_some_only_if authority population requested observation outcome hadmit⟩

def familyBools (family : Family)
    (state : State Family Event Effect Route Revision) : List Bool :=
  (state.history.filter (fun outcome => outcome.family = family)).map (·.delivered)

/-- Positive rational pseudo-counts are supplied, not chosen here. -/
structure Prior where
  success : ℚ
  failure : ℚ
  success_pos : 0 < success
  failure_pos : 0 < failure

def concentrations (prior : Prior) (family : Family)
    (state : State Family Event Effect Route Revision) : ℚ × ℚ :=
  let xs := familyBools family state
  (prior.success + PatternTheta.successes xs,
    prior.failure + PatternTheta.failures xs)

theorem admitAndUpdate_rejected_concentrations
    (prior : Prior) (family : Family)
    (authority : AuthorityCheck Evidence Family Event Effect Route Revision)
    (population : PopulationCheck Family Event Effect Route Revision)
    (requested : Request Family Event Effect Route Revision)
    (observation : SuppliedObservation Family Event Effect Route Revision Evidence)
    (state : State Family Event Effect Route Revision)
    (h : admit authority population requested observation = none) :
    concentrations prior family
        (admitAndUpdate authority population requested observation state).state =
      concentrations prior family state := by
  simp [admitAndUpdate, h]

theorem append_true_changes_success_once (prior : Prior) (family : Family)
    (state : State Family Event Effect Route Revision)
    (outcome : AttemptDeliveryOutcome Family Event Effect Route Revision)
    (hf : outcome.family = family)
    (fresh : state.history.find? (fun old => old.event = outcome.event) = none)
    (ht : outcome.delivered = true) :
    concentrations prior family (update state outcome).state =
      ((concentrations prior family state).1 + 1,
       (concentrations prior family state).2) := by
  simp [update, fresh, concentrations, familyBools, hf, ht,
    PatternTheta.successes_append, PatternTheta.failures_append,
    PatternTheta.successes, PatternTheta.failures]
  ring

theorem append_false_changes_failure_once (prior : Prior) (family : Family)
    (state : State Family Event Effect Route Revision)
    (outcome : AttemptDeliveryOutcome Family Event Effect Route Revision)
    (hf : outcome.family = family)
    (fresh : state.history.find? (fun old => old.event = outcome.event) = none)
    (ht : outcome.delivered = false) :
    concentrations prior family (update state outcome).state =
      ((concentrations prior family state).1,
       (concentrations prior family state).2 + 1) := by
  simp [update, fresh, concentrations, familyBools, hf, ht,
    PatternTheta.successes_append, PatternTheta.failures_append,
    PatternTheta.successes, PatternTheta.failures]
  ring

theorem admitted_fresh_true_changes_success_once
    (prior : Prior) (family : Family)
    (authority : AuthorityCheck Evidence Family Event Effect Route Revision)
    (population : PopulationCheck Family Event Effect Route Revision)
    (requested : Request Family Event Effect Route Revision)
    (observation : SuppliedObservation Family Event Effect Route Revision Evidence)
    (state : State Family Event Effect Route Revision)
    (outcome : AttemptDeliveryOutcome Family Event Effect Route Revision)
    (hadmit : admit authority population requested observation = some outcome)
    (hf : outcome.family = family)
    (fresh : state.history.find? (fun old => old.event = outcome.event) = none)
    (ht : outcome.delivered = true) :
    concentrations prior family
        (admitAndUpdate authority population requested observation state).state =
      ((concentrations prior family state).1 + 1,
       (concentrations prior family state).2) := by
  simp [admitAndUpdate, hadmit]
  exact append_true_changes_success_once prior family state outcome hf fresh ht

theorem admitted_fresh_false_changes_failure_once
    (prior : Prior) (family : Family)
    (authority : AuthorityCheck Evidence Family Event Effect Route Revision)
    (population : PopulationCheck Family Event Effect Route Revision)
    (requested : Request Family Event Effect Route Revision)
    (observation : SuppliedObservation Family Event Effect Route Revision Evidence)
    (state : State Family Event Effect Route Revision)
    (outcome : AttemptDeliveryOutcome Family Event Effect Route Revision)
    (hadmit : admit authority population requested observation = some outcome)
    (hf : outcome.family = family)
    (fresh : state.history.find? (fun old => old.event = outcome.event) = none)
    (ht : outcome.delivered = false) :
    concentrations prior family
        (admitAndUpdate authority population requested observation state).state =
      ((concentrations prior family state).1,
       (concentrations prior family state).2 + 1) := by
  simp [admitAndUpdate, hadmit]
  exact append_false_changes_failure_once prior family state outcome hf fresh ht

theorem replay_does_not_update (state : State Family Event Effect Route Revision)
    (outcome : AttemptDeliveryOutcome Family Event Effect Route Revision)
    (hfind : state.history.find? (fun old => old.event = outcome.event) = some outcome) :
    update state outcome = ⟨state, .duplicate⟩ := by
  simp [update, hfind]

theorem conflict_does_not_update (state : State Family Event Effect Route Revision)
    (old outcome : AttemptDeliveryOutcome Family Event Effect Route Revision)
    (hfind : state.history.find? (fun x => x.event = outcome.event) = some old)
    (hne : old ≠ outcome) :
    update state outcome = ⟨state, .conflict⟩ := by
  simp [update, hfind, hne]

theorem untouched_family_unchanged (prior : Prior) (family : Family)
    (state : State Family Event Effect Route Revision)
    (outcome : AttemptDeliveryOutcome Family Event Effect Route Revision)
    (hne : outcome.family ≠ family) :
    concentrations prior family (update state outcome).state =
      concentrations prior family state := by
  unfold update
  split
  · simp [concentrations, familyBools, hne]
  · split <;> rfl

/-! Synthetic supplied model: the checker premises are examples, not runtime
authority and not a causal model. No fire witness appears in these types. -/

inductive FamilyExample where | reusable | untouched deriving DecidableEq, Repr
inductive EffectExample where | done | other deriving DecidableEq, Repr
inductive RouteExample where | ordinary | other deriving DecidableEq, Repr

structure EvidenceExample where
  event : Nat
  effect : EffectExample
  route : RouteExample
  revision : Nat
  delivered : Bool
  deriving DecidableEq, Repr

def exampleAuthority : AuthorityCheck EvidenceExample FamilyExample Nat EffectExample RouteExample Nat where
  Admits e r b := e.event = r.event ∧ e.effect = r.effect ∧ e.route = r.route ∧
    e.revision = r.revision ∧ e.delivered = b
  check e r b := decide (e.event = r.event ∧ e.effect = r.effect ∧ e.route = r.route ∧
    e.revision = r.revision ∧ e.delivered = b)
  check_iff _ _ _ := by simp

def examplePopulation : PopulationCheck FamilyExample Nat EffectExample RouteExample Nat where
  Admits r _ := r.family = .reusable
  check r _ := decide (r.family = .reusable)
  check_iff _ _ := by simp

def rejectPopulation : PopulationCheck FamilyExample Nat EffectExample RouteExample Nat where
  Admits _ _ := False
  check _ _ := false
  check_iff _ _ := by simp

def exampleRequest : Request FamilyExample Nat EffectExample RouteExample Nat :=
  ⟨.reusable, 19, .done, .ordinary, 7⟩

def exampleEvidence (b : Bool) : EvidenceExample := ⟨19, .done, .ordinary, 7, b⟩

def exampleObservation (event revision : Nat) (route : RouteExample)
    (observed : Option Bool) (evidence : Option EvidenceExample) :
    SuppliedObservation FamilyExample Nat EffectExample RouteExample Nat EvidenceExample :=
  ⟨.reusable, event, .done, route, revision, observed, evidence⟩

theorem admitted_delivery_without_fire_field :
    admit exampleAuthority examplePopulation exampleRequest
      (exampleObservation 19 7 .ordinary (some true) (some (exampleEvidence true))) =
      some ⟨.reusable, 19, .done, .ordinary, 7, true⟩ := by decide

theorem selected_only_unqualified_not_admitted :
    admit exampleAuthority examplePopulation exampleRequest
      (exampleObservation 19 7 .ordinary (some true) none) = none := by decide

theorem rejected_payload_not_admitted :
    admit exampleAuthority examplePopulation exampleRequest
      (exampleObservation 19 7 .ordinary (some false) (some (exampleEvidence true))) = none := by decide

theorem missing_payload_not_admitted :
    admit exampleAuthority examplePopulation exampleRequest
      (exampleObservation 19 7 .ordinary none (some (exampleEvidence true))) = none := by decide

theorem wrong_effect_not_admitted :
    admit exampleAuthority examplePopulation exampleRequest
      ⟨.reusable, 19, .other, .ordinary, 7, some true, some (exampleEvidence true)⟩ = none := by
  decide

theorem wrong_event_not_admitted :
    admit exampleAuthority examplePopulation exampleRequest
      (exampleObservation 20 7 .ordinary (some true) (some (exampleEvidence true))) = none := by decide

theorem wrong_route_not_admitted :
    admit exampleAuthority examplePopulation exampleRequest
      (exampleObservation 19 7 .other (some true) (some (exampleEvidence true))) = none := by decide

theorem wrong_revision_not_admitted :
    admit exampleAuthority examplePopulation exampleRequest
      (exampleObservation 19 8 .ordinary (some true) (some (exampleEvidence true))) = none := by decide

def emptyExampleState : State FamilyExample Nat EffectExample RouteExample Nat := ⟨[]⟩
def trueOutcome : AttemptDeliveryOutcome FamilyExample Nat EffectExample RouteExample Nat :=
  ⟨.reusable, 19, .done, .ordinary, 7, true⟩
def falseOutcome : AttemptDeliveryOutcome FamilyExample Nat EffectExample RouteExample Nat :=
  ⟨.reusable, 19, .done, .ordinary, 7, false⟩
def trueObservation := exampleObservation 19 7 .ordinary (some true) (some (exampleEvidence true))
def falseObservation := exampleObservation 19 7 .ordinary (some false) (some (exampleEvidence false))

theorem composed_admitted_true_appends :
    admitAndUpdate exampleAuthority examplePopulation exampleRequest trueObservation emptyExampleState =
      ⟨⟨[trueOutcome]⟩, .admitted .appended, some trueOutcome⟩ := by decide

theorem composed_admitted_false_appends :
    admitAndUpdate exampleAuthority examplePopulation exampleRequest falseObservation emptyExampleState =
      ⟨⟨[falseOutcome]⟩, .admitted .appended, some falseOutcome⟩ := by decide

theorem composed_population_rejection_unchanged :
    admitAndUpdate exampleAuthority rejectPopulation exampleRequest trueObservation emptyExampleState =
      ⟨emptyExampleState, .rejected, none⟩ := by decide

theorem composed_unqualified_unchanged :
    admitAndUpdate exampleAuthority examplePopulation exampleRequest
      (exampleObservation 19 7 .ordinary (some true) none) emptyExampleState =
      ⟨emptyExampleState, .rejected, none⟩ := by decide

theorem composed_wrong_identity_unchanged :
    admitAndUpdate exampleAuthority examplePopulation exampleRequest
      (exampleObservation 20 7 .ordinary (some true) (some (exampleEvidence true)))
      emptyExampleState = ⟨emptyExampleState, .rejected, none⟩ := by decide

theorem composed_exact_replay_duplicate :
    admitAndUpdate exampleAuthority examplePopulation exampleRequest trueObservation
      ⟨[trueOutcome]⟩ = ⟨⟨[trueOutcome]⟩, .admitted .duplicate, some trueOutcome⟩ := by decide

/-- The flipped Boolean has separately matching authority, but immutable event
identity makes it a conflict and leaves the prior true history unchanged. -/
theorem composed_flipped_payload_conflict :
    admitAndUpdate exampleAuthority examplePopulation exampleRequest falseObservation
      ⟨[trueOutcome]⟩ = ⟨⟨[trueOutcome]⟩, .admitted .conflict, some falseOutcome⟩ := by decide

#print axioms admit_of_exact
#print axioms admit_eq_some_only_if
#print axioms admitAndUpdate_rejected_state
#print axioms admitAndUpdate_rejected_concentrations
#print axioms admitAndUpdate_appended_only_if
#print axioms append_true_changes_success_once
#print axioms append_false_changes_failure_once
#print axioms admitted_fresh_true_changes_success_once
#print axioms admitted_fresh_false_changes_failure_once
#print axioms replay_does_not_update
#print axioms conflict_does_not_update
#print axioms untouched_family_unchanged
#print axioms composed_population_rejection_unchanged
#print axioms composed_exact_replay_duplicate
#print axioms composed_flipped_payload_conflict

end DarkTower.WarMachine.AttemptDeliveryTheta
